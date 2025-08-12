/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include <util/exception_utils.h>
#include <util/expr_iterator.h>
#include <util/expr_util.h>
#include <util/format.h>
#include <util/format_expr.h>
#include <util/invariant.h>
#include <util/magic.h>
#include <util/mathematical_expr.h>
#include <util/replace_symbol.h>
#include <util/std_expr.h>

#include <pointer-analysis/value_set_dereference.h>

#include "goto_symex.h"
#include "path_storage.h"

#include <memory>
#include <iostream>
#include <filesystem>
#include "cbmc/cbmc_osek_configuration.h"




int called_function_type = No_Function; //no function
irep_idt task_called_name;
int step = 0;
/////task priority for frame stack
//std::map<irep_idt, int> task_priority;
/////task name
//std::map<int, irep_idt> task_id;








symex_configt::symex_configt(const optionst &options)
  : max_depth(options.get_unsigned_int_option("depth")),
    doing_path_exploration(options.is_set("paths")),
    allow_pointer_unsoundness(
      options.get_bool_option("allow-pointer-unsoundness")),
    constant_propagation(options.get_bool_option("propagation")),
    self_loops_to_assumptions(
      options.get_bool_option("self-loops-to-assumptions")),
    simplify_opt(options.get_bool_option("simplify")),
    unwinding_assertions(options.get_bool_option("unwinding-assertions")),
    partial_loops(options.get_bool_option("partial-loops")),
    run_validation_checks(options.get_bool_option("validate-ssa-equation")),
    show_symex_steps(options.get_bool_option("show-goto-symex-steps")),
    show_points_to_sets(options.get_bool_option("show-points-to-sets")),
    max_field_sensitivity_array_size(
      options.is_set("no-array-field-sensitivity")
        ? 0
        : options.is_set("max-field-sensitivity-array-size")
            ? options.get_unsigned_int_option(
                "max-field-sensitivity-array-size")
            : DEFAULT_MAX_FIELD_SENSITIVITY_ARRAY_SIZE),
    complexity_limits_active(
      options.get_signed_int_option("symex-complexity-limit") > 0),
    cache_dereferences{options.get_bool_option("symex-cache-dereferences")}
{
}

/// If 'to' is not an instruction in our currently top-most active loop,
/// pop and re-check until we find an loop we're still active in, or empty
/// the stack.
static void pop_exited_loops(
  const goto_programt::const_targett &to,
  std::vector<framet::active_loop_infot> &active_loops)
{
  while(!active_loops.empty())
  {
    if(!active_loops.back().loop.contains(to))
      active_loops.pop_back();
    else
      break;
  }
}

//move the execution function
//static const goto_symext::get_goto_functiont get_goto_functio;
//static goto_symext::statet *stat;
//static goto_programt::instructiont instructio;

void symex_transition(
  goto_symext::statet &state,
  goto_programt::const_targett to,
  bool is_backwards_goto)
{
  if(!state.call_stack().empty())
  {
    // initialize the loop counter of any loop we are newly entering
    // upon this transition; we are entering a loop if
    // 1. the transition from state.source.pc to "to" is not a backwards goto
    // or
    // 2. we are arriving from an outer loop

    // TODO: This should all be replaced by natural loop analysis.
    // This is because the way we detect loops is pretty imprecise.

    framet &frame = state.call_stack().top();
    const goto_programt::instructiont &instruction=*to;
    for(const auto &i_e : instruction.incoming_edges)
    {
      if(
        i_e->is_backwards_goto() && i_e->get_target() == to &&
        (!is_backwards_goto ||
         state.source.pc->location_number > i_e->location_number))
      {
        const auto loop_id =
          goto_programt::loop_id(state.source.function_id, *i_e);
        auto &current_loop_info = frame.loop_iterations[loop_id];
        current_loop_info.count = 0;

        // We've found a loop, put it on the stack and say it's our current
        // active loop.
        if(
          frame.loops_info && frame.loops_info->loop_map.find(to) !=
                                frame.loops_info->loop_map.end())
        {
          frame.active_loops.emplace_back(frame.loops_info->loop_map[to]);
        }
      }
    }

    // Only do this if we have active loop analysis going.
    if(!frame.active_loops.empty())
    {
      // Otherwise if we find we're transitioning out of a loop, make sure
      // to remove any loops we're not currently iterating over.

      // Match the do-while pattern.
      if(
        state.source.pc->is_backwards_goto() &&
        state.source.pc->location_number < to->location_number)
      {
        pop_exited_loops(to, frame.active_loops);
      }

      // Match for-each or while.
      for(const auto &incoming_edge : state.source.pc->incoming_edges)
      {
        if(
          incoming_edge->is_backwards_goto() &&
          incoming_edge->location_number < to->location_number)
        {
          pop_exited_loops(to, frame.active_loops);
        }
      }
    }
  }

  state.source.pc=to;
}

void symex_transition(goto_symext::statet &state)
{
  goto_programt::const_targett next = state.source.pc;
  ++next;
  symex_transition(state, next, false);
}

void goto_symext::symex_assert(
  const goto_programt::instructiont &instruction,
  statet &state)
{
  exprt condition = clean_expr(instruction.condition(), state, false);

  // First, push negations in and perhaps convert existential quantifiers into
  // universals:
  if(has_subexpr(condition, ID_exists) || has_subexpr(condition, ID_forall))
    do_simplify(condition);

  // Second, L2-rename universal quantifiers:
  if(has_subexpr(condition, ID_forall))
    rewrite_quantifiers(condition, state);

  // now rename, enables propagation
  exprt l2_condition = state.rename(std::move(condition), ns).get();

  // now try simplifier on it
  do_simplify(l2_condition);

  std::string msg = id2string(instruction.source_location().get_comment());
  if(msg.empty())
    msg = "assertion";

  vcc(
    l2_condition, instruction.source_location().get_property_id(), msg, state);
}

void goto_symext::vcc(
  const exprt &condition,
  const irep_idt &property_id,
  const std::string &msg,
  statet &state)
{
  state.total_vccs++;
  path_segment_vccs++;

  if(condition.is_true())
    return;

  const exprt guarded_condition = state.guard.guard_expr(condition);

  state.remaining_vccs++;
  target.assertion(
    state.guard.as_expr(), guarded_condition, property_id, msg, state.source);
}

void goto_symext::symex_assume(statet &state, const exprt &cond)
{
  exprt simplified_cond = clean_expr(cond, state, false);
  simplified_cond = state.rename(std::move(simplified_cond), ns).get();
  do_simplify(simplified_cond);

  // It would be better to call try_filter_value_sets after apply_condition,
  // but it is not currently possible. See the comment at the beginning of
  // \ref apply_goto_condition for more information.

  try_filter_value_sets(
    state, cond, state.value_set, &state.value_set, nullptr, ns);

  // apply_condition must come after rename because it might change the
  // constant propagator and the value-set and we read from those in rename
  state.apply_condition(simplified_cond, state, ns);

  symex_assume_l2(state, simplified_cond);
}

void goto_symext::symex_assume_l2(statet &state, const exprt &cond)
{
  if(cond.is_true())
    return;

  if(cond.is_false())
    state.reachable = false;

  // we are willing to re-write some quantified expressions
  exprt rewritten_cond = cond;
  if(has_subexpr(rewritten_cond, ID_exists))
    rewrite_quantifiers(rewritten_cond, state);

  if(state.threads.size()==1)
  {
    exprt tmp = state.guard.guard_expr(rewritten_cond);
    target.assumption(state.guard.as_expr(), tmp, state.source);
  }
  // symex_target_equationt::convert_assertions would fail to
  // consider assumptions of threads that have a thread-id above that
  // of the thread containing the assertion:
  else
    state.guard.add(rewritten_cond);

  if(state.atomic_section_id!=0 &&
     state.guard.is_false())
    symex_atomic_end(state);
}

void goto_symext::rewrite_quantifiers(exprt &expr, statet &state)
{
  const bool is_assert = state.source.pc->is_assert();

  if(
    (is_assert && expr.id() == ID_forall) ||
    (!is_assert && expr.id() == ID_exists))
  {
    // for assertions e can rewrite "forall X. P" to "P", and
    // for assumptions we can rewrite "exists X. P" to "P"
    // we keep the quantified variable unique by means of L2 renaming
    auto &quant_expr = to_quantifier_expr(expr);
    symbol_exprt tmp0 =
      to_symbol_expr(to_ssa_expr(quant_expr.symbol()).get_original_expr());
    symex_decl(state, tmp0);
    instruction_local_symbols.push_back(tmp0);
    exprt tmp = quant_expr.where();
    rewrite_quantifiers(tmp, state);
    quant_expr.swap(tmp);
  }
  else if(expr.id() == ID_or || expr.id() == ID_and)
  {
    for(auto &op : expr.operands())
      rewrite_quantifiers(op, state);
  }
}

static void
switch_to_thread(goto_symex_statet &state, const unsigned int thread_nb)
{
  PRECONDITION(state.source.thread_nr < state.threads.size());
  PRECONDITION(thread_nb < state.threads.size());

  // save PC
  state.threads[state.source.thread_nr].pc = state.source.pc;
  state.threads[state.source.thread_nr].atomic_section_id =
    state.atomic_section_id;

  // get new PC
  state.source.thread_nr = thread_nb;
  state.source.pc = state.threads[thread_nb].pc;
  state.source.function_id = state.threads[thread_nb].function_id;

  state.guard = state.threads[thread_nb].guard;
  // A thread's initial state is certainly reachable:
  state.reachable = true;
}

void goto_symext::symex_threaded_step(
  statet &state, const get_goto_functiont &get_goto_function)
{
  symex_step(get_goto_function, state);

  _total_vccs = state.total_vccs;
  _remaining_vccs = state.remaining_vccs;

  if(should_pause_symex)
    return;

  // is there another thread to execute?
  if(state.call_stack().empty() &&
     state.source.thread_nr+1<state.threads.size())
  {
    unsigned t=state.source.thread_nr+1;
#if 0
    std::cout << "********* Now executing thread " << t << '\n';
#endif
    switch_to_thread(state, t);
    symex_transition(state, state.source.pc, false);
  }
}

symbol_tablet goto_symext::symex_with_state(
  statet &state,
  const get_goto_functiont &get_goto_function)
{
  // resets the namespace to only wrap a single symbol table, and does so upon
  // destruction of an object of this type; instantiating the type is thus all
  // that's needed to achieve a reset upon exiting this method
  struct reset_namespacet
  {
    explicit reset_namespacet(namespacet &ns) : ns(ns)
    {
    }

    ~reset_namespacet()
    {
      // Get symbol table 1, the outer symbol table from the GOTO program
      const symbol_table_baset &st = ns.get_symbol_table();
      // Move a new namespace containing this symbol table over the top of the
      // current one
      ns = namespacet(st);
    }

    namespacet &ns;
  };

  // We'll be using ns during symbolic execution and it needs to know
  // about the names minted in `state`, so make it point both to
  // `state`'s symbol table and the symbol table of the original
  // goto-program.
  ns = namespacet(outer_symbol_table, state.symbol_table);

  // whichever way we exit this method, reset the namespace back to a sane state
  // as state.symbol_table might go out of scope
  reset_namespacet reset_ns(ns);

  PRECONDITION(state.call_stack().top().end_of_function->is_end_function());

  symex_threaded_step(state, get_goto_function);
  if(should_pause_symex)
    return state.symbol_table;

  while(!state.call_stack().empty())
  {
    state.has_saved_jump_target = false;
    state.has_saved_next_instruction = false;
    symex_threaded_step(state, get_goto_function);
    if(should_pause_symex)
      return state.symbol_table;
  }

  // Clients may need to construct a namespace with both the names in
  // the original goto-program and the names generated during symbolic
  // execution, so return the names generated through symbolic execution
  return state.symbol_table;
}

symbol_tablet goto_symext::resume_symex_from_saved_state(
  const get_goto_functiont &get_goto_function,
  const statet &saved_state,
  symex_target_equationt *const saved_equation)
{
  // saved_state contains a pointer to a symex_target_equationt that is
  // almost certainly stale. This is because equations are owned by bmcts,
  // and we construct a new bmct for every path that we execute. We're on a
  // new path now, so the old bmct and the equation that it owned have now
  // been deallocated. So, construct a new state from the old one, and make
  // its equation member point to the (valid) equation passed as an argument.
  statet state(saved_state, saved_equation);

  // Do NOT do the same initialization that `symex_with_state` does for a
  // fresh state, as that would clobber the saved state's program counter
  return symex_with_state(state, get_goto_function);
}

std::unique_ptr<goto_symext::statet> goto_symext::initialize_entry_point_state(
  const get_goto_functiont &get_goto_function)
{
  const irep_idt entry_point_id = goto_functionst::entry_point();

  const goto_functionst::goto_functiont *start_function;
  try
  {
    start_function = &get_goto_function(entry_point_id);
  }
  catch(const std::out_of_range &)
  {
    throw unsupported_operation_exceptiont("the program has no entry point");
  }

  // Get our path_storage pointer because this state will live beyond
  // this instance of goto_symext, so we can't take the reference directly.
  auto *storage = &path_storage;

  // create and prepare the state
  auto state = std::make_unique<statet>(
    symex_targett::sourcet(entry_point_id, start_function->body),
    symex_config.max_field_sensitivity_array_size,
    symex_config.simplify_opt,
    guard_manager,
    [storage](const irep_idt &id) { return storage->get_unique_l2_index(id); });

  CHECK_RETURN(!state->threads.empty());
  CHECK_RETURN(!state->call_stack().empty());

  goto_programt::const_targett limit =
    std::prev(start_function->body.instructions.end());
  state->call_stack().top().end_of_function = limit;
  state->call_stack().top().calling_location.pc =
    state->call_stack().top().end_of_function;
  state->call_stack().top().hidden_function = start_function->is_hidden();

  state->symex_target = &target;

  state->run_validation_checks = symex_config.run_validation_checks;

  // initialize support analyses
  auto emplace_safe_pointers_result =
    path_storage.safe_pointers.emplace(entry_point_id, local_safe_pointerst{});
  if(emplace_safe_pointers_result.second)
    emplace_safe_pointers_result.first->second(start_function->body);

  path_storage.dirty.populate_dirty_for_function(
    entry_point_id, *start_function);
  state->dirty = &path_storage.dirty;

  // Only enable loop analysis when complexity is enabled.
  if(symex_config.complexity_limits_active)
  {
    // Set initial loop analysis.
    path_storage.add_function_loops(entry_point_id, start_function->body);
    state->call_stack().top().loops_info =
      path_storage.get_loop_analysis(entry_point_id);
  }

  // make the first step onto the instruction pointed to by the initial program
  // counter
  symex_transition(*state, state->source.pc, false);

  return state;
}

symbol_tablet goto_symext::symex_from_entry_point_of(
  const get_goto_functiont &get_goto_function,
  const shadow_memory_field_definitionst &fields)
{
  auto state = initialize_entry_point_state(get_goto_function);
  // Initialize declared shadow memory fields
  state->shadow_memory.fields = fields;
//  cbmc_osek_configuration::define_task_priority();
//  cbmc_osek_configuration::define_task_id();
//  cbmc_osek_configuration::get_task_attribute(); //in cbmc_parse_options.cpp
  return symex_with_state(*state, get_goto_function);
}

void goto_symext::initialize_path_storage_from_entry_point_of(
  const get_goto_functiont &get_goto_function,
  symbol_table_baset &new_symbol_table,
  const shadow_memory_field_definitionst &fields)
{
  auto state = initialize_entry_point_state(get_goto_function);
  // Initialize declared shadow memory fields
  state->shadow_memory.fields = fields;

  path_storaget::patht entry_point_start(target, *state);
  entry_point_start.state.saved_target = state->source.pc;
  entry_point_start.state.has_saved_next_instruction = true;

  path_storage.push(entry_point_start);
}

goto_symext::get_goto_functiont
goto_symext::get_goto_function(abstract_goto_modelt &goto_model)
{
  return [&goto_model](
           const irep_idt &id) -> const goto_functionst::goto_functiont & {
    return goto_model.get_goto_function(id);
  };
}

messaget::mstreamt &
goto_symext::print_callstack_entry(const symex_targett::sourcet &source)
{
  log.status() << "'" << source.function_id << "'"
               << ": at location: " << source.pc->location_number;

  return log.status();
}


void goto_symext::print_symex_step(statet &state)
{
  // If we're showing the route, begin outputting debug info, and don't print
  // instructions we don't run.

  // We also skip dead instructions as they don't add much to step-based
  // debugging and if there's no code block at this point.
  if(
    !symex_config.show_symex_steps || !state.reachable ||
    state.source.pc->type() == DEAD ||
    (state.source.pc->code().is_nil() &&
     state.source.pc->type() != END_FUNCTION))
  {
    return;
  }

  if(state.source.pc->code().is_not_nil())
  {
    auto guard_expression = state.guard.as_expr();
    std::size_t size = 0;
    for(auto it = guard_expression.depth_begin();
        it != guard_expression.depth_end();
        ++it)
    {
      size++;
    }

    log.status() << "[" << step++ << "] --> symex_step: "
                 << state.source.function_id
                 << ": [Guard size: " << size << "] "
                 << format(state.source.pc->code());

    if(
      state.source.pc->source_location().is_not_nil() &&
      !state.source.pc->source_location().get_java_bytecode_index().empty())
    {
      log.status()
        << " bytecode index: "
        << state.source.pc->source_location().get_java_bytecode_index();
    }

    log.status() << messaget::eom;
  }

  // Print the method we're returning too.
  const auto &call_stack = state.threads[state.source.thread_nr].call_stack;
  if(state.source.pc->type() == END_FUNCTION)
  {
    if(!call_stack.empty())
    {
      log.status() << "END_FUNCTION -> Returning to: ";
      print_callstack_entry(call_stack.back().calling_location)
        << messaget::eom;
    }
  }

  // On a function call print the entire call stack.
  if(state.source.pc->type() == FUNCTION_CALL)
  {
    log.status() << messaget::eom;

//    if(!call_stack.empty())
//    {
//      log.status() << "Call stack:" << messaget::eom;
//
//      for(auto &frame : call_stack)
//      {
//        print_callstack_entry(frame.calling_location) << messaget::eom;
//      }
//
//      print_callstack_entry(state.source) << messaget::eom;
//
//      // Add the method we're about to enter with no location number.
//      log.status() << "-->" << format(state.source.pc->call_function())
//                   << messaget::eom
//                   << messaget::eom;
//    }

    print_stack_to_check(state, true);
  }
}

int goto_symext::get_API_function_type(statet &state) {
//  const auto &call_stack = state.threads[state.source.thread_nr].call_stack;
  int result = Normal_Function;
  if(state.source.pc->type() == FUNCTION_CALL)
  {
//    if(!call_stack.empty())
//    {
      // Add the method we're about to enter with no location number.
      irep_idt func_name = format_to_string(state.source.pc->call_function());
      int func_type = cbmc_osek_configuration::get_function_code(func_name);
      log.status() << "Function name: " << func_name << messaget::eom;
      switch(func_type){
        case TerminateTask:
          log.status() << "TerminateTask is called" << messaget::eom;
          result = TerminateTask;
          break;
        case ActivateTask:
          log.status() << "ActivateTask is called" << messaget::eom;

//          log.status() << "argument: " << stoi(format_to_string(state.source.pc->call_arguments().front())) << messaget::eom;
          task_called_name =
            cbmc_osek_configuration::get_task_name(stoi(format_to_string(state.source.pc->call_arguments().front())));
          log.status() << "argument: " << task_called_name <<messaget::eom ;


//                       << state.source.pc->call_arguments().begin()->type().id() << messaget::eom
//                       << state.source.pc->call_arguments().begin()->id() << messaget::eom
//                       << format_to_string(state.source.pc->call_function()) <<messaget::eom
//                       << state.source.pc->call_arguments().size() <<messaget::eom;
//          for (auto arg =  state.source.pc->call_arguments().rbegin();
//              arg != state.source.pc->call_arguments().rend(); ++arg)
//            log.status() << format_to_string(&arg) << messaget::eom;

//          for(auto arg : state.source.pc->call_arguments())
//            log.status() << arg.id() << messaget::eom;
//            << state.source.pc->call_function().id_string() <<messaget::eom;
//                       << state.source.pc->code().op0() << messaget::eom ;

          result = ActivateTask;
          break;
        case Schedule:
          switch(called_function_type) {
            case ChainTask:
              log.status() << "Schedule is called after ChainTask"
                           << messaget::eom;
              result = Schedule_after_ChainTask;
              break;
            case ActivateTask:
              log.status() << "Schedule is called after ActivateTask"
                           << messaget::eom;
              result = Schedule_after_ActivateTask;
              break;
          }
          break;
        case ChainTask:
          log.status() << "ChainTask is called" << messaget::eom;
          result = ChainTask;
          break;
        default:
          result = Normal_Function;
      }
    }
//  }
  return result;
}

///print stack to check
void goto_symext::print_stack_to_check(statet &state, bool print_next_function){
  auto &call_stack = state.threads[state.source.thread_nr].call_stack;
  log.status() << messaget::eom << "Check stack, size: " << call_stack.size()
               << messaget::eom;

  int i = 0;
  for(auto &frame : call_stack)
  {
    frame.task_name = frame.calling_location.function_id;
    log.status() << i++ << ".";
    print_callstack_entry(frame.calling_location);
    log.status() << " (from frame: task_name: " << frame.task_name
                 << ", priority: " << frame.task_priority <<")"<< messaget::eom;
  }
  log.status() << "-->";
  print_callstack_entry(state.source) << messaget::eom;

  // Add the method we're about to enter with no location number.
  if (print_next_function)
    log.status() << "Will run: " << format(state.source.pc->call_function())
                 << messaget::eom << messaget::eom;
}

///move the top stack frame to the right position (for execution order)
int goto_symext::move_top_stack_frame(statet &state, bool remove_top_frame = false){
  auto &call_stack = state.threads[state.source.thread_nr].call_stack;

  log.status() << "Task: " << call_stack.top().task_name<< ":"
               << call_stack.top().task_priority <<  messaget::eom;

//  if (remove_top_frame){
//    log.status() << "- Pop in stack: " <<  messaget::eom;
//    call_stack.pop();
//  }

  int pos = call_stack.size();
  int new_task_priority = call_stack.top().task_priority;
  int exits_frame_priority = call_stack.top().task_priority;
  dstringt func_id;

  bool is_top_frame = true;
  bool need_changed = false;
  for (auto frame =  call_stack.rbegin(); frame != call_stack.rend(); ++frame) {
//    func_id = frame->calling_location.function_id;
    func_id = frame->task_name;
    exits_frame_priority = frame->task_priority;

    log.status() << "- Position in stack: " << pos-- << ":" << func_id
                 << ", priority: " << exits_frame_priority <<  messaget::eom;
    //ignore top frame stack
    if (is_top_frame) {
      is_top_frame = false;
      continue;
    }

    if (exits_frame_priority == 0) //change from -1, all default value for frame is now 0
      continue;
    else
      if( new_task_priority > exits_frame_priority | func_id.compare("main") == 0)
        break;
      else
        need_changed = true;
  }

  if (need_changed)
  {
    log.status() << "+ Need to move the new frame after position = " << ++pos <<  messaget::eom;
    call_stack.emplace(call_stack.begin() + pos, call_stack.top()); //[pos] = call_stack.top();
    //go to top frame
    symex_end_of_function(state);
    symex_transition(state);

    log.status() << "+ stack after move frame to position = " << pos <<  messaget::eom;
    print_stack_to_check(state);
//    auto top_frame = call_stack.top();
//    call_stack.insert(call_stack.begin()+pos,top_frame);
  }else {
    log.status() << "+ No need to move the new frame!" <<  messaget::eom;
    return -1;
  }
  return  pos;
}

///assign priority and execute function
void goto_symext::assign_priority_and_execution_order_after_API(statet &state, const get_goto_functiont &get_goto_function, bool remove_top_frame = false)
{
  //assign values for stack frame (task name, priority)
  int tsk_priority = assign_value_to_top_stack_frame(state);
  //print stack to check
  log.status() << "-STACK After assigning priority:" << messaget::eom;
  print_stack_to_check(state);

  //put new stack frame to right position (with its priority)
  if(tsk_priority > 0)
  {
    log.status() << messaget::eom << "--> Find position for Task:" << messaget::eom;
    move_top_stack_frame(state, remove_top_frame);
  }
  else
  {
    log.status() << "No need to order the task" << messaget::eom;
  }



//    if(function_called.compare("ChainTask") == 0)
//    {
//      log.status() << messaget::eom << "--> ChainTask " << messaget::eom;
//      ///call ChainTask
//      goto_symext::prepare_chain_task(state);
//      print_stack_to_check(state);
//    }
}

///assign priority of the function to the top stack frame
int goto_symext::assign_value_to_top_stack_frame(statet &state){
    auto &call_stack = state.threads[state.source.thread_nr].call_stack;

    call_stack.top().task_name = call_stack.back().calling_location.function_id;
    int priority = cbmc_osek_configuration::get_task_priority(call_stack.top().task_name);
    if (priority >= 0) {
      call_stack.top().task_priority = priority;
    }

    goto_symext::log.status() << "Values of top task frame will be: "
                              << call_stack.top().task_name
                              << "," << priority << messaget::eom;
    return  priority;
}

/// do just one step
void goto_symext::symex_step(
  const get_goto_functiont &get_goto_function,
  statet &state)
{
  // Print debug statements if they've been enabled.
  print_symex_step(state); //can realize called_function_type: NO! print only

  // Print debug statements if they've been enabled.
//  print_symex_step(state);
//  execute_next_instruction(get_goto_function, state);
//  kill_instruction_local_symbols(state);

  if(state.source.pc->type() == FUNCTION_CALL)
  {
    auto func_type = get_API_function_type(state);
    if(func_type != Normal_Function || called_function_type == No_Function) //remember last function name
      called_function_type = func_type;

    //execute function
    auto &call_stack = state.threads[state.source.thread_nr].call_stack;
    const goto_programt::instructiont &instruction=*state.source.pc;
    irep_idt caller_ChainTask;

    switch(called_function_type)
    {
    case Normal_Function:
      symex_function_call(get_goto_function, state, instruction);
      break;
    case TerminateTask: //same as END_FUNCTION
      symex_end_of_function(state); //end terminate function
      symex_transition(state);
      print_stack_to_check(state);
      called_function_type = No_Function;
      break;

    case ActivateTask:
      log.status() << "----------------------------------------" << messaget::eom;
      log.status() << "Execute ActivateTask " << messaget::eom;

      //execute ActivateTask
      execute_next_instruction(get_goto_function, state);
      assign_value_to_top_stack_frame(state);
//      print_stack_to_check(state);

//      while (state.source.function_id.compare("ActivateTask") == 0){
      while(as_string(state.source.function_id).find("ActivateTask") != std::string::npos){
        log.status() << "--> symex_step: "
                     << state.source.function_id << " "
                     << format(state.source.pc->code())<< messaget::eom;
        execute_next_instruction(get_goto_function, state);
        assign_value_to_top_stack_frame(state);
        print_stack_to_check(state);
      }

      //execute Wrapper Function
      log.status() << "--> execute wrapper task: "
                   << state.source.function_id << messaget::eom;
      execute_next_instruction(get_goto_function, state);
      assign_value_to_top_stack_frame(state);

      log.status() << "----------Move frame---------"
                   << task_called_name << messaget::eom;
      move_top_stack_frame(state, true);
      print_stack_to_check(state);

      //remove caller activate
      log.status() << "--> remove caller activate task: "
                  << state.source.function_id << messaget::eom;
      symex_end_of_function(state); //terminate function
      symex_transition(state);
      print_stack_to_check(state);
      called_function_type = No_Function;

//      log.status() << "1 " << messaget::eom;
//      log.status() << "--> symex_step: "
//                   << state.source.function_id << " "
//                   << format(state.source.pc->code())<< messaget::eom;
//      execute_next_instruction(get_goto_function, state); //execute ActivateTask
//      assign_value_to_top_stack_frame(state);
//      print_stack_to_check(state);
//
//      log.status() << "2 " << messaget::eom;
//      log.status() << "--> symex_step: "
//                   << state.source.function_id << " "
//                   << format(state.source.pc->code())<< messaget::eom;
//      execute_next_instruction(get_goto_function, state); //execute ActivateTask
//      assign_value_to_top_stack_frame(state);
//      print_stack_to_check(state);
//
//      log.status() << "3 " << messaget::eom;
//      log.status() << "--> symex_step: "
//                   << state.source.function_id << " "
//                   << format(state.source.pc->code())<< messaget::eom;
//      execute_next_instruction(get_goto_function, state); //execute TASK1
//      assign_value_to_top_stack_frame(state);
//      print_stack_to_check(state);
//
//      log.status() << "4 " << messaget::eom;
//      log.status() << "--> symex_step: "
//                   << state.source.function_id << " "
//                   << format(state.source.pc->code())<< messaget::eom;
//      execute_next_instruction(get_goto_function, state); //execute Schedule
//      assign_value_to_top_stack_frame(state);
//      print_stack_to_check(state);
//
//      log.status() << "5 " << messaget::eom;
//      log.status() << "--> symex_step: "
//                   << state.source.function_id << " "
//                   << format(state.source.pc->code())<< messaget::eom;
//      execute_next_instruction(get_goto_function, state); //execute TASK1
//      assign_value_to_top_stack_frame(state);
//      print_stack_to_check(state);
//
//      log.status() << "6 " << messaget::eom;
//      log.status() << "--> symex_step: "
//                   << state.source.function_id << " "
//                   << format(state.source.pc->code())<< messaget::eom;
//      execute_next_instruction(get_goto_function, state); //execute T1
//      assign_value_to_top_stack_frame(state);
//      print_stack_to_check(state);
//
//      log.status() << "move?" << messaget::eom;

      //      called_function_type = ActivateTask; //no needed!
//      log.status() << "----------------------------------------"
//                   << task_called_name << messaget::eom;

//      log.status() << "7 " << messaget::eom;
//      log.status() << "--> symex_step: "
//                   << state.source.function_id
//                   << format(state.source.pc->code())<< messaget::eom;
//      execute_next_instruction(get_goto_function, state); //execute T1
//      assign_value_to_top_stack_frame(state);
//      print_stack_to_check(state);


//      if (task_called_name.compare("Task2") == 0){
//        log.status() << "----------Move frame---------"
//                     << task_called_name << messaget::eom;
//        move_top_stack_frame(state, true);
//        print_stack_to_check(state);
//      }

      called_function_type = No_Function;
      break;
    case Schedule_after_ActivateTask:
      break;
      //execute & assign priority
      log.status() << "execute schedule 1" << messaget::eom;
      execute_next_instruction(get_goto_function, state);
      print_stack_to_check(state);
      log.status() << "assign_priority_and_execution_order_after_API_SCHEDULE"<< messaget::eom;
      goto_symext::assign_priority_and_execution_order_after_API(
        state, get_goto_function); //assign priority - if needed
                                   //      called_function_type = No_Function;
      print_stack_to_check(state);
      execute_next_instruction(get_goto_function, state);
      log.status() << "execute schedule 2" << messaget::eom;
      goto_symext::assign_priority_and_execution_order_after_API(
        state, get_goto_function); //assign priority - if needed
                                   //      called_function_type = No_Function;
//      execute_next_instruction(
//        get_goto_function, state); //run until a new Function_type found -> thieu vi tri
      break;
    case ChainTask:
      //execute task
//      log.status() << "**Execute ChainTask: " << messaget::eom;
//      print_symex_step(state);
//      symex_function_call(get_goto_function, state, instruction);
//      called_function_type = ChainTask;
//      break;
//    case Schedule_after_ChainTask:
      log.status() << "----------------------------------------" << messaget::eom;
      log.status() << "Execute ChainTask " << messaget::eom;


      //execute ChainTask
      execute_next_instruction(get_goto_function, state);
      assign_value_to_top_stack_frame(state);
      print_stack_to_check(state);

      caller_ChainTask = call_stack.top().task_name; //remember task name for ending
      log.status() << "Caller ChainTask: " << caller_ChainTask << messaget::eom;
      //execute API
//      while (state.source.function_id.compare("ChainTask") == 0){
      while(as_string(state.source.function_id).find("ChainTask") != std::string::npos){
        //execute instruction in ChainTask
        log.status() << "--> symex_step: "
                     << state.source.function_id << " "
                     << format(state.source.pc->code())<< messaget::eom;
        execute_next_instruction(get_goto_function, state);
//        assign_value_to_top_stack_frame(state);
        print_stack_to_check(state);
      }

      call_stack.pop(); //for ChainTask
      call_stack.pop(); //for caller
      log.status() << "--> remove current task" << messaget::eom;
      print_stack_to_check(state);
//      //remove task frame related to caller
//      while (call_stack.top().task_name.compare(caller_ChainTask) == 0)
//        call_stack.pop();

      //execute Wrapper Function
      log.status() << "--> execute wrapper task: "
                   << state.source.function_id << messaget::eom;
      execute_next_instruction(get_goto_function, state);
//      call_stack.pop();
      assign_value_to_top_stack_frame(state);
      print_stack_to_check(state);

      log.status() << "----------Move frame---------"
                   << task_called_name << messaget::eom;
      move_top_stack_frame(state, true);
      print_stack_to_check(state);

      //remove caller chaintask
      log.status() << "--> remove caller chaintask: "
                   << state.source.function_id << messaget::eom;
      symex_end_of_function(state); //terminate function
      symex_transition(state);
      print_stack_to_check(state);
      called_function_type = No_Function;

      //      log.status() << "1 " << messaget::eom;
      //      log.status() << "--> symex_step: "
      //                   << state.source.function_id << " "
      //                   << format(state.source.pc->code())<< messaget::eom;
      //      execute_next_instruction(get_goto_function, state); //execute ActivateTask
      //      assign_value_to_top_stack_frame(state);
      //      print_stack_to_check(state);
      //
      //      log.status() << "2 " << messaget::eom;
      //      log.status() << "--> symex_step: "
      //                   << state.source.function_id << " "
      //                   << format(state.source.pc->code())<< messaget::eom;
      //      execute_next_instruction(get_goto_function, state); //execute ActivateTask
      //      assign_value_to_top_stack_frame(state);
      //      print_stack_to_check(state);
      //
      //      log.status() << "3 " << messaget::eom;
      //      log.status() << "--> symex_step: "
      //                   << state.source.function_id << " "
      //                   << format(state.source.pc->code())<< messaget::eom;
      //      execute_next_instruction(get_goto_function, state); //execute TASK1
      //      assign_value_to_top_stack_frame(state);
      //      print_stack_to_check(state);
      //
      //      log.status() << "4 " << messaget::eom;
      //      log.status() << "--> symex_step: "
      //                   << state.source.function_id << " "
      //                   << format(state.source.pc->code())<< messaget::eom;
      //      execute_next_instruction(get_goto_function, state); //execute Schedule
      //      assign_value_to_top_stack_frame(state);
      //      print_stack_to_check(state);
      //
      //      log.status() << "5 " << messaget::eom;
      //      log.status() << "--> symex_step: "
      //                   << state.source.function_id << " "
      //                   << format(state.source.pc->code())<< messaget::eom;
      //      execute_next_instruction(get_goto_function, state); //execute TASK1
      //      assign_value_to_top_stack_frame(state);
      //      print_stack_to_check(state);
      //
      //      log.status() << "6 " << messaget::eom;
      //      log.status() << "--> symex_step: "
      //                   << state.source.function_id << " "
      //                   << format(state.source.pc->code())<< messaget::eom;
      //      execute_next_instruction(get_goto_function, state); //execute T1
      //      assign_value_to_top_stack_frame(state);
      //      print_stack_to_check(state);
      //
      //      log.status() << "move?" << messaget::eom;

      //      called_function_type = ActivateTask; //no needed!
      //      log.status() << "----------------------------------------"
      //                   << task_called_name << messaget::eom;

      //      log.status() << "7 " << messaget::eom;
      //      log.status() << "--> symex_step: "
      //                   << state.source.function_id
      //                   << format(state.source.pc->code())<< messaget::eom;
      //      execute_next_instruction(get_goto_function, state); //execute T1
      //      assign_value_to_top_stack_frame(state);
      //      print_stack_to_check(state);


      //      if (task_called_name.compare("Task2") == 0){
      //        log.status() << "----------Move frame---------"
      //                     << task_called_name << messaget::eom;
      //        move_top_stack_frame(state, true);
      //        print_stack_to_check(state);
      //      }

//      break;
      //    case Schedule:
      //end current task -> remove task frame
//      log.status() << "Schedule after ChainTask " << messaget::eom;
//      log.status() << "**Remove 1st Task from stack: "
//                   << call_stack.top().task_name << ":"
//                   << call_stack.top().task_priority << messaget::eom;
//      call_stack.pop();
//      log.status() << "**Remove 2nd Task from stack: "
//                   << call_stack.top().task_name << ":"
//                   << call_stack.top().task_priority << messaget::eom;
//      call_stack.pop();
//      log.status() << "**Remove 3rd Task from stack: "
//                   << call_stack.top().task_name << ":"
//                   << call_stack.top().task_priority << messaget::eom;
//      call_stack.pop();
//      print_stack_to_check(state);
//
//      //      symex_end_of_function(state); //auto go to the last task frame instruction
//      symex_transition(state);
//      symex_function_call(get_goto_function, state, instruction);
//      goto_symext::assign_priority_and_execution_order_after_API(
//        state, get_goto_function); //assign priority - if needed
//      called_function_type = Normal_Function;
//      print_stack_to_check(state);
      break;
    default:
      //      called_function_type = Normal_Function; //cannot set value here
      execute_next_instruction(get_goto_function, state);
      //      called_function_type = Normal_Function; -> will not realize next step for scheduling
      break;
    }
    assign_value_to_top_stack_frame(state);
    print_stack_to_check(state);
  } else { //instruction only
      execute_next_instruction(get_goto_function, state);
  }
//  is_related_API_function_call = 0;

  kill_instruction_local_symbols(state);
}


void goto_symext::execute_next_instruction(
  const get_goto_functiont &get_goto_function,
  statet &state)
{
  PRECONDITION(!state.threads.empty());
  PRECONDITION(!state.call_stack().empty());

  const goto_programt::instructiont &instruction=*state.source.pc;

  if(!symex_config.doing_path_exploration)
    merge_gotos(state);

  // depth exceeded?
  if(state.depth > symex_config.max_depth)
  {
    // Rule out this path:
    symex_assume_l2(state, false_exprt());
  }
  state.depth++;

  // actually do instruction
  switch(instruction.type())
  {
  case SKIP:
    if(state.reachable)
      target.location(state.guard.as_expr(), state.source);
    symex_transition(state);
    break;

  case END_FUNCTION:
    // do even if !state.reachable to clear out frame created
    // in symex_start_thread
    symex_end_of_function(state);
    symex_transition(state);
    break;

  case LOCATION:
    if(state.reachable)
      target.location(state.guard.as_expr(), state.source);
    symex_transition(state);
    break;

  case GOTO:
    if(state.reachable)
      symex_goto(state);
    else
      symex_unreachable_goto(state);
    break;

  case ASSUME:
    if(state.reachable)
      symex_assume(state, instruction.condition());
    symex_transition(state);
    break;

  case ASSERT:
    if(state.reachable && !ignore_assertions)
      symex_assert(instruction, state);
    symex_transition(state);
    break;

  case SET_RETURN_VALUE:
    if(state.reachable)
      symex_set_return_value(state, instruction.return_value());
    symex_transition(state);
    break;

  case ASSIGN:
    if(state.reachable)
      symex_assign(state, instruction.assign_lhs(), instruction.assign_rhs());

    symex_transition(state);
    break;

  case FUNCTION_CALL:
    if(state.reachable) {
      symex_function_call(get_goto_function, state, instruction);
    } else
      symex_transition(state);
    break;

  case OTHER:
    if(state.reachable)
      symex_other(state);
    symex_transition(state);
    break;

  case DECL:
    if(state.reachable)
      symex_decl(state);
    symex_transition(state);
    break;

  case DEAD:
    symex_dead(state);
    symex_transition(state);
    break;

  case START_THREAD:
    symex_start_thread(state);
    symex_transition(state);
    break;

  case END_THREAD:
    // behaves like assume(0);
    if(state.reachable)
      state.reachable = false;
    symex_transition(state);
    break;

  case ATOMIC_BEGIN:
    symex_atomic_begin(state);
    symex_transition(state);
    break;

  case ATOMIC_END:
    symex_atomic_end(state);
    symex_transition(state);
    break;

  case CATCH:
    symex_catch(state);
    symex_transition(state);
    break;

  case THROW:
    symex_throw(state);
    symex_transition(state);
    break;

  case NO_INSTRUCTION_TYPE:
    throw unsupported_operation_exceptiont("symex got NO_INSTRUCTION");

  case INCOMPLETE_GOTO:
    DATA_INVARIANT(false, "symex got unexpected instruction type");
  }

  complexity_violationt complexity_result =
    complexity_module.check_complexity(state);
  if(complexity_result != complexity_violationt::NONE)
    complexity_module.run_transformations(complexity_result, state);
}

void goto_symext::kill_instruction_local_symbols(statet &state)
{
  for(const auto &symbol_expr : instruction_local_symbols)
    symex_dead(state, symbol_expr);
  instruction_local_symbols.clear();
}

/// Check if an expression only contains one unique symbol (possibly repeated
/// multiple times)
/// \param expr: The expression to examine
/// \return If only one unique symbol occurs in \p expr then return it;
///   otherwise return an empty std::optional
static std::optional<symbol_exprt>
find_unique_pointer_typed_symbol(const exprt &expr)
{
  std::optional<symbol_exprt> return_value;
  for(auto it = expr.depth_cbegin(); it != expr.depth_cend(); ++it)
  {
    const symbol_exprt *symbol_expr = expr_try_dynamic_cast<symbol_exprt>(*it);
    if(symbol_expr && can_cast_type<pointer_typet>(symbol_expr->type()))
    {
      // If we already have a potential return value, check if it is the same
      // symbol, and return an empty std::optional if not
      if(return_value && *symbol_expr != *return_value)
      {
        return {};
      }
      return_value = *symbol_expr;
    }
  }

  // Either expr contains no pointer-typed symbols or it contains one unique
  // pointer-typed symbol, possibly repeated multiple times
  return return_value;
}

void goto_symext::try_filter_value_sets(
  goto_symex_statet &state,
  exprt condition,
  const value_sett &original_value_set,
  value_sett *jump_taken_value_set,
  value_sett *jump_not_taken_value_set,
  const namespacet &ns)
{
  condition = state.rename<L1>(std::move(condition), ns).get();

  std::optional<symbol_exprt> symbol_expr =
    find_unique_pointer_typed_symbol(condition);

  if(!symbol_expr)
  {
    return;
  }

  const pointer_typet &symbol_type = to_pointer_type(symbol_expr->type());

  const std::vector<exprt> value_set_elements =
    original_value_set.get_value_set(*symbol_expr, ns);

  std::unordered_set<exprt, irep_hash> erase_from_jump_taken_value_set;
  std::unordered_set<exprt, irep_hash> erase_from_jump_not_taken_value_set;
  erase_from_jump_taken_value_set.reserve(value_set_elements.size());
  erase_from_jump_not_taken_value_set.reserve(value_set_elements.size());

  // Try evaluating the condition with the symbol replaced by a pointer to each
  // one of its possible values in turn. If that leads to a true for some
  // value_set_element then we can delete it from the value set that will be
  // used if the condition is false, and vice versa.
  for(const exprt &value_set_element : value_set_elements)
  {
    if(
      value_set_element.id() == ID_unknown ||
      value_set_element.id() == ID_invalid)
    {
      continue;
    }

    const bool exclude_null_derefs = false;
    if(value_set_dereferencet::should_ignore_value(
         value_set_element, exclude_null_derefs, language_mode))
    {
      continue;
    }

    value_set_dereferencet::valuet value =
      value_set_dereferencet::build_reference_to(
        value_set_element, *symbol_expr, ns);

    if(value.pointer.is_nil())
      continue;

    exprt modified_condition(condition);

    address_of_aware_replace_symbolt replace_symbol{};
    replace_symbol.insert(*symbol_expr, value.pointer);
    replace_symbol(modified_condition);

    // This do_simplify() is needed for the following reason: if `condition` is
    // `*p == a` and we replace `p` with `&a` then we get `*&a == a`. Suppose
    // our constant propagation knows that `a` is `1`. Without this call to
    // do_simplify(), state.rename() turns this into `*&a == 1` (because
    // rename() doesn't do constant propagation inside addresses), which
    // do_simplify() turns into `a == 1`, which cannot be evaluated as true
    // without another round of constant propagation.
    // It would be sufficient to replace this call to do_simplify() with
    // something that just replaces `*&x` with `x` whenever it finds it.
    do_simplify(modified_condition);

    state.record_events.push(false);
    modified_condition = state.rename(std::move(modified_condition), ns).get();
    state.record_events.pop();

    do_simplify(modified_condition);

    if(jump_taken_value_set && modified_condition.is_false())
    {
      erase_from_jump_taken_value_set.insert(value_set_element);
    }
    else if(jump_not_taken_value_set && modified_condition.is_true())
    {
      erase_from_jump_not_taken_value_set.insert(value_set_element);
    }
  }
  if(jump_taken_value_set && !erase_from_jump_taken_value_set.empty())
  {
    auto entry_index = jump_taken_value_set->get_index_of_symbol(
      symbol_expr->get_identifier(), symbol_type, "", ns);
    jump_taken_value_set->erase_values_from_entry(
      *entry_index, erase_from_jump_taken_value_set);
  }
  if(jump_not_taken_value_set && !erase_from_jump_not_taken_value_set.empty())
  {
    auto entry_index = jump_not_taken_value_set->get_index_of_symbol(
      symbol_expr->get_identifier(), symbol_type, "", ns);
    jump_not_taken_value_set->erase_values_from_entry(
      *entry_index, erase_from_jump_not_taken_value_set);
  }
}
