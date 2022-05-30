import all

section eval_trace

meta def EVAL_TRACE := tt

meta def set_show_eval_trace : bool → tactic unit := tactic.set_bool_option `evaltrace

meta def eval_trace {α} [has_to_tactic_format α] : α → tactic unit | a := do {
  evaltrace_flag ← tactic.get_bool_option `evaltrace ff,
  -- let trace_flag := tactic.is_trace_enabled_for `EVAL_TRACE,
  let trace_flag := EVAL_TRACE,
  let cond := (trace_flag || evaltrace_flag),
  when cond (tactic.trace a)
}

end eval_trace

namespace set_env

meta def get_env_at_decl (decl_nm : name) : tactic environment := do {
  env ← tactic.get_env,
  lean_file ← env.decl_olean decl_nm,
  pure $ environment.for_decl_of_imported_module lean_file decl_nm
}

meta def set_env_at_decl (decl_nm : name) : tactic unit := do {
    env ← get_env_at_decl decl_nm,
    eval_trace format!"[set_env_at_decl] GOT ENV AT DECL {decl_nm}",
    tactic.set_env_core env,
    eval_trace format!"[set_env_at_decl] SET ENV AT DECL {decl_nm}"
}

end set_env


meta def add_open_namespace : name → tactic unit := λ nm, do
env ← tactic.get_env, tactic.set_env (env.execute_open nm)

meta def add_open_namespaces (nms : list name) : tactic unit :=
nms.mmap' add_open_namespace


run_cmd do {
set_env.set_env_at_decl `finset.union_comm,
add_open_namespaces [
`finset,
`finset,
`nat,
`function,
`subtype,
`multiset]}

namespace inspection_tools

def join (sep : string) : list string → string
| [x]     := x
| []      := ""
| (x::xs) := x ++ sep ++ join xs

meta def expr_to_string (e : expr bool.tt) : tactic string :=
do
  o ← tactic.get_options,
  tactic.set_options (options.mk.set_bool `pp.all tt),
  f ← tactic.pp e,
  tactic.set_options o,  -- set back to before
  return $ to_string f
  
meta def local_cxt_to_string (v : expr bool.tt) : tactic string := 
do 
  tp ← tactic.infer_type v,
  v_str ← expr_to_string v,
  tp_str ← expr_to_string tp,
  return $ v_str ++ "\n\n" ++ tp_str

meta def goal_to_string (g : expr) : tactic string :=
do 
  tactic.set_goals [g],
  goal ← tactic.target,
  local_cxt ← tactic.local_context,
  let local_cxt_len := list.length local_cxt,
  goal_str ← expr_to_string goal,
  local_cxt_strs ← (list.mmap local_cxt_to_string local_cxt),
  let s1 := goal_str ++ "\n\n",
  let s2 := "Local Context Vars: " ++ (to_string local_cxt_len) ++ "\n\n",
  let s3 := join "\n\n" local_cxt_strs,
  return $ s1 ++ s2 ++ s3

meta def state_report : tactic string :=
do 
 gs ← tactic.get_goals,
 -- loop over all goals (has effect of resetting the goal each time)
 let gs_len := list.length gs,
 goal_strings ← gs.mmap goal_to_string,
 tactic.set_goals gs,  -- set goals back
 let s := "Goals: " ++ (to_string gs_len) ++ "\n\n" ++ (join "\n\n" goal_strings),
 return s
 
meta def trace_goal_state : tactic unit :=
do 
 s ← state_report,
 tactic.trace s,
 return ()

end inspection_tools


namespace custom
 
meta def trace_custom_state : tactic unit :=
do 
 tactic.trace "",  -- make more interesting
 return ()

end custom

section example_block
universes u_1
example {α : Type u_1} [_inst_1 : decidable_eq α] (s₁ s₂ : finset α) : s₁ ∪ s₂ = s₂ ∪ s₁ :=
begin
simp,
inspection_tools.trace_goal_state,
custom.trace_custom_state,
end
end example_block

#eval 1