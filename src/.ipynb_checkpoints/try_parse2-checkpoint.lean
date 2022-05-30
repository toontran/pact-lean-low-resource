import data.nat.basic
import system.io
import tactic.core
import tactic

import utils
import .tactic_state
import basic.queue

section tactic_state
open interaction_monad.result
setup_tactic_parser

/- set this to tt to enable tracing
  `tactic.set_bool_option` is tactic state specific,
  and is difficult to globally set -/

meta def num_goals' : tactic_state → option ℕ :=
λ ts, match tactic.num_goals ts with | (success val _) := pure val | _ := none end

-- TODO(jesse): this is a hack. might be better to do this in python
meta def consume_with_parser {α} (p : lean.parser α) : string → io string := λ inp, do {
  io.run_tactic' $ do
    prod.snd <$> (lean.parser.run_with_input (with_input p inp) "")
}

-- TODO(jesse): performance
meta def consume_spaces : string → string
| arg@⟨[]⟩ := arg
| arg@⟨(x::xs)⟩ := if x = ' ' then consume_spaces ⟨xs⟩ else arg

-- WARNING: this is a hack
meta def remove_indents_with_split (c : char := '\t'): string → string := λ str,
let strs := str.split (= '\t') in
string.intercalate (⟨['\t']⟩ : string) (consume_spaces <$> strs)

meta def postprocess_tactic_state : tactic_state → tactic string := λ ts, do
  let main : tactic string := do {
    let ts_str := ts.to_format.to_string,
    tabbed_ts_str ← do {
      if (num_goals' ts).get_or_else 0 ≤ 1
      then pure $ ts_str.replace_char '\n' '\t'
      else tactic.unsafe_run_io $ (λ x, string.replace_char x '\n' '\t')
             <$> (consume_with_parser small_nat >=>
               consume_with_parser ident) ts_str},
    pure $ remove_indents_with_split '\t' tabbed_ts_str
  },
  main <|> (let msg := "[postprocess_tactic_state] WARNING: POSTPROCESSING FAILED" in tactic.trace msg *> tactic.fail msg)

end tactic_state

meta def add_open_namespace : name → tactic unit := λ nm, do
env ← tactic.get_env, tactic.set_env (env.execute_open nm)

meta def add_open_namespaces (nms : list name) : tactic unit :=
nms.mmap' add_open_namespace

section run_with_state'

namespace interaction_monad
open interaction_monad.result
meta def run_with_state' {σ₁ σ₂ : Type} {α : Type*} (state : σ₁) (tac : interaction_monad σ₁ α) : interaction_monad σ₂ α :=
λ s, match (tac state) with
     | (success val _) := success val s
     | (exception fn pos _) := exception fn pos s
     end
end interaction_monad
end run_with_state'

namespace tactic

open interaction_monad.result
meta def run (tac : tactic unit) : tactic (interaction_monad.result tactic_state unit) := do {
  σ ← get_state,
  match tac σ with
  | r@(success _ new_state) := interaction_monad.set_state new_state *> pure r
  | r@(exception fn pos new_state) := pure r
  end
}

-- meta instance has_format_result {α σ} [has_to_format σ] [has_to_format α] : has_to_format (interaction_monad.result σ α) := ⟨by mk_to_format `interaction_monad.result⟩ -- ayyy

meta instance has_to_format_tactic_result {α : Type*} [has_to_format α] : has_to_format (interaction_monad.result tactic_state α) :=
⟨λ r,
  match r with
  | (success val new_state) := format!"SUCCESS!\nNEW_STATE: {new_state}\nVAL: {val}"
  | (exception fn pos old_state) := do {
    let msg := (fn.get_or_else (λ _, format.of_string "n/a")) (),
    format!"EXCEPTION!\nMSG: {msg}\nPOS: {pos}\nOLD_STATE: {old_state}"
  }
  end
⟩

meta instance has_to_tactic_format_tactic_result {α : Type*} [has_to_format α] : has_to_tactic_format (interaction_monad.result tactic_state α) :=
⟨λ σ, pure $ has_to_format.to_format σ⟩

end tactic

section parse_eval_tac
setup_tactic_parser
open tactic

meta def parse_eval_tac
  (ps : parser_state)
  (tactic_string : string)
  : tactic (tactic unit × format) := do {
  let itactic_string := "{" ++ tactic_string ++ "}",
  texpr ← (reflected_value.expr ∘ prod.fst) <$>
    (interaction_monad.run_with_state' ps $ with_input parser.itactic_reflected itactic_string),
  prod.mk <$> (eval_expr (tactic unit) texpr) <*> has_to_tactic_format.to_tactic_format texpr
}

end parse_eval_tac

section frontend

open tactic lean lean.parser interactive
meta def read_eval_print_loop (ps : parser_state) : tactic unit :=
do
  trace "\nTactic state:",
  trace_state,
  let rest : tactic unit := do
  {trace "\nEnter a tactic command:",
  tactic_string <- tactic.unsafe_run_io $ io.get_line,
  (t, fmt) ← parse_eval_tac ps tactic_string,
  trace "",
  trace ("Running tactic:\n" ++ fmt.to_string),
  tactic.run t >>= eval_trace,  -- runs the tactic on the goal.  It is crashing
  read_eval_print_loop},  --- loops forever
  done <|> rest

--- like main_t, but sets the goal and environment to a user-supplied theorem in mathlib
--- note: if the environment contains all declarations in mathlib,
--- and olean files exist,
--- we don't need to supply the lean file as env.decl_olean will find it automatically.
meta def main_t_at : parser_state → tactic unit := λ ps, do {
  trace "enter declaration to prove",
  goal_nm_string ← tactic.unsafe_run_io $ io.get_line,
  ⟨nm, _⟩ ← interaction_monad.run_with_state' ps $ with_input ident goal_nm_string,
  env ← get_env,
  decl ← env.get nm,
  let g := decl.type,
  set_goal_to g,
  lean_file ← env.decl_olean nm,
  set_env_core $ environment.for_decl_of_imported_module lean_file nm,
  read_eval_print_loop ps
}

@[user_command]
meta def main_app_at
(meta_info : decl_meta_info) (_ : parse (tk "main_app_at")) : lean.parser unit :=
get_state >>= of_tactic ∘ (main_t_at)

end frontend

section main

setup_tactic_parser

open tactic
meta def main_t : parser_state → tactic unit := λ ps,
do
  trace "Enter a goal:",
  set_goal_to `(true),
  goal_string <- tactic.unsafe_run_io $ io.get_line,
  trace "GOAL STRING: " *> trace goal_string,
  (goal_pexpr, _) ← interaction_monad.run_with_state' ps $ with_input types.texpr goal_string,
  eval_trace ps.cur_pos,
  set_goal_to <e> goal_pexpr,
  (read_eval_print_loop ps) *> main_t ps  -- loops forever

@[user_command]
meta def main
(meta_info : decl_meta_info) (_ : parse (tk "main")) : lean.parser unit :=
(get_state >>= of_tactic ∘ main_t)

end main
