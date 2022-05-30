import all
import data.nat.basic
import system.io
import tactic.core
import tactic
import init.meta.expr

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

end frontend

section evaluation_harness

meta def run_tac_with_tactic_state
  (tac : tactic unit)
  (ts : tactic_state)
  : tactic (result _ _) := do {
  tactic.write ts,
  pure $ tac ts
}

meta structure EvaluationInput : Type :=
(decl_nm : name)
(ts_data : tactic_state_data)
(tactic_string : string)
(open_namespaces : list name)

/- (before_state, action, after_state) tuple -/
meta structure EvaluationResult : Type :=
(before_state : tactic_state)
(tactic_string : string)
(result : result tactic_state unit)

meta instance : has_to_format EvaluationResult :=
⟨λ ⟨σ, tac_str, r⟩,
  format.join [
    -- hmm. why doesn't the highlighting work?
    format.highlight "INPUT STATE:\n" format.color.pink,
    σ.to_format,
    "\n\n",
    format.highlight "ACTION:\n" format.color.pink,
    tac_str,
    "\n\n",
    format.highlight  "RESULT:\n" format.color.pink,
    (has_to_format.to_format r)
  ]
⟩

/-- Creates an empty tactic state. -/
meta def mk_tactic_state : tactic tactic_state :=
tactic.unsafe_run_io $ io.run_tactic' $ tactic.exact `(trivial) *> tactic.read

/-- creates tactic_state_data as if we were proving the declaration
 (currently only theorems are supported) with name `decl_nm`. -/
meta def get_tsd_at_decl (decl_nm : name) : tactic tactic_state_data := do {
  env ← tactic.get_env,
  decl ← env.get decl_nm,
  mk_tactic_state >>= tactic.write,
  ts ← tactic.read,
  tactic.set_goal_to decl.type,
  result ← tactic_state_data.get,
  tactic.write ts,
  pure result
}

end evaluation_harness




section parse_tac

setup_tactic_parser

open tactic

/-- Parse a reflected interactive tactic from a string.
    The result can be evaluated to a `tactic unit` by using
    `eval_expr (tactic unit)`. -/
meta def parse_itactic_reflected (tactic_string : string) : tactic expr :=
let itactic_string := "{ " ++ tactic_string ++  " }" in
lean.parser.run $ do
  get_state >>= λ ps, of_tactic $ do
    tactic.set_env ps.env,
    --eval_trace format!"[parse_itactic_reflected] TRYING TO PARSE {itactic_string}",
    (reflected_value.expr ∘ prod.fst) <$>
      (@interaction_monad.run_with_state' parser_state _ _ ps $
         with_input parser.itactic_reflected itactic_string)

-- meta def parse_itactic (tactic_string : string) : tactic expr := parse_itactic_reflected tactic_string
  -- rtac ← parse_itactic_reflected tactic_string
  -- eval_expr (tactic unit) rtac

/-- Parse an interactive tactic from a string. -/
meta def parse_itactic (tactic_string : string) : tactic (tactic unit) := do
  rtac ← parse_itactic_reflected tactic_string,
  eval_expr (tactic unit) rtac

end parse_tac


namespace tactic
open interaction_monad interaction_monad.result

/- capture but backtrack the state -/
meta def capture' {α} (t : tactic α) : tactic (tactic_result α) :=
λ s, match t s with
| (success r s') := success (success r s') s
| (exception f p s') := success (exception f p s') s
end

end tactic

meta def get_tac_and_capture_result (next_candidate : string) (timeout : ℕ := 5000) : tactic unit := do {
  tac ← do {
    env ← tactic.get_env,
    eval_trace format!"[get_tac_and_capture_result] PARSING TACTIC: {next_candidate}",
    tac ← parse_itactic next_candidate,
    eval_trace format!"[get_tac_and_capture_result] PARSE SUCCESSFUL",
    tactic.set_env env,
    pure tac
  },
  eval_trace format!"[get_tac_and_capture_result] TRYING TACTIC: {next_candidate}",
  result ← tactic.capture' (tactic.try_for_time timeout $ tactic.try_for 200000 tac), -- if `tac` fails, exception is captured here
  eval_trace format!"[get_tac_and_capture_result] RESULT: {result}"
}

meta def try_get_tac_and_capture_result (tac_string : string) (timeout : ℕ := 5000) : tactic unit := do {
  get_tac_and_capture_result tac_string timeout <|> do {
    let msg : format := format!"[try_get_tac_and_capture_result] parse_itactic failed on {tac_string}",
    eval_trace msg
    -- interaction_monad.mk_exception msg none <$> tactic.read
  }
}  





section main

open tactic lean lean.parser interactive
open io
setup_tactic_parser
meta def main : io unit := do {
    args ← io.cmdline_args,
    for_ args (λ arg, do io.put_str_ln' format!"Input arguments: {arg}"),

    goal_nm_string ← args.nth_except 0 "goal_nm_string",
    tactic_string ← args.nth_except 1 "tactic_string",
    goal_new_string ← args.nth_except 2 "goal_new_string",
  
    let run_parse : string → io unit := λ args, do {
        io.run_tactic' $ do 
        {
            --trace "\nTactic state:",
            lean.parser.run $ do
            get_state >>= λ ps, of_tactic $ do 
            {
                
                
                ⟨nm, _⟩ ← interaction_monad.run_with_state' ps $ with_input ident goal_nm_string,
                tsd ← get_tsd_at_decl nm,
                eval_trace format!"Success! Nm: {nm}",
                env ← get_env_at_decl nm,
                eval_trace format!"Success! Nm: {nm}",
                tactic.set_env_core env,
                eval_trace format!"Success! Nm: {nm}",
                rebuild_tactic_state tsd,
                eval_trace format!"Success! Rebuilt",
                
                env ← tactic.get_env,
                do {d ← env.get nm, eval_trace format! "WARNING: GOT DECL"} 
                <|> do {eval_trace format! "NO GOT DECL"},

                -- Want to print goal
                -- gs <- tactic.get_goals,
                -- let goal_strs := gs.map serialize_expr,
                -- eval_trace format! "{goal_strs}",
                -- trace "asdfa",
                trace_state,
                s ← tactic.read, 
                eval_trace format!"State: {s}",
                -- Change goal
                --ps.set_env env,
                --eval_trace format! "Yup",
                goal_pexpr ← interaction_monad.run_with_state' ps $ with_input (lean.parser.pexpr 0 tt) goal_new_string,
                --⟨goal_pexpr, _⟩ ← ps.with_input types.texpr goal_new_string,
                trace goal_pexpr.1,
                --trace get_goals,
                
                --goal_expr ← interaction_monad.run_with_state' ps $ of_tactic (tactic.to_expr goal_pexpr.1),
                --goal_expr ← tactic.to_expr goal_pexpr.1 tt ff,
                --⟨goal_pexpr, s⟩ ← interaction_monad.run_with_state' ps $ with_input types.texpr goal_new_string,
                
                let goal_expr := tactic.unsafe_run_io $ deserialize goal_new_string,
                eval_trace format!"Got expr",
                goal_expr2 ← tactic.to_expr goal_expr tt ff,
                eval_trace format!"Buh",
                --trace goal_expr,
                v <- tactic.mk_meta_var goal_expr2,
                eval_trace format!"mk_meta_var",
                tactic.set_goals $ [v],
                
                --goal_nm ← interaction_monad.run_with_state' ps $ with_input ident goal_nm_string,
                --eval_trace format!"Read goal_pexpr: {go}",
                -- eval_trace ps.cur_pos,
                --set_goal_to <e> goal_pexpr.1,
                
                --set
                --tactic.unsafe_change 
                
                -- print goal again
                trace_state,

                try_get_tac_and_capture_result tactic_string 1000

                -- do {
                --   parse_itactic tactic_string,
                --   eval_trace format!"PARSE SUCCESSFUL: {tactic_string}"
                -- } <|> do {
                --   eval_trace format!"PARSE FAILED: {tactic_string}"
                -- }                

                -- decl ← env.get nm,
                -- eval_trace format!"Success! Nm: {nm}",
                -- let g := decl.type,
                -- set_goal_to g,
                -- lean_file ← env.decl_olean nm,
                -- eval_trace format!"Success! Nm: {lean_file}",
                -- set_env_core $ environment.for_decl_of_imported_module lean_file nm,
                -- read_eval_print_loop ps
            }
        } <|> do {
        eval_trace format!"Failed!"
      }
    },
  
    --for_ args (λ cand, do run_parse cand)
    run_parse goal_nm_string,
}

end main