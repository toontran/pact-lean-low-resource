import data.nat.basic
import system.io
import tactic.core
import tactic

import utils
import .tactic_state
import basic.queue


section run_with_state'

namespace interaction_monad
open interaction_monad.result

/-- Reconfigure run_with_state: 
https://github.com/leanprover-community/mathlib/blob/0420dd88ddad1db7840cf1b68f72211ba0818a50/src/tactic/core.lean#L157
Simply add requirement `{σ₁ σ₂ : Type} {α : Type*}`
-/
meta def run_with_state' {σ₁ σ₂ : Type} {α : Type*} (state : σ₁) (tac : interaction_monad σ₁ α) : interaction_monad σ₂ α :=
λ s, match (tac state) with
     | (success val _) := success val s
     | (exception fn pos _) := exception fn pos s
     end
end interaction_monad
end run_with_state'


section parse_tac

setup_tactic_parser

open tactic

/-- Parse a reflected interactive tactic from a string.
    There will be results if the tactic can be parsed.
    Else throws an error (need to be catched). -/
meta def parse_itactic_reflected (tactic_string : string) : tactic expr :=
let itactic_string := "{ " ++ tactic_string ++  " }" in
lean.parser.run $ do
  get_state >>= λ ps, of_tactic $ do
    tactic.set_env ps.env,
    --eval_trace format!"[parse_itactic_reflected] TRYING TO PARSE {itactic_string}",
    (reflected_value.expr ∘ prod.fst) <$>
      (@interaction_monad.run_with_state' parser_state _ _ ps $
         with_input parser.itactic_reflected itactic_string)

meta def parse_itactic (tactic_string : string) : tactic expr := parse_itactic_reflected tactic_string

end parse_tac


section main

/-- Takes in unlimited number of tactics
    and try to parse them. -/
meta def main : io unit := do {
  args ← io.cmdline_args,
      
  for_ args (λ cand, do io.put_str_ln' format!"candidates: {cand}"),
  
  let run_parse : string → io unit := λ cand, do {
      io.run_tactic' $ do 
      {
        parse_itactic cand,
        eval_trace format!"PARSE SUCCESSFUL: {cand}"
      } <|> do {
        eval_trace format!"PARSE FAILED: {cand}"
      }
  },
  
  for_ args (λ cand, do run_parse cand)
}

end main
