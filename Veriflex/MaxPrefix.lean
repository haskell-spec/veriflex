import Veriflex.Grammar
import Veriflex.Brzozowski
import Veriflex.Located

/-!
# MaxPrefix
-/

namespace Veriflex

structure State : Type where
  initial : RE
  re : RE
  left : List LChar
  right : List LChar
  best : Option (List LChar × List LChar)

def initial_state (s : List LChar) (re: RE) : State :=
  State.mk re re [] s none

def max_pref_one_step
  (state: State) : Option State :=
  match state.right with
  | [] => none
  | s :: right' =>
    let re' := derivative s.content state.re
    let left' := state.left ++ [s]
    if nullable re'
    then some (State.mk state.initial re' left' right' (some (left', right')))
    else some (State.mk state.initial re' left' right' state.best)

partial def max_pref_one_rec (s : State) : State :=
  match max_pref_one_step s with
  | none => s
  | some s' => max_pref_one_rec s'

/--
Given an input string and a rule, compute the longest prefix of the input that matches this rule.
If the regular expression matches successfully, return the computed token,
the length of the consumed input, and the remainder of the output.
-/
def max_pref_one (re : RE) (s : List LChar) : Option (List LChar × List LChar) :=
  (max_pref_one_rec (initial_state s re)).best



/--
Proving invariants
-/

def invariant_strings (state : State) : Prop :=
  match state.best with
  | none => true
  | some (left', right') => left' ++ right' = state.left ++ state.right

theorem preserves_invariant_strings :
  ∀ s, invariant_strings s →
       max_pref_one_step s = some s' →
       invariant_strings s' := sorry

theorem max_pref_one_prefix :
  max_pref_one rule input = some ⟨pre, rest⟩ →
  pre ++ rest = input := sorry
