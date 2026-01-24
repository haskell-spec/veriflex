import Veriflex.Grammar
import Veriflex.Brzozowski
import Veriflex.Located

/-!
# MaxPrefix
-/

namespace Veriflex

structure State : Type where
  initial_re : RE
  initial_text : List LChar
  re : RE
  left : List LChar
  right : List LChar
  best : Option (List LChar × List LChar)

def initial_state (s : List LChar) (re: RE) : State :=
  State.mk re s re [] s none

def max_pref_one_step
  (state: State) : Option State :=
  match state.right with
  | [] => none
  | s :: right' =>
    let re' := derivative s.content state.re
    let left' := state.left ++ [s]
    if nullable re'
    then some (State.mk state.initial_re state.initial_text re' left' right' (some (left', right')))
    else some (State.mk state.initial_re state.initial_text re' left' right' state.best)


def measure_state (s : Option State) : Nat :=
  match s with
  | none => 0
  | some s => 1 + s.right.length

theorem measure_decrease :
  ∀ s, measure_state (max_pref_one_step s) < measure_state (some s) := by
  intros s
  match H : max_pref_one_step s with
  | none =>
    simp!
    omega
  | some s' =>
    simp!
    unfold max_pref_one_step at H
    match H' : s.right with
    | List.nil =>
      rw [H'] at H <;> simp! at H
    | List.cons hd tl =>
      rw [H'] at H <;> simp! at H
      by_cases H'' : nullable (derivative hd.content s.re)
      . rw [H''] at H <;> simp! at H
        rw [←H] <;> simp!
      . simp! at H'' <;> rw [H''] at H <;> simp! at H
        rw [←H] <;> simp!

def max_pref_one_helper (s : State)(next : Option State) : State :=
  match next with
  | none => s
  | some s' => max_pref_one_helper s' (max_pref_one_step s')
  termination_by measure_state next
  decreasing_by
    apply measure_decrease

def max_pref_one_rec (s : State) : State :=
  max_pref_one_helper s (max_pref_one_step s)

def preserved (P : State → Prop) : Prop :=
  ∀ (s₁ s₂ : State), P s₁ → max_pref_one_step s₁ = some s₂ → P s₂

def fundamental_lemma (P : State → Prop) (H_preserved : preserved P)(s : State):
    P s →
    P (max_pref_one_rec s) := by
    intros H_start
    unfold max_pref_one_rec
    sorry

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
  | none =>
    state.initial_text = state.left ++ state.right
  | some (left', right') =>
    state.initial_text = state.left ++ state.right ∧
    state.initial_text = left' ++ right'


theorem preserved_invariant_strings_step : preserved invariant_strings := by
  intros s s' H_pre H_step
  let ⟨_,initial_text,re,left,right,best⟩ := s
  unfold max_pref_one_step at H_step
  simp! at H_step
  cases right with
  | nil => simp! at H_step
  | cons s right' =>
    simp! at H_step
    by_cases H : (nullable (derivative s.content re) = true)
    . rw [H] at H_step <;> simp! at H_step
      rw [←H_step] <;> clear H_step H
      unfold invariant_strings at * <;> simp! at *
      match best with
      | none => assumption
      | some b =>
        simp! at H_pre
        let ⟨H_pre, _⟩ := H_pre
        assumption
    . simp! at H
      rw [H] at H_step <;> simp! at H_step
      rw [←H_step] <;> clear H_step H
      unfold invariant_strings at * <;> simp! at *
      assumption

theorem preserves_invariant_strings :
  ∀ s, invariant_strings s →
       invariant_strings (max_pref_one_rec s) := by
  intros s H_pre
  apply fundamental_lemma
  . apply preserved_invariant_strings_step
  . assumption


theorem max_pref_one_prefix :
  max_pref_one rule input = some ⟨pre, rest⟩ →
  pre ++ rest = input := by
  intros H
  unfold max_pref_one at H
  have H_pre : invariant_strings (initial_state input rule) := by
    unfold initial_state invariant_strings <;> simp!
  have H_res : invariant_strings (max_pref_one_rec (initial_state input rule)) := by
   apply preserves_invariant_strings
   assumption
  clear H_pre
  unfold invariant_strings at H_res
  rw [H] at H_res <;> simp! at H_res
  let ⟨_,H_res⟩ := H_res
  rw [←H_res]
  sorry
