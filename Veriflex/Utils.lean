/-!
# Utility functions

This file contains generic utility functions
-/

def find_first_max_rec {α : Type} : Option α → List α → (α → Nat) → Option α := λ best l f =>
  match l with
  | List.nil => best
  | List.cons x xs =>
    match best with
    | none => find_first_max_rec (some x) xs f
    | some b => if f b < f x
                then find_first_max_rec (some x) xs f
                else find_first_max_rec (some b) xs f

def find_first_max {α : Type} : List α → (α → Nat) → Option α := λ l f =>
  find_first_max_rec none l f

theorem find_first_max_empty :
  find_first_max l f = none ↔ l = [] := by
  apply Iff.intro <;> intros H
  . cases l with
    | nil => rfl
    | cons hd tl =>
      unfold find_first_max at H
      simp! at H
      exfalso
      revert hd
      induction tl with
      | nil =>
        intros hd H
        simp! at H
      | cons hd' tl' IH =>
        intros hd H
        simp! at H
        by_cases H_le : f hd < f hd'
        . rw [ite_eq_left H_le] at H
          specialize IH _ H
          exact IH
        . rw [ite_eq_right H_le] at H
          specialize IH _ H
          exact IH
  . rw [H]
    rfl

theorem find_first_max_rec_contained :
  find_first_max_rec (some best) l f = some x →
  x ∈ l ∨ x = best := by
  intros H
  revert best
  induction l with
  | nil =>
    intros best H
    simp! at H
    apply Or.inr
    symm
    assumption
  | cons hd tl IH =>
    intros best H
    simp! at H
    by_cases H_le : f best < f hd
    . rw [ite_eq_left H_le] at H
      specialize IH H
      apply Or.inl
      simp
      cases IH with
      | inl H' => apply Or.inr ; assumption
      | inr H' => apply Or.inl ; assumption
    . rw [ite_eq_right H_le] at H
      specialize IH H
      cases IH with
      | inl H' =>
        apply Or.inl
        simp
        apply Or.inr
        assumption
      | inr H' =>
        apply Or.inr
        assumption

theorem find_first_max_contained :
  find_first_max l f = some x → x ∈ l := by
  intros  H
  unfold find_first_max at H
  cases l with
  | nil => simp! at H
  | cons hd tl =>
    simp! at H
    have H_or : x ∈ tl ∨ x = hd := find_first_max_rec_contained H
    cases H_or with
    | inl H' =>
      simp
      apply Or.inr
      assumption
    | inr H' =>
      simp
      apply Or.inl
      assumption
