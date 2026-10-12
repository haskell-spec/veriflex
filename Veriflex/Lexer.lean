import Veriflex.Grammar
import Veriflex.Brzozowski
import Veriflex.Utils
import Veriflex.MaxPrefix
import Veriflex.Located

/-!
# Lexer

This file implements the function `lex` which takes a grammar and lexes a string.
-/
namespace Veriflex

def apply_rule  {tok : Type} :
  Rule tok × Option (List LChar × List LChar) →
  Option (tok × List LChar × List LChar) := λ ⟨rule,x ⟩ =>
  match x with
  | none => none
  | some ⟨pre, rest⟩ => some ⟨rule.action (String.ofList (contents pre)), pre, rest⟩

def max_pref {tok : Type}
             (input : List LChar)
             (G : Grammar tok)
             : Option (tok × List LChar × List LChar) :=
  let max_prefixes : List (Rule tok × Option (List LChar × List LChar)) := G.map (λ rule => ⟨rule, max_pref_one rule.re input⟩)
  let max_prefixes : List (Option (tok × List LChar × List LChar)) := max_prefixes.map apply_rule
  let max_prefixes : List (tok × List LChar × List LChar) := max_prefixes.filterMap id
  let result : Option (tok × List LChar × List LChar):= find_first_max max_prefixes (λ x => x.2.1.length)
  result

theorem max_pref_length :
  max_pref input rules = some ⟨tok,pre,rest⟩ →
  input.length = pre.length + rest.length := by
  unfold max_pref
  simp!
  generalize H_eq : List.filterMap (apply_rule ∘ fun rule => (rule, max_pref_one rule.re input)) rules = xs
  have H_forall : ∀ x ∈ xs, input.length = x.snd.fst.length + x.snd.snd.length := by
    intros x H_in
    rw [←H_eq] at H_in
    let ⟨tok,n,rest⟩ := x
    simp!
    clear H_eq
    have X := List.mem_filterMap.mp H_in
    let ⟨rule,_,X⟩ := X
    simp! at X
    generalize H_eq : max_pref_one rule.re input = res at X
    cases res with
    | none => simp! at X
    | some val =>
      let ⟨pre,rest'⟩ := val
      simp! at X
      have Y := max_pref_one_prefix H_eq
      let ⟨_,X₁,X₂⟩ := X
      rw [←X₁, ←Y, X₂]
      rw [List.length_append]
  intros H
  have H_in := find_first_max_contained H
  specialize H_forall ⟨ tok,pre ,rest⟩ H_in
  assumption

def first_token {tok : Type}
                (G : Grammar tok)
                (input : List LChar)
                : Option (Located tok × List LChar) :=
  match max_pref input G with
  | none => none
  | some ⟨tok,pre,rest⟩ =>
    match pre with
    | List.nil => none
    | List.cons x _ => some ⟨Located.mk x.location tok, rest⟩



theorem first_token_smaller :
  first_token rules input = some ⟨tok, rest⟩ →
  rest.length < input.length := by
  unfold first_token
  generalize H_eq : max_pref input rules = res
  intros H
  cases res with
  | none =>
    simp! at H
  | some v =>
    let ⟨token,n,rest'⟩ := v
    simp! at H
    have X : input.length = n.length + rest'.length := by
      apply max_pref_length
      apply H_eq
    clear H_eq
    cases n with
    | nil => simp! at H
    | cons hd tl =>
      simp! at H
      let ⟨H₁,H₂⟩ := H
      simp! at X
      rw [H₂] at X
      omega

def measure {tok a : Type}(x : Option (tok × List a)) : Nat :=
  match x with
  | none => 0
  | some ⟨ _, xs ⟩ => xs.length + 1

def lex_rec {tok : Type}
            (G : Grammar tok)
            (input : List LChar)
            (next: Option (Located tok × List LChar))
            : List (Located tok) × List LChar :=
  match next with
  | none => ([], input)
  | some (tok, rest) =>
    let (toks, rest') :=
      lex_rec G rest (first_token G rest)
    (tok :: toks, rest')
termination_by measure next
decreasing_by
  simp!
  generalize H : first_token G rest = x
  cases x with
  | none =>
    simp!
  | some x =>
    let ⟨_, x ⟩ := x
    simp!
    exact (first_token_smaller H)

def lex {tok : Type}
        (G : Grammar tok)
        (input : List LChar)
        : List (Located tok) × List LChar :=
  lex_rec G input (first_token G input)

end Veriflex
