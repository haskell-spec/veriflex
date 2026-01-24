import Veriflex.RegExp
/-!
# Rules and Grammar

This file describes the rules which make up the grammar of the lexer.
Each rule consists of a regular expression and a semantic action, i.e.
a function which takes the lexed string and transforms it into a token.
-/

namespace Veriflex

structure Rule (tok : Type): Type where
  re : RE
  action : String → tok

abbrev Grammar (tok : Type) : Type := List (Rule tok)

/-- `p` is a prefix of `z` -/
def Prefix (p z : List Char) : Prop :=
  ∃ s, p ++ s = z

/-- `p` is the longest prefix of `z` matching a rule in the grammar `G` -/
def MaxPref {tok : Type}
            (G : Grammar tok)
            (p z : List Char)
            : Prop :=
  /- `p` is a prefix of  `z`-/
  Prefix p z ∧
  /- `p` matches against a rule in `G`-/
  (∃ r ∈ G, Matching r.re p) ∧
  /- All longer prefixes don't match -/
  (∀ p', Prefix p' z ∧ p.length < p'.length →
         ∀ r' ∈ G, ¬ (Matching r'.re p'))

inductive Index {α : Type } : Nat → α → List α → Prop where
  | ZERO : Index Nat.zero x (x :: xs)
  | SUCC : Index n x xs → Index (Nat.succ n) x (y :: xs)

def FirstToken {tok : Type}
               (G : Grammar tok)
               (t : tok)
               (pre z : List Char)
               : Prop :=
  /- `pre` must not be empty -/
  pre ≠ [] ∧
  /- `pre` must be a maximal prefix of `z` matching a rule in `G` -/
  MaxPref G pre z ∧
  /- There is a rule `r` in `G` which matches `pre` and produces token `tok` -/
  (∃ n r, Index n r G ∧
          Matching r.re pre ∧
          r.action pre.toString = t ∧
          /- All other rules which occur earlier in `G` do not match -/
          (∀ r' n', n' < n → Index n' r' G → ¬ Matching r'.re pre))


inductive Tokens {tok : Type} (G : Grammar tok) : List Token →  List Char → List Char → Prop where
  | NIL :
    Tokens G [] xs xs
  | CONS :
    z = pre ++ s →
    FirstToken G t pre z →
    Tokens G  toks u s →
    Tokens G (tok :: toks) u (z ++ ps)

end Veriflex
