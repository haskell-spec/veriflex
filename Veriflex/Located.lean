/-!
# Located

This file defines a structure `Located` that is used to track source code locations of
characters and tokens, as well as utility functions.
-/
namespace Veriflex

abbrev Location : Type := Nat

structure Located (a : Type) : Type where
  location : Location
  content : a
  deriving BEq, Repr

abbrev LChar : Type := Located Char

/-- Forget the locations and return the -/
def contents {a : Type} (xs : List (Located a)) : List a :=
  xs.map (λ x => x.content)

/-- Returns the location of the first item in the list, if it exists. -/
def first_loc {a : Type} (xs : List (Located a)) : Option Location :=
  match xs with
  | List.nil => none
  | List.cons x _ => some x.location

end Veriflex
