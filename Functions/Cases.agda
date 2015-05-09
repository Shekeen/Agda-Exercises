module Functions.Cases where

open import Sets.Enumerated using (Bool; true; false)


not : Bool → Bool
not true = false
not false = true


_∧_ : Bool → Bool → Bool
true ∧ x = x
false ∧ _ = false

infixr 6 _∧_

_∨_ : Bool → Bool → Bool
true ∨ _ = true
false ∨ x = x

infixr 5 _∨_

