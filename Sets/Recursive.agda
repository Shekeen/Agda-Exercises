module Sets.Recursive where

open import Sets.Enumerated using (Bool; true; false)


data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ


data ℕ⁺ : Set where
  one : ℕ⁺
  double double+1 : ℕ⁺ → ℕ⁺

data ℕ₂ : Set where
  zero : ℕ₂
  id : ℕ⁺ → ℕ₂
