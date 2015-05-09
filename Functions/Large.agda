module Functions.Large where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)


data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

_≤′_ : ℕ → ℕ → Set
zero ≤′ n = ⊤
suc m ≤′ zero = ⊥
suc m ≤′ suc n = m ≤′ n


_≡_ : ℕ → ℕ → Set
zero ≡ zero = ⊤
zero ≡ suc n = ⊥
suc m ≡ zero = ⊥
suc m ≡ suc n = m ≡ n

_≢_ : ℕ → ℕ → Set
zero ≢ zero = ⊥
zero ≢ suc n = ⊤
suc m ≢ zero = ⊤
suc m ≢ suc n = m ≢ n


even : ℕ → Set
odd : ℕ → Set

even zero = ⊤
even (suc m) = odd m

odd zero = ⊥
odd (suc m) = even m


_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

_>_ : ℕ → ℕ → Set
n > m = suc m ≤ n

_≥_ : ℕ → ℕ → Set
n ≥ m = m ≤ n


¬ : Set → Set
¬ A = A → ⊥
