module Functions.Recursive where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; zero)
open import Sets.Recursive using (ℕ⁺; one; double; double+1; ℕ₂; zero; id)


_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

infixl 6 _+_


pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n


_∸_ : ℕ → ℕ → ℕ
zero ∸ n = n
(suc n) ∸ m = suc (n ∸ m)

infixl 6 _∸_


_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

infixl 7 _*_


_⊔_ : ℕ → ℕ → ℕ
zero ⊔ n = n
m ⊔ zero = m
(suc m) ⊔ (suc n) = m ⊔ n

infixl 6 _⊔_


_⊓_ : ℕ → ℕ → ℕ
zero ⊓ n = zero
m ⊓ zero = zero
(suc m) ⊓ (suc n) = m ⊓ n

infixl 7 _⊓_


⌊_/2⌋ : ℕ → ℕ
⌊ zero /2⌋ = zero
⌊ (suc zero) /2⌋ = zero
⌊ (suc (suc n)) /2⌋ = suc ⌊ n /2⌋


odd : ℕ → Bool
even : ℕ → Bool

odd zero = false
odd (suc n) = even n

even zero = true
even (suc n) = odd n


from : ℕ₂ → ℕ
from zero = zero
from (id one) = suc zero
from (id (double n)) = (from (id n)) * 2
from (id (double+1 n)) = (from (id n)) * 2 + 1


data ℤ : Set where
  zero : ℤ
  pos neg : ℕ⁺ → ℤ


data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree


mirror : BinTree → BinTree
mirror leaf = leaf
mirror (node x y) = node (mirror y) (mirror x)
