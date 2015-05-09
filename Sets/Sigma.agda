module Sets.Sigma where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Function using (_$_; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Empty using (⊥)

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → (b : B a) → Σ A B

infixr 4 _,_


Fin′ : ℕ → Set
Fin′ n = Σ ℕ (λ x → x < n)

--toFin : ∀ {n} → Fin′ n → Fin n
--toFin (Fin′ zero) = zero
--toFin (Fin′ (suc n)) = suc (toFin (Fin′ n))


data _∈_ {A : Set}(x : A) : List A → Set where
  first : {xs : List A} → x ∈ x ∷ xs
  later : {y : A}{xs : List A} → x ∈ xs → x ∈ y ∷ xs

infix 4 _∈_

_!_ : ∀ {A : Set} → List A → ℕ → Maybe A
[] ! _ = nothing
x ∷ xs ! zero = just x
x ∷ xs ! (suc n) = xs ! n

infix 5 _!_

lookup : ∀ {A}{x : A}(xs : List A) → x ∈ xs → Σ ℕ (λ n → xs ! n ≡ just x)
lookup = {!!}
