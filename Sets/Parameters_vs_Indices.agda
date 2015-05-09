module Sets.Parameters_vs_Indices where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)


data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_


data _∈_ {A : Set}(x : A) : List A → Set where
  first : ∀ {xs} → x ∈ x ∷ xs
  later : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

infix 4 _∈_


data _⊆_ {A : Set} : List A → List A → Set where
  first : ∀ {x xs} → (x ∷ []) ⊆ (x ∷ xs)
  later : ∀ {xs y ys} → xs ⊆ ys → xs ⊆ (y ∷ ys)
  cons : ∀ {x xs ys} → (x ∷ []) ⊆ ys → xs ⊆ ys → (x ∷ xs) ⊆ ys
