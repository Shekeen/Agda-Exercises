module Functions.Universal_Quantification where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _≤′_; ≤′-step; ≤′-refl)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (flip; _$_; _∘_)

≤-refl : ∀ {n} → n ≤ n
≤-refl {n = zero} = z≤n
≤-refl {n = suc n} = s≤s ≤-refl

{-
≤-refl : (n : ℕ) → n ≤ n
≤-refl zero = zero
≤-refl (suc n) = s≤s (≤-refl n)
-}

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans z≤n _ = z≤n
≤-trans (s≤s f₁) (s≤s f₂) = s≤s (≤-trans f₁ f₂)

total : ∀ {m n} → m ≤ n ⊎ n ≤ m
total {m = zero} = inj₁ z≤n
total {m = suc m}{n = zero} = inj₂ z≤n
total {m = suc m}{n = suc n} with total
... | inj₁ f₁ = inj₁ (s≤s f₁)
... | inj₂ f₂ = inj₂ (s≤s f₂)

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s f) = f

{-
≤-mono : ∀ {m n k} → n ≤ m → k + n ≤ k + m
≤-mono {k = zero} f = f
≤-mono {k = suc k} f = s≤s (≤-mono f)
-}

≤-next : ∀ {n} -> n ≤ 1 + n
≤-next {n = zero} = z≤n
≤-next {n = suc n} = s≤s ≤-next

≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n
≤-step f = ≤-trans f ≤-next

≤′⇒≤ : ∀ {a b} → a ≤′ b → a ≤ b
≤′⇒≤ ≤′-refl = ≤-refl
≤′⇒≤ (≤′-step f) = ≤-step (≤′⇒≤ f)

z≤′n : ∀ {n} → zero ≤′ n
z≤′n {n = zero} = ≤′-refl
z≤′n {n = suc n} = ≤′-step z≤′n

s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
s≤′s ≤′-refl = ≤′-refl
s≤′s (≤′-step f) = ≤′-step (s≤′s f)

≤⇒≤′ : ∀ {a b} → a ≤ b → a ≤′ b
≤⇒≤′ z≤n = z≤′n
≤⇒≤′ (s≤s f) = s≤′s (≤⇒≤′ f)


fin≤ : ∀ {n}(m : Fin n) → toℕ m < n
fin≤ = {!!}
