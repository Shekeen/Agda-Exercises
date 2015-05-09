module Functions.Dependent where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)


fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero = zero
fromℕ (suc n) = suc (fromℕ n)

_-_ : (n : ℕ) → Fin (suc n) → ℕ
zero - _ = zero
n - zero = n
(suc n) - (suc f) = n - f

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero = zero
toℕ (suc f) = suc (toℕ f)

fromℕ≤ : ∀ {m n} → m < n → Fin n
fromℕ≤ (s≤s z≤n) = zero
fromℕ≤ (s≤s (s≤s f)) = suc (fromℕ≤ (s≤s f))

inject+ : ∀ {m} n → Fin m → Fin (m + n)
inject+ n zero = zero
inject+ n (suc f) = suc (inject+ n f)

four : Fin 66
four = suc (suc (suc (suc zero)))

raise : ∀ {m} n → Fin m → Fin (n + m)
raise zero f = f
raise (suc n) f = suc (raise n f)

head : ∀ {n}{A : Set} → Vec A (suc n) → A
head (x ∷ _) = x

tail : ∀ {n}{A : Set} → Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs

_++_ : ∀ {n m}{A : Set} → Vec A n → Vec A m → Vec A (n + m)
[] ++ v = v
(x ∷ xs) ++ v = x ∷ (xs ++ v)

maps : ∀ {n}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
maps [] [] = []
maps (f ∷ fs) (x ∷ xs) = (f x) ∷ (maps fs xs)

replicate : ∀ {n}{A : Set} → A → Vec A n
replicate {n = zero} _ = []
replicate {n = suc n} x = x ∷ replicate x

map : ∀ {n}{A B : Set} → (A → B) → Vec A n → Vec B n
map f xs = maps (replicate f) xs

zipWith : ∀ {n}{A B : Set} → (A → B → A × B) → Vec A n → Vec B n → Vec (A × B) n
zipWith f xs ys = maps (map f xs) ys

zip : ∀ {n}{A B : Set} → Vec A n → Vec B n → Vec (A × B) n
zip = zipWith _,_

_!_ : ∀ {n}{A : Set} → Vec A n → Fin n → A
v ! zero = head v
v ! (suc f) = (tail v) ! f
