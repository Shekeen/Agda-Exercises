module Sets.Propositions where

open import Data.Nat using (ℕ; zero; suc)

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

data _⊎_ (A B : Set) : Set where
  inj₁ : A -> A ⊎ B
  inj₂ : B -> A ⊎ B

infixr 1 _⊎_


⊤×⊤ : ⊤ × ⊤
⊤×⊤ = tt , tt

⊤⊎⊤ : ⊤ ⊎ ⊤
⊤⊎⊤ = inj₁ tt

⊤⊎⊥ : ⊤ ⊎ ⊥
⊤⊎⊥ = inj₁ tt

⊥⊎⊤ : ⊥ ⊎ ⊤
⊥⊎⊤ = inj₂ tt

--⊥⊎⊤⊎⊤×(⊥⊎⊥)⊎⊤ : ⊥ ⊎ ⊤ ⊎ ⊤ × (⊥ ⊎ ⊥) ⊎ ⊤
--⊥⊎⊤⊎⊤×(⊥⊎⊥)⊎⊤ = inj₂ tt


data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m : ℕ} → {n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_


0≤1 : 0 ≤ 1
0≤1 = z≤n

1≤10 : 1 ≤ 10
1≤10 = s≤s z≤n

3≤7 : 3 ≤ 7
3≤7 = s≤s (s≤s (s≤s z≤n))

7≰3 : 7 ≤ 3 → ⊥
7≰3 (s≤s (s≤s (s≤s ())))

4≰2 : 4 ≤ 2 → ⊥
4≰2 (s≤s (s≤s ()))

8≰4 : 8 ≤ 4 → ⊥
8≰4 (s≤s x) = 7≰3 x

{-
data _isDoubleOf_ : ℕ → ℕ → Set where
  z_isDoubleOf_z : zero isDoubleOf zero
  m_isDoubleOf_n : {m : ℕ} → {n : ℕ} → m isDoubleOf n → suc (suc m) isDoubleOf suc n

infix 1 _isDoubleOf_

8isDoubleOf4 : 8 isDoubleOf 4
8isDoubleOf4 = m_isDoubleOf_n (m_isDoubleOf_n (m_isDoubleOf_n (m_isDoubleOf_n z_isDoubleOf_z)))

9isNotDoubleOf4 : 9 isDoubleOf 4 → ⊥
9isNotDoubleOf4 (m_isDoubleOf_n (m_isDoubleOf_n (m_isDoubleOf_n (m_isDoubleOf_n ()))))
-}

data Even : ℕ → Set
data Odd : ℕ → Set

data Even where
  zero_even : Even zero
  rest_even : {n : ℕ} -> Odd n -> Even (suc n)

data Odd where
  rest_odd : {n : ℕ} → Even n → Odd (suc n)

odd3 : Odd 3
odd3 = rest_odd (rest_even (rest_odd zero_even))

even4 : Even 4
even4 = rest_even odd3

noteven3 : Even 3 → ⊥
noteven3 (rest_even (rest_odd (rest_even ())))


data _≡_ : ℕ → ℕ → Set where
  z≡z : zero ≡ zero
  s≡s : ∀ {n} → n ≡ n → suc n ≡ suc n

data _≠_ : ℕ → ℕ → Set where
  z≠s : ∀ {n} → zero ≠ suc n
  s≠s : ∀ {m n} → m ≠ n → suc m ≠ suc n

2≡2 : 2 ≡ 2
2≡2 = s≡s (s≡s z≡z)


data _+_≡_ : ℕ → ℕ → ℕ → Set where
  z+n≡n : ∀ {n} → zero + n ≡ n
  s+n≡s : ∀ {m n k} → m + n ≡ k → suc m + n ≡ suc k

5+5≡10 : 5 + 5 ≡ 10
5+5≡10 = s+n≡s (s+n≡s (s+n≡s (s+n≡s (s+n≡s z+n≡n))))

2+2≠5 : 2 + 2 ≡ 5 → ⊥
2+2≠5 (s+n≡s (s+n≡s ()))


data _⊓_≡_ : ℕ → ℕ → ℕ → Set where
  n⊓z≡z : ∀ {n} → n ⊓ zero ≡ zero
  z⊓n≡z : ∀ {n} → zero ⊓ n ≡ zero
  s⊓s≡s₁ : ∀ {m n} → m ⊓ n ≡ m → suc m ⊓ suc n ≡ suc m
  s⊓s≡s₂ : ∀ {m n} → m ⊓ n ≡ n → suc m ⊓ suc n ≡ suc n

3⊓5≡3 : 3 ⊓ 5 ≡ 3
3⊓5≡3 = s⊓s≡s₁ (s⊓s≡s₁ (s⊓s≡s₁ z⊓n≡z))

3⊓5≠5 : 3 ⊓ 5 ≡ 5 → ⊥
3⊓5≠5 (s⊓s≡s₂ (s⊓s≡s₂ (s⊓s≡s₂ ())))

3⊓5≠4 : 3 ⊓ 5 ≡ 4 → ⊥
3⊓5≠4 ()


data _⊔_≡_ : ℕ → ℕ → ℕ → Set where
  n⊔z≡n : ∀ {n} → n ⊔ zero ≡ n
  z⊔n≡n : ∀ {n} → zero ⊔ n ≡ n
  s⊔s≡s₁ : ∀ {m n} → m ⊔ n ≡ m → suc m ⊔ suc n ≡ suc m
  s⊔s≡s₂ : ∀ {m n} → m ⊔ n ≡ n → suc m ⊔ suc n ≡ suc n


data _isDoubleOf_ : ℕ → ℕ → Set where
  mDoublen : ∀ {m n} → n + n ≡ m → m isDoubleOf n
infix 1 _isDoubleOf_


data _*_≡_ : ℕ → ℕ → ℕ → Set where
  z*n≡z : ∀ {n} → zero * n ≡ zero
  n*z≡z : ∀ {n} → n * zero ≡ zero
  s*n≡s : ∀ {m n k₁ k₂} → k₁ + n ≡ k₂ → m * n ≡ k₁ → suc m * n ≡ k₂
  n*s≡s : ∀ {m n k₁ k₂} → k₁ + m ≡ k₂ → m * n ≡ k₁ → m * suc n ≡ k₂

3+3≡6 : 3 + 3 ≡ 6
3+3≡6 = s+n≡s (s+n≡s (s+n≡s z+n≡n))

6+3≡9 : 6 + 3 ≡ 9
6+3≡9 = s+n≡s (s+n≡s (s+n≡s 3+3≡6))

3*3≡9 : 3 * 3 ≡ 9
3*3≡9 = s*n≡s 6+3≡9 (s*n≡s 3+3≡6 (s*n≡s z+n≡n z*n≡z))


data ℕ₁ : Set where
  one : ℕ₁
  double double+1 : ℕ₁ → ℕ₁

data ℕ⁺ : Set where
  zero : ℕ⁺
  id : ℕ₁ → ℕ⁺


data _≈_ : ℕ → ℕ⁺ → Set where
  z≈z : zero ≈ zero
  o≈o : suc zero ≈ id one
  n≈d : ∀ {m₁ m₂ n} → m₁ + m₁ ≡ m₂ → m₁ ≈ id n → m₂ ≈ id (double n)
  n≈d+1 : ∀ {m n} → m ≈ id (double n) → suc m ≈ id (double+1 n)

1+1≡2 : 1 + 1 ≡ 2
1+1≡2 = s+n≡s z+n≡n

2+2≡4 : 2 + 2 ≡ 4
2+2≡4 = s+n≡s (s+n≡s z+n≡n)

4≈ddo : 4 ≈ id (double (double one))
4≈ddo = n≈d 2+2≡4 (n≈d 1+1≡2 o≈o)
