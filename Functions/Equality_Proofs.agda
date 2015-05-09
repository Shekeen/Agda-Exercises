module Functions.Equality_Proofs where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Function using (_$_) 


data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

refl′ : ∀ {A}(a : A) → a ≡ a
refl′ a = refl

sym : ∀ {A}{a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : ∀ {A}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : ∀ {A B}{m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
cong f refl = refl

+-right-identity : ∀ {n} → n + 0 ≡ n
+-right-identity {n = zero} = refl
+-right-identity {n = suc n} = cong suc +-right-identity

+-left-identity : ∀ {n} → 0 + n ≡ n
+-left-identity = refl

+-assoc : ∀ {a b c} → a + (b + c) ≡ (a + b) + c
+-assoc {a = zero} = refl
+-assoc {a = suc a}{b}{c} = cong suc $ +-assoc {a}{b}{c}

m+1+n≡1+m+n : ∀ {m n} → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n {m = zero} = refl
m+1+n≡1+m+n {m = suc m}{n} = cong suc $ m+1+n≡1+m+n {m}{n}


fromList : List ⊤ → ℕ
fromList [] = zero
fromList (x ∷ xs) = suc $ fromList xs

toList : ℕ → List ⊤
toList zero = []
toList (suc n) = tt ∷ toList n

from-to : ∀ {a} → fromList (toList a) ≡ a
from-to {a = zero} = refl
from-to {a = suc a} = cong suc from-to

to-from : ∀ {a} → toList (fromList a) ≡ a
to-from {a = []} = refl
to-from {a = a′ ∷ a} = cong (_∷_ a′) $ to-from

fromPreserves++ : ∀ {a b} → fromList (a ++ b) ≡ fromList a + fromList b
fromPreserves++ {a = []} = refl
fromPreserves++ {a = _ ∷ a}{b} = cong suc $ fromPreserves++ {a}{b}

toPreserves+ : ∀ {a b} → toList (a + b) ≡ toList a ++ toList b
toPreserves+ {a = zero} = refl
toPreserves+ {a = suc a}{b} = cong (_∷_ tt) $ toPreserves+ {a}{b}


_≡[_]_ : ∀ {A : Set}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡[ refl ] refl = refl

infixr 2 _≡[_]_

_◾ : ∀ {A : Set}(x : A) → x ≡ x
x ◾ = refl

infix 2 _◾

+-comm′ : (n m : ℕ) → n + m ≡ m + n
+-comm′ zero n = sym (+-right-identity {n})
+-comm′ (suc m) n =
    suc m + n
  ≡[ refl ]
    suc (m + n)
  ≡[ cong suc (+-comm′ m n) ]
    suc (n + m)
  ≡[ sym (m+1+n≡1+m+n {n}{m}) ]
    n + suc m
  ◾


distribʳ-*-+ : ∀ a b c → (a + b) * c ≡ a * c + b * c
distribʳ-*-+ zero b c = refl
distribʳ-*-+ (suc a) b c =
    c + (a + b) * c
  ≡[ cong (λ x → c + x) (distribʳ-*-+ a b c) ]
    c + (a * c + b * c)
  ≡[ +-assoc {c}{a * c}{b * c} ]
    c + a * c + b * c
  ◾

*-left-identity : ∀ a -> 1 * a ≡ a
*-left-identity zero = refl
*-left-identity (suc a) = cong suc $ *-left-identity a

*-right-identity : ∀ a → a * 1 ≡ a
*-right-identity zero = refl
*-right-identity (suc a) = cong suc $ *-right-identity a

*-assoc : ∀ a b c → a * (b * c) ≡ (a * b) * c
*-assoc zero b c = refl
*-assoc (suc a) b c =
    b * c + a * (b * c)
  ≡[ cong (λ x → b * c + x) $ *-assoc a b c ]
    b * c + (a * b) * c
  ≡[ sym $ distribʳ-*-+ b (a * b) c ]
    (b + a * b) * c
  ≡[ cong (λ x → (x + a * b) * c) $ sym $ *-left-identity b ]
    (1 * b + a * b) * c
  ≡[ cong (λ x → x * c) $ sym $ distribʳ-*-+ 1 a b ]
    (1 + a) * b * c
  ◾

n*0≡0 : ∀ n → n * 0 ≡ 0
n*0≡0 zero = refl
n*0≡0 (suc n) = cong (_+_ 0) $ n*0≡0 n

*-suc : ∀ n m → n + n * m ≡ n * suc m
*-suc zero _ = refl
*-suc (suc n) m = 
    1 + n + (m + n * m)
  ≡[ +-assoc {1 + n}{m}{n * m} ]
    1 + n + m + n * m
  ≡[ cong (λ x → x + n * m) $ sym $ +-assoc {1}{n}{m} ]
    1 + (n + m) + n * m
  ≡[ cong (λ x → 1 + x + n * m) $ +-comm′ n m ]
    1 + (m + n) + n * m
  ≡[ cong (λ x → x + n * m) $ +-assoc {1}{m}{n} ]
    (1 + m + n) + n * m
  ≡[ sym $ +-assoc {1 + m}{n}{n * m} ]
    1 + m + (n + n * m)
  ≡[ cong (λ x → suc m + x) $ *-suc n m ]
    suc m + n * suc m
  ≡[ cong (λ x → x + n * suc m) $ sym $ *-left-identity $ suc m ]
    1 * suc m + n * suc m
  ≡[ sym $ distribʳ-*-+ 1 n (suc m) ]
    suc n * suc m
  ◾

*-comm : ∀ m n → m * n ≡ n * m
*-comm zero n = sym $ n*0≡0 n
*-comm (suc m) n =
    n + m * n
  ≡[ cong (λ x → n + x) $ *-comm m n ]
    n + n * m
  ≡[ *-suc n m ]
    n * (suc m)
  ◾

