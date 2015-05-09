module sample where

data Bool : Set where
  true false : Bool

data Answer : Set where
  yes no maybe : Answer

data Quarter : Set where
  north south west east : Quarter


data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m : ℕ} → {n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_


data ℕ⁺ : Set where
  one : ℕ⁺
  double double+1 : ℕ⁺ → ℕ⁺

data ℕ₂ : Set where
  zero : ℕ₂
  id : ℕ⁺ → ℕ₂

nine : ℕ₂
nine = id (double+1 (double (double one)))

data ℤ : Set where
  zero : ℤ
  pos neg : ℕ⁺ → ℤ


data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

data BinTreeLeafℕ : Set where
  leaf : ℕ → BinTreeLeafℕ
  node : BinTreeLeafℕ → BinTreeLeafℕ → BinTreeLeafℕ

data BinTreeNodeℕ : Set where
  leaf : BinTreeNodeℕ
  node : ℕ → BinTreeNodeℕ → BinTreeNodeℕ → BinTreeNodeℕ

data BinTreeBoolℕ : Set where
  leaf : ℕ → BinTreeBoolℕ
  node : Bool → BinTreeBoolℕ → BinTreeBoolℕ → BinTreeBoolℕ

data Listℕ : Set where
  empty : Listℕ
  cons : ℕ → Listℕ → Listℕ
