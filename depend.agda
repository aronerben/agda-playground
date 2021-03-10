module depend where

open import Relation.Binary.PropositionalEquality

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

record CommutativeSemigroup (a : Set) : Set where
  field
    _⊛_ : a → a → a
    associative : ∀ a b c → (a ⊛ b) ⊛ c ≡ a ⊛ (b ⊛ c)
    commutative : ∀ a b → a ⊛ b ≡ b ⊛ a

plusAssociative : ∀ a b c -> (a + b) + c ≡ a + (b + c)
plusAssociative zero b c = refl
plusAssociative (suc a) b c = cong suc (plusAssociative a b c)

plusCommutativeAux : ∀ a b -> a + suc b ≡ suc (a + b)
plusCommutativeAux zero b = refl
plusCommutativeAux (suc a) b = cong suc (plusCommutativeAux a b)

plusCommutative : ∀ a b -> a + b ≡ b + a
plusCommutative zero zero = refl
plusCommutative (suc a) zero = cong suc (plusCommutative a zero)
plusCommutative zero (suc b) = cong suc (plusCommutative zero b)
plusCommutative (suc a) (suc b) rewrite plusCommutativeAux a b | plusCommutativeAux b a = cong suc (cong suc (plusCommutative a b))

plusSemigroup : CommutativeSemigroup ℕ
plusSemigroup = record
  { _⊛_ = _+_
  ; associative = plusAssociative
  ; commutative = plusCommutative
  }
