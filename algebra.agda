module algebra where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Goals are written as normalised

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

record Semigroup (a : Set) : Set where
  field
    _⊛_ : a → a → a
    assoc : ∀ a b c → (a ⊛ b) ⊛ c ≡ a ⊛ (b ⊛ c)

record Monoid (a : Set) : Set where
  field
    semigroup : Semigroup a
  open Semigroup semigroup
  field
    e : a
    idl : ∀ a → e ⊛ a ≡ a
    idr : ∀ a → a ⊛ e ≡ a

record Group (a : Set) : Set where
  field
    monoid : Monoid a
  open Monoid monoid
  open Semigroup semigroup
  field
  -- TODO [aerben] fix this
    invl : ∀ a ∃ b → a ⊛ b ≡ e
    invr : ∀ a ∃ b → b ⊛ a ≡ e

record AbelianGroup (a : Set) : Set where
  field
    group : Group a
  open Group group
  open Monoid monoid
  open Semigroup semigroup
  field
    commutative : ∀ a b → a ⊛ b ≡ b ⊛ a

record CommutativeSemigroup (a : Set) : Set where
  field
    _⊛_ : a → a → a
    associative : ∀ a b c → (a ⊛ b) ⊛ c ≡ a ⊛ (b ⊛ c)
    commutative : ∀ a b → a ⊛ b ≡ b ⊛ a

plusAssociative : ∀ a b c -> (a + b) + c ≡ a + (b + c)
-- Goal: (b + c) ≡ (b + c)
-- Follows from reflexivity
plusAssociative zero b c = refl
-- Goal: suc ((a + b) + c) ≡ suc (a + (b + c))
-- Inductive step
-- Follows from induction assumption and congruence
plusAssociative (suc a) b c =
  begin
    suc ((a + b) + c)
  ≡⟨ cong suc (plusAssociative a b c) ⟩
    suc (a + (b + c))
  ∎

plusCommutativeLemma : ∀ a b -> a + suc b ≡ suc (a + b)
-- Goal: suc b ≡ suc b
-- Follows from reflexivity
plusCommutativeLemma zero b = refl
-- Goal: suc (a + suc b) ≡ suc (suc (a + b))
-- Inductive step
-- Follows from induction assumption and congruence
plusCommutativeLemma (suc a) b =
  begin
    suc (a + suc b)
  ≡⟨ cong suc (plusCommutativeLemma a b) ⟩
    suc (suc (a + b))
  ∎

plusCommutative : ∀ a b -> a + b ≡ b + a
-- Goal: zero ≡ zero
-- Follows from reflexivity
plusCommutative zero zero = refl
-- Goal: suc (a + zero) ≡ suc a
-- One-sided inductive step
-- Follows from induction assumption and congruence
plusCommutative (suc a) zero =
  begin
    suc (a + zero)
  ≡⟨ cong suc (plusCommutative a zero) ⟩
    suc a
  ∎
-- Goal: suc b ≡ suc (b + zero)
-- One-sided inductive step
-- Follows from induction assumption and congruence
plusCommutative zero (suc b) =
  begin
    suc b
  ≡⟨ cong suc (plusCommutative zero b) ⟩
    suc (b + zero)
  ∎
-- plusCommutative (suc a) (suc b) rewrite plusCommutativeAux a b | plusCommutativeAux b a = cong suc (cong suc (plusCommutative a b))
-- Goal: suc (a + suc b) ≡ suc (b + suc a)
plusCommutative (suc a) (suc b) =
  begin
    suc (a + suc b)
  ≡⟨ cong suc (plusCommutativeLemma a b) ⟩
    suc (suc (a + b))
  ≡⟨ cong suc (cong suc (plusCommutative a b)) ⟩
    suc (suc (b + a))
    -- Need to invoke symmetry since definitional equivalence does not guarantee it
  ≡⟨ cong suc (sym (plusCommutativeLemma b a)) ⟩
    suc (b + suc a)
  ∎

plusSemigroup : CommutativeSemigroup ℕ
plusSemigroup = record
  { _⊛_ = _+_
  ; associative = plusAssociative
  ; commutative = plusCommutative
  }
