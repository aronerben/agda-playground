module induction where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- -------------------------------
-- (zero + n) + p ≡ zero + (n + p)
--
-- (m + n) + p ≡ m + (n + p)
-- ---------------------------------
-- (suc m + n) + p ≡ suc m + (n + p)

-- 1)
-- In the beginning, we know nothing.

-- On the first day, we know zero.
-- 0 : ℕ

-- On the second day, we know one and about associativity of 0.
-- 0 : ℕ
-- 1 : ℕ    (0 + 0) + 0 ≡ 0 + (0 + 0)

-- On the third day, we know two and about associativity of 1.
-- 0 : ℕ
-- 1 : ℕ    (0 + 0) + 0 ≡ 0 + (0 + 0)
-- 2 : ℕ    (0 + 1) + 0 ≡ 0 + (1 + 0)    (0 + 1) + 1 ≡ 0 + (1 + 1)    (0 + 0) + 1 ≡ 0 + (0 + 1)    (1 + 0) + 0 ≡ 1 + (0 + 0)

-- On the fourth day, we know two and about associativity of 2.
-- 0 : ℕ
-- 1 : ℕ    (0 + 0) + 0 ≡ 0 + (0 + 0)
-- 2 : ℕ    (0 + 1) + 0 ≡ 0 + (1 + 0)    (0 + 1) + 1 ≡ 0 + (1 + 1)    (0 + 0) + 1 ≡ 0 + (0 + 1)    (1 + 0) + 0 ≡ 1 + (0 + 0)    (1 + 0) + 1 ≡ 1 + (0 + 1)    (1 + 1) + 0 ≡ 1 + (1 + 0)    (1 + 1) + 1 ≡ 1 + (1 + 1)
-- 3 : ℕ    (0 + 2) + 0 ≡ 0 + (2 + 0)    (0 + 2) + 2 ≡ 0 + (2 + 2)    (0 + 0) + 2 ≡ 0 + (0 + 2)    (0 + 2) + 1 ≡ 0 + (2 + 1)    (0 + 1) + 2 ≡ 0 + (1 + 2)    (2 + 0) + 0 ≡ 2 + (0 + 0)    (2 + 1) + 0 ≡ 2 + (1 + 0)    (2 + 2) + 0 ≡ 2 + (2 + 0)    (2 + 0) + 1 ≡ 2 + (0 + 1)    (2 + 0) + 2 ≡ 2 + (0 + 2)    (2 + 1) + 1 ≡ 2 + (1 + 1)    (2 + 1) + 2 ≡ 2 + (1 + 2)    (2 + 2) + 1 ≡ 2 + (2 + 1)    (2 + 2) + 2 ≡ 2 + (2 + 2)


-- 2)
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎

-- +-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
-- +-swap m n p rewrite sym (+-assoc m n p)
--                 | cong (_+ p) (+-comm m n)
--                 | +-assoc n m p
--                 = refl

-- 3)
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p =
  begin
    (zero + n) * p
  ≡⟨⟩
    n * p
  ≡⟨⟩
    zero * p + n * p
  ∎
*-distrib-+ (suc m) n p =
  begin
    ((suc m) + n) * p
  ≡⟨⟩
    suc (m + n) * p
  ≡⟨⟩
    p + ((m + n) * p)
  ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p))⟩
    (p + m * p) + n * p
  ≡⟨⟩
    (suc m) * p + n * p
  ∎

-- 4)
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p =
  begin
    (zero * n) * p
  ≡⟨⟩
    zero * p
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero * n
  ≡⟨⟩
    zero * (n * p)
  ∎
*-assoc (suc m) n p =
  begin
    (suc m * n) * p
  ≡⟨⟩
    (n + m * n) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    (n * p) + (m * n) * p
  ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    (n * p) + m * (n * p)
  ≡⟨⟩
    suc m * (n * p)
  ∎

-- 5)
+-absorbingʳ : ∀ (m : ℕ) → m * zero ≡ zero
+-absorbingʳ zero =
  begin
    zero * zero
  ≡⟨⟩
    zero
  ∎
+-absorbingʳ (suc m) =
  begin
    suc m * zero
  ≡⟨⟩
    zero + m * zero
  ≡⟨ cong (zero +_) (+-absorbingʳ m) ⟩
    zero + zero
  ≡⟨⟩
    zero
  ∎

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n =
  begin
    zero * (suc n)
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero * n
  ≡⟨⟩
    zero + zero * n
  ∎
*-suc (suc m) n =
  begin
    suc m * suc n
  ≡⟨⟩
    (suc n) + (m * suc n)
  ≡⟨ cong ((suc n) +_) (*-suc m n) ⟩
    (suc n) + (m + m * n)
  ≡⟨⟩
    suc (n + (m + m * n))
  ≡⟨ cong suc (sym (+-assoc n m (m * n))) ⟩
    suc ((n + m) + m * n)
  ≡⟨ cong (λ {x → suc (x + m * n)}) (+-comm n m) ⟩
    suc ((m + n) + m * n)
  ≡⟨ cong suc (+-assoc m n (m * n)) ⟩
    suc (m + (n + m * n))
  ≡⟨⟩
    suc (m + (suc m * n))
  ≡⟨⟩
    suc m + suc m * n
  ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero =
  begin
    m * zero
  ≡⟨ +-absorbingʳ m ⟩
    zero
  ≡⟨⟩
    zero * m
  ∎
*-comm m (suc n) =
  begin
    m * suc n
  ≡⟨ *-suc m n ⟩
    m + m * n
  ≡⟨ cong (m +_) (*-comm m n) ⟩
    m + n * m
  ≡⟨⟩
    suc n * m
  ∎
