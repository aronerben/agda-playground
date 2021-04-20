module induction where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

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
*-absorbingʳ : ∀ (m : ℕ) → m * zero ≡ zero
*-absorbingʳ zero =
  begin
    zero * zero
  ≡⟨⟩
    zero
  ∎
*-absorbingʳ (suc m) =
  begin
    suc m * zero
  ≡⟨⟩
    zero + m * zero
  ≡⟨ cong (zero +_) (*-absorbingʳ m) ⟩
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
  ≡⟨ cong (λ {term → suc (term + m * n)}) (+-comm n m) ⟩
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
  ≡⟨ *-absorbingʳ m ⟩
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

-- 6)
0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero =
  begin
    zero ∸ zero
  ≡⟨⟩
    zero
  ∎
0∸n≡0 (suc n) =
  begin
    zero ∸ suc n
  ≡⟨⟩
    zero
  ∎
-- No induction needed, just prove it holds for 0 and for suc n. (Holds because of definition of ∸)

-- 7)
0∸n≡0∸n+p : ∀ (n p : ℕ) → zero ∸ n ≡ zero ∸ (n + p)
0∸n≡0∸n+p n zero  =
  begin
    zero ∸ n
  ≡⟨ cong (zero ∸_) (sym (+-identityʳ n)) ⟩
    zero ∸ (n + zero)
  ∎
0∸n≡0∸n+p n (suc p)  =
  begin
    zero ∸ n
  ≡⟨ 0∸n≡0 n ⟩
    zero
  ≡⟨⟩
    zero ∸ suc (n + p)
  ≡⟨ cong (zero ∸_) (sym (+-suc n p)) ⟩
    zero ∸ (n + suc p)
  ∎

∸-+-assoc : ∀ (m n p : ℕ) → (m ∸ n) ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p =
  begin
    (zero ∸ n) ∸ p
  ≡⟨ cong (_∸ p) (0∸n≡0 n) ⟩
    zero ∸ p
  ≡⟨ 0∸n≡0 p ⟩
    zero
  ≡⟨ sym (0∸n≡0 n) ⟩
    zero ∸ n
  ≡⟨  0∸n≡0∸n+p n p ⟩
    zero ∸ (n + p)
  ∎
∸-+-assoc (suc m) zero p =
  begin
    (suc m ∸ zero) ∸ p
  ≡⟨⟩
    suc m ∸ (zero + p)
  ∎
∸-+-assoc (suc m) (suc n) p =
  begin
    (suc m ∸ suc n) ∸ p
  ≡⟨⟩
    (m ∸ n) ∸ p
  ≡⟨ ∸-+-assoc m n p ⟩
    m ∸ (n + p)
  ≡⟨⟩
    suc m ∸ suc (n + p)
  ≡⟨⟩
    suc m ∸ (suc n + p)
  ∎

-- 8)
*-identityˡ : ∀ (n : ℕ) -> 1 * n ≡ n
*-identityˡ n =
  begin
    1 * n
  ≡⟨⟩
    (suc zero) * n
  ≡⟨⟩
    n + (zero * n)
  ≡⟨⟩
    n + zero
  ≡⟨ +-identityʳ n ⟩
    n
  ∎

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p =
  begin
    m ^ (zero + p)
  ≡⟨⟩
    m ^ p
  ≡⟨ sym (*-identityˡ (m ^ p)) ⟩
    1 * m ^ p
  ≡⟨⟩
    (m ^ zero) * (m ^ p)
  ∎
^-distribˡ-+-* m (suc n) p =
  begin
    m ^ (suc n + p)
  ≡⟨⟩
    m ^ suc (n + p)
  ≡⟨⟩
    m * (m ^ (n + p))
  ≡⟨ cong (m *_) (^-distribˡ-+-* m n p) ⟩
    m * (m ^ n * m ^ p)
  ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩
    (m * m ^ n) * m ^ p
  ≡⟨⟩
    (m ^ suc n) * (m ^ p)
  ∎


^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero =
  begin
    (m * n) ^ zero
  ≡⟨⟩
    1
  ≡⟨⟩
    1 * 1
  ≡⟨⟩
    (m ^ zero) * (n ^ zero)
  ∎
^-distribʳ-* m n (suc p) =
  begin
    (m * n) ^ (suc p)
  ≡⟨⟩
    (m * n) * (m * n) ^ p
  ≡⟨ cong ((m * n) *_) (^-distribʳ-* m n p) ⟩
    (m * n) * ((m ^ p) * (n ^ p))
  ≡⟨ sym (*-assoc (m * n) (m ^ p) (n ^ p)) ⟩
    ((m * n) * (m ^ p)) * (n ^ p)
  ≡⟨ cong (_* (n ^ p)) (*-assoc m n (m ^ p)) ⟩
    (m * (n * (m ^ p))) * (n ^ p)
  ≡⟨ cong (λ {term -> (m * term) * (n ^ p)}) (*-comm n (m ^ p)) ⟩
    (m * ((m ^ p) * n)) * (n ^ p)
  ≡⟨ cong (_* (n ^ p)) (sym (*-assoc m (m ^ p) n)) ⟩
    (m * (m ^ p) * n) * (n ^ p)
  ≡⟨ *-assoc (m * (m ^ p)) n (n ^ p) ⟩
    m * (m ^ p) * (n * (n ^ p))
  ≡⟨⟩
    (m ^ suc p) * (n ^ suc p)
  ∎

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero =
  begin
    (m ^ n) ^ zero
  ≡⟨⟩
    1
  ≡⟨⟩
    m ^ zero
  ≡⟨ cong (m ^_) (sym (*-absorbingʳ n)) ⟩
    m ^ (n * zero)
  ∎
^-*-assoc m n (suc p) =
  begin
    (m ^ n) ^ suc p
  ≡⟨⟩
    (m ^ n) * (m ^ n) ^ p
  ≡⟨ cong ((m ^ n) *_) (^-*-assoc m n p) ⟩
    (m ^ n) * (m ^ (n * p))
  ≡⟨ cong (λ {term -> (m ^ n) * (m ^ term)}) (*-comm n p) ⟩
    (m ^ n) * (m ^ (p * n))
  ≡⟨ sym (^-distribˡ-+-* m n (p * n)) ⟩
    m ^ (n + p * n)
  ≡⟨⟩
    m ^ (suc p * n)
  ≡⟨ cong (m ^_) (*-comm (suc p) n) ⟩
    m ^ (n * suc p)
  ∎

-- 9)
data Bin : Set where
  - : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc - = - I
inc (rest O) = rest I
inc (rest I) = (inc rest) O

to : ℕ → Bin
to zero = - O
to (suc n) = inc (to n)

from : Bin → ℕ
from - = 0
from (rest O) = 2 * from rest
from (rest I) = 2 * from rest + 1

bin-inverse-suc-inc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
bin-inverse-suc-inc - = refl
bin-inverse-suc-inc (b O) =
  begin
    from (inc (b O))
  ≡⟨⟩
    from (b I)
  ≡⟨⟩
    2 * from b + 1
  ≡⟨ +-comm (2 * from b) 1 ⟩
    suc (2 * from b)
  ≡⟨⟩
    suc (from (b O))
  ∎
bin-inverse-suc-inc (b I) =
  begin
    from (inc (b I))
  ≡⟨⟩
    from ((inc b) O)
  ≡⟨⟩
    2 * from (inc b)
  ≡⟨ cong (2 *_) (bin-inverse-suc-inc b) ⟩
    2 * suc (from b)
  ≡⟨ *-comm 2 (suc (from b)) ⟩
     suc (from b) * 2
  ≡⟨⟩
    (1 + from b) * 2
  ≡⟨ *-distrib-+ 1 (from b) 2 ⟩
    1 * 2 + from b * 2
  ≡⟨ cong (1 * 2 +_) (*-comm (from b) 2) ⟩
    1 * 2 + 2 * from b
  ≡⟨⟩
    2 + 2 * from b
  ≡⟨⟩
    suc 1 + 2 * from b
  ≡⟨⟩
    suc (1 + 2 * from b)
  ≡⟨ cong (suc) (+-comm 1 (2 * from b)) ⟩
    suc (2 * from b + 1)
  ≡⟨⟩
    suc (from (b I))
  ∎

-- ∀ (b : Bin) → to (from b) ≡ b
-- This does not work, as "from" is a surjective function. Both "-" and "- O" from Bin map into 0 from ℕ. Surjective functions have no left inverse.
-- 0 would have to map into two values, making the inverse of "from" not a function.

-- This works, as "to" is an injective function. 0 from ℕ maps (according to our definition) into "- O" in Bin. Injective functions have a left inverse.
-- "from" is a left inverse to "to". Note that there are infinitely many left inverses, since "-" could be mapped to any value in ℕ.
from∘to≡idₗ : ∀ (n : ℕ) → from (to n) ≡ n
from∘to≡idₗ n = {!!}
