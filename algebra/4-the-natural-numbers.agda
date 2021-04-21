module 4-the-natural-numbers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; ⌊_/2⌋)
open import Data.List using (sum; upTo)

-- 4)
sum-to-n : ℕ -> ℕ
sum-to-n n = sum (upTo (n + 1))

gaussian : ∀ (n : ℕ) -> sum-to-n n ≡ ⌊(n * (n + 1))/2⌋
gaussian zero = refl
gaussian (suc n) = {!!}

-- 4)
--(n+1)*(n+2)/2
--
--n*(n+1)/2 + (n+1)
