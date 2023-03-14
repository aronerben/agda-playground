module 4-the-natural-numbers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; ⌊_/2⌋)

-- 4)
open import Data.Nat.Properties using (
  *-comm
  ; *-distribʳ-+
  ; +-suc
  ; +-comm
  ; *-distribˡ-+
  )

1+⋯+n : ℕ → ℕ
1+⋯+n zero = zero
1+⋯+n (suc n) = suc n + 1+⋯+n n

n≡[n*2]/2 : ∀ (n : ℕ) → n ≡ ⌊ n * 2 /2⌋ 
n≡[n*2]/2 zero = refl
n≡[n*2]/2 (suc n) =
  begin
    suc n
  ≡⟨ cong suc (n≡[n*2]/2 n) ⟩
    suc ⌊  n * 2 /2⌋ 
  ≡⟨⟩
    1 + ⌊  n * 2 /2⌋ 
  ≡⟨⟩
    ⌊ 2 + n * 2 /2⌋ 
  ≡⟨⟩
    ⌊ suc n * 2 /2⌋ 
  ∎

data IsEven : ℕ → Set where
  even : (k : ℕ) → IsEven (k * 2)

rearrange-lemma : ∀ n → suc (suc n) * suc n ≡ suc n * 2 + suc n * n
rearrange-lemma n =
  begin
    suc (suc n) * suc n
  ≡⟨⟩
    suc (1 + n) * (1 + n)
  ≡⟨⟩
    (2 + n) * (1 + n)
  ≡⟨ *-distribʳ-+ (1 + n) 2 n ⟩
    2 * (1 + n) + n * (1 + n)
  ≡⟨ cong (2 * (1 + n) +_) (*-comm n (1 + n)) ⟩
    2 * (1 + n) + (1 + n) * n 
  ≡⟨⟩
    2 * suc n + suc n * n 
  ≡⟨ cong (_+ suc n * n) (*-comm 2 (suc n)) ⟩
    suc n * 2 + suc n * n 
  ∎

even+even≡even : ∀ {m n : ℕ} → IsEven m → IsEven n → IsEven (m + n)
even+even≡even (even k) (even i) rewrite (sym (*-distribʳ-+ 2 k i)) =
               even (k + i)

[1+n]*n≡even : ∀ (n : ℕ) → IsEven (suc n * n)
[1+n]*n≡even zero = even 0
[1+n]*n≡even (suc n) rewrite rearrange-lemma n =
             even+even≡even (even (suc n)) ([1+n]*n≡even n) 

even/2+even/2≡[even+even]/2 : ∀ {m n : ℕ}
                             → IsEven m
                             → IsEven n
                             → ⌊ m /2⌋ + ⌊ n /2⌋ ≡ ⌊ m + n /2⌋
even/2+even/2≡[even+even]/2 (even k) (even i) =
  begin
    ⌊ k * 2 /2⌋ + ⌊ i * 2 /2⌋
  ≡⟨ cong (_+ ⌊ i * 2 /2⌋) (sym (n≡[n*2]/2 k)) ⟩
    k + ⌊ i * 2 /2⌋
  ≡⟨ cong (k +_) (sym (n≡[n*2]/2 i)) ⟩
    k + i
  ≡⟨ n≡[n*2]/2 (k + i) ⟩
    ⌊ (k + i) * 2 /2⌋
  ≡⟨ cong ⌊_/2⌋ (*-distribʳ-+ 2 k i) ⟩
    ⌊ k * 2 + i * 2 /2⌋
  ∎

gaussian-sum : ∀ (n : ℕ) → 1+⋯+n n ≡ ⌊ n * (n + 1) /2⌋
gaussian-sum zero = refl
gaussian-sum (suc n) =
  begin
    1+⋯+n (suc n)
  ≡⟨⟩
    suc n + 1+⋯+n n
  ≡⟨ cong (suc n +_) (gaussian-sum n)⟩
    suc n + ⌊ n * (n + 1) /2⌋
  ≡⟨ cong (_+ ⌊ n * (n + 1) /2⌋) (n≡[n*2]/2 (suc n)) ⟩
    ⌊ suc n * 2 /2⌋ + ⌊ n * (n + 1) /2⌋
  ≡⟨ cong (λ {term → ⌊ suc n * 2 /2⌋ + ⌊ n * term /2⌋}) (+-comm n 1) ⟩
    ⌊ suc n * 2 /2⌋ + ⌊ n * (1 + n) /2⌋
  ≡⟨⟩
    ⌊ suc n * 2 /2⌋ + ⌊ n * suc n /2⌋
  ≡⟨ cong (λ {term → ⌊ suc n * 2 /2⌋ + ⌊ term /2⌋}) (*-comm n (suc n)) ⟩
    ⌊ suc n * 2 /2⌋ + ⌊ suc n * n /2⌋
  ≡⟨ even/2+even/2≡[even+even]/2 (even (suc n)) ([1+n]*n≡even n) ⟩
    ⌊ suc n * 2 + suc n * n /2⌋
  ≡⟨ cong (⌊_/2⌋) (sym (*-distribˡ-+ (1 + n) 2 n)) ⟩
    ⌊ suc n * (2 + n) /2⌋
  ≡⟨ cong (λ {term → ⌊ suc n * term /2⌋}) (+-comm 2 n) ⟩
    ⌊ suc n * (n + 2) /2⌋ 
  ≡⟨ cong (λ {term → ⌊ suc n * term /2⌋}) (+-suc n 1) ⟩
    ⌊ suc n * (suc n + 1) /2⌋ 
  ∎


gaussian-sum' : ∀ (n : ℕ) → 1+⋯+n n ≡ ⌊ n * (n + 1) /2⌋
gaussian-sum' zero = refl
gaussian-sum' (suc n) =
  begin
    1+⋯+n (suc n)
  ≡⟨⟩
    suc n + 1+⋯+n n
  ≡⟨ {!!} ⟩
    suc n + ⌊ n * (n + 1) /2⌋
  ≡⟨ {!!} ⟩
    ⌊ suc n * 2 /2⌋ + ⌊ n * (n + 1) /2⌋
  ≡⟨ {!!} ⟩
    ⌊ suc n * 2 /2⌋ + ⌊ n * (1 + n) /2⌋
  ≡⟨⟩
    ⌊ suc n * 2 /2⌋ + ⌊ n * suc n /2⌋
  ≡⟨ {!!} ⟩
    ⌊ suc n * 2 /2⌋ + ⌊ suc n * n /2⌋
  ≡⟨ {!!} ⟩
    ⌊ suc n * 2 + suc n * n /2⌋
  ≡⟨ {!!} ⟩
    ⌊ suc n * (2 + n) /2⌋
  ≡⟨ {!!} ⟩
    ⌊ suc n * (n + 2) /2⌋ 
  ≡⟨ {!!} ⟩
    ⌊ suc n * (suc n + 1) /2⌋ 
  ∎
