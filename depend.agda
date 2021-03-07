module depend where

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

num3 : Nat
num3 = suc (suc (suc zero))

_+_ : Nat → Nat → Nat
zero + y = y
suc x + y = suc (x + y)
