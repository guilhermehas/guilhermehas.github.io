open import Level
open import Data.Rational as ℚ
  renaming (_+_ to _+q_; _*_ to _*q_; _/_ to _/q_)
  hiding (_≟_; _÷_; 1/_)
open import Data.Integer
  renaming (_+_ to _+z_; _*_ to _*z_; _-_ to _-z_)
  hiding (_≟_)
open import Data.Bool
open import Data.Nat.Coprimality as C

private variable
  ℓ ℓ' : Level

Op2 : Set ℓ → Set ℓ' → Set _
Op2 A B = A → A → B

_<?>_ :  Op2 Set (Bool → Set)
(x <?> y) true  = x
(x <?> y) false = y

1/_ : (p : ℚ) → .{{_ : ℚ.NonZero p}} → ℚ
1/ mkℚ +[1+ n ] d prf = mkℚ +[1+ d ] n (C.sym prf)
1/ mkℚ -[1+ n ] d prf = mkℚ -[1+ d ] n (C.sym prf)

_÷_ : (p q : ℚ) → .{{_ : ℚ.NonZero q}} → ℚ
p ÷ q = p *q (1/ q)
