open import Level
open import Data.Nat hiding (_+_; _*_; _≟_; NonZero) renaming (pred to predn)
open import Data.Rational as ℚ
  renaming (_+_ to _+q_; _*_ to _*q_; _/_ to _/q_)
  hiding (_≟_; _÷_; 1/_)
open import Data.Integer
  renaming (_+_ to _+z_; _*_ to _*z_; _-_ to _-z_)
  hiding (_≟_)
open import Data.Bool
open import Data.Nat.Coprimality as C
open import Data.List renaming (map to mapl)

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

sumℤ : List ℤ → ℤ
sumℤ = foldr _+z_ (+ 0)

sumℚ : List ℚ → ℚ
sumℚ = foldr _+q_ 0ℚ

prodℚ : List ℚ → ℚ
prodℚ = foldr _*q_ 1ℚ

-- nonZero-* : ∀ {x y} → ℚ.NonZero x → ℚ.NonZero y → ℚ.NonZero (x *q y)
-- nonZero-* {x} {y} p q = {!!}

_**_ : (x : ℚ) → ℤ → ⦃ _ : ℚ.NonZero x ⦄ → ℚ
x ** (+_ 0) = 1ℚ
x ** +[1+ n ] = x *q (x ** (+ n))
x ** (-[1+ 0 ]) = 1/ x
x ** (-[1+ (suc n) ]) = (1/ x) *q (x ** -[1+ n ])
