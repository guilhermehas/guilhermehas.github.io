open import Level
open import Data.Nat
  hiding (_≟_; NonZero)
  renaming (pred to predn; _+_ to _+n_; _*_ to _*n_)
open import Data.Rational as ℚ
  renaming (_+_ to _+q_; _*_ to _*q_; _/_ to _/q_)
  hiding (_≟_; _÷_; 1/_)
open import Data.Integer
  renaming (_+_ to _+z_; _*_ to _*z_; _-_ to _-z_)
  hiding (_≟_)
open import Data.Bool
open import Data.Nat.Coprimality as C
open import Data.List renaming (map to mapl)
open import Data.Vec renaming (foldr to foldrv; tabulate to tabulateV)
open import Data.Fin
open import Function
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

private variable
  ℓ ℓ' : Level
  A : Set ℓ
  B : Set ℓ'
  m n : ℕ

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

sumℤv : Vec ℤ n → ℤ
sumℤv = foldrv _ _+z_ (+ 0)

sumℚ : List ℚ → ℚ
sumℚ = foldr _+q_ 0ℚ

prodℚ : List ℚ → ℚ
prodℚ = foldr _*q_ 1ℚ

prodℚv : Vec ℚ n → ℚ
prodℚv = foldrv _ _*q_ 1ℚ

-- nonZero-* : ∀ {x y} → ℚ.NonZero x → ℚ.NonZero y → ℚ.NonZero (x *q y)
-- nonZero-* {x} {y} p q = {!!}

-- _*qz_ : ℚ → ℤ → ℚ
-- p *qz q = ↥ p *z q /q ↧ₙ p

_**_ : (x : ℚ) → ℤ → ⦃ _ : ℚ.NonZero x ⦄ → ℚ
x ** (+_ 0) = 1ℚ
x ** +[1+ n ] = x *q (x ** (+ n))
x ** (-[1+ 0 ]) = 1/ x
x ** (-[1+ (suc n) ]) = (1/ x) *q (x ** -[1+ n ])

sumFin : ∀ {n} → (Fin n → ℤ) → ℤ
sumFin {ℕ.zero } fn = + 0
sumFin {ℕ.suc n} fn = fn Fin.zero +z sumFin λ fin → fn (Fin.suc fin)

mapvn : (Fin n → A → B) → Vec A n → Vec B n
mapvn f [] = []
mapvn f (x ∷ xs) = f Fin.zero x ∷ mapvn (λ fn → f (Fin.suc fn)) xs

private
  fn : Fin 2 → ℕ → ℕ
  fn x = toℕ x +n_

  _ : mapvn fn (10 ∷ 100 ∷ []) ≡ 10 ∷ 101 ∷ []
  _ = refl

  _nℚ = λ n → (+ n) /q 1

  -- _ : (2 nℚ) *qz (+ 5) ≡ (10 nℚ)
  -- _ = refl
