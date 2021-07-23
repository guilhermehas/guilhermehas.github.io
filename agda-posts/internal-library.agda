open import Data.Bool

_<?>_ : (x y : Set) → Bool → Set
(x <?> y) true  = x
(x <?> y) false = y
