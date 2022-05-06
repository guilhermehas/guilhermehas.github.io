---
date: 2022-06-06
title: Using pattern match in your favor
author: Guilherme
---

```
open import Function
open import Data.Unit
  hiding (_≟_)
open import Data.Empty
open import Data.Bool
  hiding (_≟_)
open import Data.Nat
  using (zero; suc)
open import Data.Integer renaming (NonZero to NonZeroℤ)
open import Data.Integer.Properties
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

pattern +z = +[1+ _ ]
pattern -z = -[1+ _ ]

NonZero? : ℤ → Bool
NonZero? +0 = false
NonZero? +z = true
NonZero? -z = true

record Int : Set where
  constructor _⟦_⟧⟦_⟧
  field
    int : ℤ
    nonZero : Bool
    nonZero-≡ : NonZero? int ≡ nonZero

pattern intnz x = _⟦_⟧⟦_⟧ _ x _
pattern ≡0 = intnz false
pattern ≢0 = intnz true

open Int

NonZero : Int → Set
NonZero ≡0 = ⊥
NonZero ≢0 = ⊤

_·_ : Int → Int → Int
(x ⟦ nx ⟧⟦ nx≡ ⟧) · (y ⟦ ny ⟧⟦ ny≡ ⟧) = (x * y) ⟦ (nx ∧ ny) ⟧⟦ α x y nx ny {nx≡} {ny≡} ⟧ where
  α : ∀ x y nx ny → {NonZero? x ≡ nx} → {NonZero? y ≡ ny} → NonZero? (x * y) ≡ nx ∧ ny
  α +0 y false _    = refl
  α +[1+ n ] +0 true false rewrite *-comm +[1+ n ] +0 = refl
  α +z +z true true = refl
  α +z -z true true = refl
  α -[1+ n ] +0 true false rewrite *-comm -[1+ n ] +0 = refl
  α -z +z true true = refl
  α -z -z true true = refl

theoProd : ∀ x y w z → {NonZero x} → {NonZero y}
  → { w · y ≡ z · x }  → nonZero w ≡ nonZero z
theoProd ≢0 ≢0 ≡0 ≡0 = refl
theoProd ≢0 ≢0 ≢0 ≢0 = refl
```
