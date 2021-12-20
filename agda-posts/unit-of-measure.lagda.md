---
date: 2021-12-18
title: Types for units of measure
author: Guilherme
---

# Motivation

My motivation to create types for units of measure is to try to avoid bugs when dealing with measure.
For example, using these types, it would be impossible to add numbers of different units.
Another advantage of using them is that when you deal with multiplication and division, the measure
of both values is multiples and divided.

# Imports

Importing libraries of Agda Stdlib:

```
open import Level
open import Algebra.Core
open import Data.Nat hiding (_+_; _*_; _≟_)
open import Data.Bool hiding (_≟_)
open import Data.Vec
open import Data.Product
open import Data.Rational as ℚ renaming (_+_ to _+q_; _*_ to _*q_; _/_ to _/q_) hiding (_≟_)
open import Data.Integer renaming (_+_ to _+z_; _*_ to _*z_; _-_ to _-z_) hiding (_≟_)
open import Data.Integer.Instances
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Function
```

# Minimalist Case

In the minimalist case, I will only define seconds and meters.
In more complex examples, it is possible to define more units of measure.

```
record Unit : Set where
  constructor m^_s^_
  field
    meters  : ℤ
    seconds : ℤ

m^_ : ℤ → Unit
m^ z = m^ z s^ (+ 1)

s^_ : ℤ → Unit
s^ z = m^ + 1 s^ z
```

## Measure Type

In the measure type, the unit is in the type.
It will be useful when defining the addition of values with the same Unit.

```
record Measure (unit : Unit) : Set where
  constructor ⟦_⟧
  field
    measure : ℚ
```

These variables and this `Op2` function will be used later.

```
private
  variable
    ℓ ℓ' : Level
    u : Unit

Op2 : Set ℓ → Set ℓ' → Set _
Op2 A B = A → A → B
```

### Operations

In addition, both have to have the same Unit Type.

```
_+_ : Op₂ (Measure u)
⟦ a ⟧ + ⟦ b ⟧ = ⟦ a +q b  ⟧
```

In multiplication and division of units, both meters and seconds are added and subtracted respectively.

```
_*_ : Op₂ Unit
(m^ mA s^ sA) * (m^ mB s^ sB) = m^ mA +z mB s^ (sA +z sB)

_/_ : Op₂ Unit
(m^ mA s^ sA) / (m^ mB s^ sB) = m^ (mA -z mB) s^ (sA -z sB)
```

## Measure and Unit Types

In this case, the unit is not in the type, but inside the record.

```
record MeasureUnit : Set where
  constructor _**_
  field
    measure : ℚ
    unit    : Unit

open MeasureUnit
```

### Operations

To multiply and divide measure units, both the measure and the unit should be multiplied and divided respectively.

```
_*m_ : Op₂ MeasureUnit
(mA ** uA) *m (mB ** uB) = (mA *q mB) ** (uA * uB)

_/m_ : (a b : MeasureUnit) ⦃ _ : ℚ.NonZero (b .measure) ⦄ → MeasureUnit
(mA ** uA) /m (mB ** uB) = (mA ÷ mB) ** (uA / uB)
```

### Equality of units.

In the addition of both measures, it is necessary to verify if both values have the same unit.
So, I will define what it means.

```
_≡u_ : Op2 MeasureUnit Set
_≡u_ = _≡_ on unit
```

The equality of two integers is decidable, so I will use it to prove that the equality of two units
is decidable too.

```
open IsDecEquivalence ⦃ ... ⦄ hiding (refl)

_≟u_ : Decidable {A = MeasureUnit} _≡u_
(_ ** (m^ mA s^ sA)) ≟u (_ ** (m^ mB s^ sB)) with mA ≟ mB | sA ≟ sB
... | no ¬p    | _        = false because ofⁿ (λ{refl → ¬p refl})
... | _        | no ¬p    = false because ofⁿ (λ{refl → ¬p refl})
... | yes refl | yes refl = yes refl
```

With the decidable property, I can extract easily the Boolean operation and the unit type of the equality.
The unit type is interested because it can be inferred easily. After all, there is just one value of Unit type.

```
_≡uᵇ_ : Op2 MeasureUnit Bool
_≡uᵇ_ = isYes ∘₂ _≟u_

_≡uT_ : Op2 MeasureUnit Set
_≡uT_ = True ∘₂ _≟u_
```

### Addition

I created first the addition with proof that the returned result has the unit of both values.

```
_+m'_ : (x y : MeasureUnit) {eq : x ≡uT y} → Σ[ m ∈ MeasureUnit ] (x ≡u m × y ≡u m)
x@(mX ** _) +m' y@(mY ** unit) with x ≟u y
... | yes refl = ((mX +q mY) ** unit) , refl , refl
```

It is easy to remove the proof if necessary:

```
_+m_ : (x y : MeasureUnit) {eq : x ≡uT y} → MeasureUnit
(x +m y) {eq} = proj₁ (_+m'_ x y {eq})
```

#### Simple examples

These are simple examples using the addition defined early.

```
private
  ℕℚ = λ n → + n /q 1

  _u₂ = _** m^ (+ 1) s^ (+ 0)

  2ℚ = ℕℚ 2
  3ℚ = ℕℚ 3

  x = 1ℚ u₂
  y = 2ℚ u₂

  _ : x +m y ≡ 3ℚ u₂
  _ = refl
```
