---
date: 2021-12-18
title: Types for units of measure
author: Guilherme
---

# Motivation

My motivation to create types for units of measure is to try to avoid bugs when dealing with dimensional.
For example, using these types, it would be impossible to add numbers of different dimensional.
Another advantage of using them is that when you deal with multiplication and division, the measure
of both values is multiples and divided.

# Imports

Importing libraries of Agda Stdlib:

```
open import Level
open import Algebra.Core
open import Data.Nat hiding (_+_; _*_; _≟_; NonZero)
open import Data.Bool hiding (_≟_)
open import Data.Vec
open import Data.Product
open import Data.Rational as ℚ
  renaming (_+_ to _+q_; _*_ to _*q_; _/_ to _/q_)
  hiding (_≟_; _÷_; 1/_; NonZero; -_)
open import Data.Integer
  renaming (_+_ to _+z_; _*_ to _*z_; _-_ to _-z_)
  hiding (_≟_; NonZero)
open import Data.Integer.Instances
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Function
open import internal-library
```

# Minimalist Case

In the minimalist case, I will only define seconds and meters.
In more complex examples, it is possible to define more dimensional.

```
record Dimensional : Set where
  constructor m^_s^_
  field
    meters  : ℤ
    seconds : ℤ

m^_ : ℤ → Dimensional
m^ z = m^ z s^ (+ 0)

s^_ : ℤ → Dimensional
s^ z = m^ + 0 s^ z
```

## Measure Type

In the measure type, the dimensional is in the type.
It will be useful when defining the addition of values with the same dimensional.

```
record Measure (dimensional : Dimensional) : Set where
  constructor ⟦_⟧
  field
    measure : ℚ
  NonZero : Set
  NonZero = ℚ.NonZero measure

open Measure
```

These variables will be used later:

```
private
  variable
    ℓ ℓ' : Level
    d d₁ d₂ : Dimensional
```

### Operations

In addition, both have to have the same Dimensional Type.

```
_+_ : Op₂ (Measure d)
⟦ a ⟧ + ⟦ b ⟧ = ⟦ a +q b  ⟧
```

In multiplication and division of dimensional, both meters and seconds are added and subtracted respectively.

```
_*_ : Op₂ Dimensional
(m^ mA s^ sA) * (m^ mB s^ sB) = m^ mA +z mB s^ (sA +z sB)

_/_ : Op₂ Dimensional
(m^ mA s^ sA) / (m^ mB s^ sB) = m^ (mA -z mB) s^ (sA -z sB)
```

For multiplication and division of measures:

```
_*d_ : Measure d₁ → Measure d₂ → Measure (d₁ * d₂)
⟦ x ⟧ *d ⟦ y ⟧ = ⟦ x *q y ⟧

_/d_ : Measure d₁ → (y : Measure d₂) → ⦃ NonZero y ⦄ → Measure (d₁ / d₂)
⟦ x ⟧ /d ⟦ y ⟧ = ⟦ x ÷ y ⟧
```

### Defining equations

One of the simplest equations in Physics are `distance = speed * time` and `speed = distance / time`.
Both will be defined in the next lines:

```
ud = m^ (+ 1)
ut = s^ (+ 1)
uv = m^ + 1 s^ (- (+ 1))

distance : (speed : Measure uv)
           (time  : Measure ut)
                  → Measure ud
distance speed time = speed *d time

speed : (distance : Measure ud)
        (time     : Measure ut) ⦃ _ : NonZero time ⦄
                  → Measure uv
speed distance time = distance /d time
```


### Examples

These are some examples of operations:

```
private module tests where
  ⦅_⦆ : ℕ → Measure d
  ⦅ n ⦆ = ⟦ + n /q 1 ⟧

  dist : Measure ud
  dist = ⦅ 6 ⦆

  speed' : Measure uv
  speed' = ⦅ 3 ⦆

  time : Measure ut
  time = ⦅ 2 ⦆

  _ : speed' ≡ speed dist time
  _ = refl

  _ : dist ≡ distance speed' time
  _ = refl
```
