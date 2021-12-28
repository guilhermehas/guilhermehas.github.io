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
module unit-of-measure where

open import Axiom.Extensionality.Propositional
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
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Function
open import internal-library

private
  variable
    ℓ ℓ′ : Level

```

# Minimalist Case

In the minimalist case, I will only define seconds and meters.
In more complex examples, it is possible to define more dimensional.

```
module MinimalistCase where

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
      d d₁ d₂ : Dimensional
```

### Operations

In addition, both have to have the same Dimensional Type.

```
  _+d_ : Op₂ (Measure d)
  ⟦ a ⟧ +d ⟦ b ⟧ = ⟦ a +q b  ⟧
```

In multiplication and division of dimensional, both meters and seconds are added and subtracted respectively.

```
  _*u_ : Op₂ Dimensional
  (m^ mA s^ sA) *u (m^ mB s^ sB) = m^ mA +z mB s^ (sA +z sB)

  _/u_ : Op₂ Dimensional
  (m^ mA s^ sA) /u (m^ mB s^ sB) = m^ (mA -z mB) s^ (sA -z sB)
```

For multiplication and division of measures:

```
  _*d_ : Measure d₁ → Measure d₂ → Measure (d₁ *u d₂)
  ⟦ x ⟧ *d ⟦ y ⟧ = ⟦ x *q y ⟧

  _/d_ : Measure d₁ → (y : Measure d₂) → ⦃ NonZero y ⦄ → Measure (d₁ /u d₂)
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

    _ : speed' ≡ speed dist time ⦃ _ ⦄
    _ = refl

    _ : dist ≡ distance speed' time
    _ = refl
```

# Dimensional in Data Type

In this case, dimensional is in the data type.

```
module DimensionalInData where

  data Dimensional : Set where
    m s : Dimensional
```

Each dimensional has its power, that is an integer number.
For example, the area dimensional is `m^2` and the meter power is 2.

```
  DimensionalPower = Dimensional → ℤ

  m^_ : ℤ → DimensionalPower
  (m^ z) m = z
  (m^ z) s = + 0

  s^_ : ℤ → DimensionalPower
  (s^ z) m = + 0
  (s^ z) s = z
```

## Measure Type

The measure has its dimensional in its type like in the last code.

```
  private
    variable
      d d₁ d₂ : DimensionalPower

  record Measure (_ : DimensionalPower) : Set where
    constructor ⟦_⟧
    field
      measure : ℚ
    NonZero : Set
    NonZero = ℚ.NonZero measure

  open Measure
```

### Operations

The multiplication of two measures is a function that returns the sum of two-dimension.
And the division is the subtraction.

```
  _*u_ : Op₂ DimensionalPower
  (f *u g) x = f x +z g x

  _/u_ : Op₂ DimensionalPower
  (f /u g) x = f x -z g x
```

For multiplication and division of measures:

```
  _*d_ : Measure d₁ → Measure d₂ → Measure (d₁ *u d₂)
  ⟦ x ⟧ *d ⟦ y ⟧ = ⟦ x *q y ⟧

  _/d_ : Measure d₁ → (y : Measure d₂) → ⦃ NonZero y ⦄ → Measure (d₁ /u d₂)
  ⟦ x ⟧ /d ⟦ y ⟧ = ⟦ x ÷ y ⟧
```

### Defining equations

The dimensional of distance is `m`, time is `s`, and velocity is `m/s`.

```
  ud = m^ (+ 1)
  ut = s^ (+ 1)
  uv = ud /u ut
```

The distance is `speed * time`.

```
  distance : Measure uv
           → Measure ut
           → Measure (uv *u ut)
  distance speed time = speed *d time
```

It is necessary to postulate Extensionality because the type system is not smart enough
to figure out that two functions are equal.
This would be possible to verify because the domain of the function is finite (it is Bool, which has only two values).

```
  postulate
    ext : Extensionality ℓ ℓ′

  distance' : (speed : Measure uv)
              (time  : Measure ut)
                     → Measure ud
  distance' speed time = subst Measure
    (ext (λ{ m → refl ; s → refl}))
    (speed *d time)
```

Speed is defined as `distance/time`.

```
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

    _ : speed' ≡ speed dist time ⦃ _ ⦄
    _ = refl
```
