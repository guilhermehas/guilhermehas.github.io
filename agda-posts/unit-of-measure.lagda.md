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
open import Data.Nat hiding (_+_; _*_; _≟_; NonZero) renaming (pred to predn)
open import Data.Bool hiding (_≟_)
open import Data.List renaming (map to mapl)
open import Data.Vec
  hiding (foldr; filter)
  renaming (zipWith to zipWithV; tabulate to tabulateV; lookup to lookupv)
open import Data.Product
open import Data.Rational as ℚ
  renaming (_+_ to _+q_; _*_ to _*q_; _/_ to _/q_)
  hiding (_≟_; _÷_; 1/_; NonZero; -_)
open import Data.Integer
  renaming (_+_ to _+z_; _*_ to _*z_; _-_ to _-z_)
  hiding (_≟_; NonZero)
open import Data.Integer.Instances
open import Data.Fin
open import Data.Fin.Properties renaming (_≟_ to _≟f_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Function
open import internal-library

private
  variable
    ℓ ℓ′ : Level
    n : ℕ

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

# Dimensional Unit

In this code, Dimensional and Unit are distinct.
Dimensional is something that can be measured
and Unit is the unit of measure.
For example, time and distance are two dimensions,
and meter is a unit of measure of distance.

```
module DimensionalUnit where

  data Dimensional : Set where
    distance time : Dimensional

  data Unit : Set where
    m km s ms : Unit

  _≟d_ : (x y : Dimensional) → Dec (x ≡ y)
  distance ≟d distance = yes refl
  distance ≟d time     = no (λ ())
  time     ≟d distance = no (λ ())
  time     ≟d time     = yes refl

  AllUnit : List Unit
  AllUnit = m ∷ km ∷ s ∷ ms ∷ []

  AllDimensional : List Dimensional
  AllDimensional = distance ∷ time ∷ []
```

## Conversion between Unit and Dimensional

Each unit has a dimensional associated with that.
The dimensional of meter and kilometer is distance
and the dimensional of seconds and milliseconds is time.

```
  UnitDimensional : Unit → Dimensional
  UnitDimensional m  = distance
  UnitDimensional km = distance
  UnitDimensional s  = time
  UnitDimensional ms = time

  DimensionalUnit : Dimensional → Unit
  DimensionalUnit distance = m
  DimensionalUnit time     = s

  StandardUnit? : Unit → Bool
  StandardUnit? m  = true
  StandardUnit? km = false
  StandardUnit? s  = true
  StandardUnit? ms = false
```

## Unit Proportion

Each unit has a value proportional to the standard measure.
The standard measure of distance is in meters and time in seconds.
So their values are one.
But kilometer is 1000 times meters so its value is 1000,
and milliseconds is 1/1000 of a second, so its value is 1/1000.

```
  UnitProportion : Unit → ℚ
  UnitProportion m  = 1ℚ
  UnitProportion km = + 1000 /q 1
  UnitProportion s  = 1ℚ
  UnitProportion ms = + 1 /q 1000
```

## Unit and Dimensional Power

Unit Power is the power of each unit.
For example: `m^2 * km^(- 1) * s^5 * ms^0`.

```
  UnitPower = Unit → ℤ
```

Dimensional power is the same thing as Unit power, but for dimensional.
Dimensional Value will return the value measured in the standard measure.

```
  DimensionalPower = Dimensional → ℤ

  private
    variable
      up up₁ up₂ : UnitPower

  UnitPower→DimensionalPower : UnitPower → DimensionalPower
  UnitPower→DimensionalPower up dim =
    sumℤ (mapl up (filter ((dim ≟d_) ∘ UnitDimensional) AllUnit))

  DimensionalPower→UnitPower : DimensionalPower → UnitPower
  DimensionalPower→UnitPower dp unit =
    if StandardUnit? unit then
    sumℤ (mapl dp (filter (_≟d UnitDimensional unit) AllDimensional))
    else + 0
```

## Normalization and Value associated with Unit Power

For normalization, it transforms Unit Power into Dimensional Power and after to Unit Power.
In this way, it eliminates units that are not standard such as kilometers.

```
  normalizeUnit : UnitPower → UnitPower
  normalizeUnit = DimensionalPower→UnitPower ∘ UnitPower→DimensionalPower

  NonZeroUnit : ∀ x → ℚ.NonZero (UnitProportion x)
  NonZeroUnit m  = _
  NonZeroUnit km = _
  NonZeroUnit s  = _
  NonZeroUnit ms = _
```

In this function, it gets the product of values that are not standard with their power.
For example, `km^2` will return `1.000.000` (that is `1.000^2`).


```
  UnitPower→DimensionalValue : UnitPower → ℚ
  UnitPower→DimensionalValue up = prodℚ
    (mapl (λ x → _**_ (UnitProportion x) (up x) ⦃ NonZeroUnit x ⦄) AllUnit)
```

### Examples

The Unit Power `m^1 * km^(-1) * s^0 * ms^(-2)`
will be transformed into

`m^2 * (1.000 * m)^(-1) * s^0 * (1/1000 * s)^(-2)`
≡ `1.000 * m^1 * s^(-2)`.

```
  private
    up-ex : UnitPower
    up-ex m = + 2
    up-ex km = - (+ 1)
    up-ex s = + 0
    up-ex ms = - (+ 2)

    _ : UnitPower→DimensionalValue up-ex ≡ + 1000 /q 1
    _ = refl

    _ : UnitPower→DimensionalPower up-ex distance ≡ + 1
    _ = refl

    _ : normalizeUnit up-ex m ≡ + 1
    _ = refl

    _ : normalizeUnit up-ex km ≡ + 0
    _ = refl

    _ : UnitPower→DimensionalPower up-ex time ≡ - (+ 2)
    _ = refl

    _ : normalizeUnit up-ex s ≡ - (+ 2)
    _ = refl
```

## Unit Power operations

The multiplication and division of units are the same as the last code.

```
  _*u_ : Op₂ UnitPower
  (f *u g) x = f x +z g x

  _/u_ : Op₂ UnitPower
  (f /u g) x = f x -z g x
```

The definition of measure also looks the same as the last code.

```
  record Measure (_ : UnitPower) : Set where
    constructor ⟦_⟧
    field
      measure : ℚ
    NonZero : Set
    NonZero = ℚ.NonZero measure

  open Measure
```

## Measure operations

The difference now between this and the last code is that now the unit is normalized.
So units that are not standard such as kilometers will be removed.

```
  _*m_ : Measure up₁ → Measure up₂ → Measure (normalizeUnit (up₁ *u up₂))
  _*m_ {up₁} {up₂} ⟦ x ⟧ ⟦ y ⟧ =
    ⟦ UnitPower→DimensionalValue up₁ *q UnitPower→DimensionalValue up₂ *q x *q y ⟧

  _/m_ : Measure up₁ → (y : Measure up₂) ⦃ _ : NonZero y ⦄ → Measure (normalizeUnit (up₁ *u up₂))
  _/m_ {up₁} {up₂} ⟦ x ⟧  ⟦ y ⟧ ⦃ nzy ⦄ = ⟦ _÷_
    (UnitPower→DimensionalValue up₁ *q x)
    (UnitPower→DimensionalValue up₂ *q y)
    ⦃ trustMe ⦄ ⟧
    where
      postulate
        trustMe : ℚ.NonZero (UnitPower→DimensionalValue up₂ *q y)

  _+m_ : Measure up → Measure up → Measure up
  ⟦ x ⟧ +m ⟦ y ⟧ = ⟦ x +q y ⟧
```

## Simple functions of Unit Power

Some functions to define examples in a better way.

```
  _⋆_ : ℚ → (u : UnitPower) → Measure u
  q ⋆ _ = ⟦ q ⟧

  _⋆⋆_ = λ q u → ((+ q) /q 1) ⋆ u

  m^_ : ℤ → UnitPower
  (m^ z) m  = z
  (m^ z) km = + 0
  (m^ z) s  = + 0
  (m^ z) ms = + 0

  km^_ : ℤ → UnitPower
  (km^ z) m  = + 0
  (km^ z) km = z
  (km^ z) s  = + 0
  (km^ z) ms = + 0

  s^_ : ℤ → UnitPower
  (s^ z) m  = + 0
  (s^ z) km = + 0
  (s^ z) s  = z
  (s^ z) ms = + 0
```

## Tests

These are some examples of addition.
The problem with the product is that Unit Power is a function,
so it is necessary to prove that two functions are equal and
it requires extensionality.

```
  private
    _ : (1 ⋆⋆ (m^ (+ 1))) +m (2 ⋆⋆ (m^ (+ 1)))
      ≡ (3 ⋆⋆ (m^ (+ 1)))
    _ = refl

    m/s = (m^ (+ 1)) *u (s^ (- (+ 1)))

    _ : (10 ⋆⋆ m/s) +m (20 ⋆⋆ m/s)
      ≡ (30 ⋆⋆ m/s)
    _ = refl
```

# Dimensional Units in Vector

The problem with the last approach is that it is not possible to infer
automatically that two functions are equal.
But `Fin n → A` is isomorphic to `Vec A n` and the compiler infer easily
that two vectors are equal.
So it is better to use vectors instead of functions.

```
module DimensionalUnitVector where
  DimensionalSize = 2
  UnitSize = 4

  Dimensional = Vec ℤ DimensionalSize
  Unit = Vec ℤ UnitSize
```

We have two dimensional. Distance is the first and time is the second.

```
  distance : Fin DimensionalSize
  distance = Fin.zero

  time : Fin DimensionalSize
  time = Fin.suc Fin.zero
```

These are the units of meters, kilometers, seconds, and milliseconds.

```
  m^_ : ℤ → Unit
  m^ z = z ∷ + 0 ∷ + 0 ∷ + 0 ∷ []

  km^_ : ℤ → Unit
  km^ z = + 0 ∷ z ∷ + 0 ∷ + 0 ∷ []

  s^_ : ℤ → Unit
  s^ z = + 0 ∷ + 0 ∷ z ∷ + 0 ∷ []

  ms^_ : ℤ → Unit
  ms^ z = + 0 ∷ + 0 ∷ + 0 ∷ z ∷ []
```

For each unit (m, km, s, ms), there is a dimensional associated with that.
It is in the vector `UnitDimensional`.

```
  UnitDimensional : Vec (Fin DimensionalSize) UnitSize
  UnitDimensional = distance ∷ distance ∷ time ∷ time ∷ []
```

Meters and seconds are unit standards of distance and time respectively.

```
  UnitStandard : Vec Bool UnitSize
  UnitStandard = true ∷ false ∷ true ∷ false ∷ []
```

## Unit Proportion

Unit proportion is the same in the case above.
But the difference is that it has to come with proof that all elements
are non-zero.

```
  ℚNZ = Σ[ q ∈ ℚ ] ℚ.NonZero q

  UnitProportionNZ : Vec ℚNZ UnitSize
  UnitProportionNZ = (1ℚ , _) ∷ (+ 1000 /q 1 , _)∷ ((1ℚ , _)) ∷ (+ 1 /q 1000 , _) ∷ []
```

## Unit operations

To multiplicate the unit, it is just necessary to add each element of both vectors,
and to divide, it is necessary to subtract.

```
  _*u_ : Op₂ Unit
  _*u_ = zipWithV _+z_

  _/u_ : Op₂ Unit
  _/u_ = zipWithV _-z_
```

## Unit and dimensional conversion

These functions are the same as in the case of the Dimensional Unit above.

```
  Unit→Dimensional : Unit → Dimensional
  Unit→Dimensional un =
    tabulateV λ dpos → sumFin λ unp →
    if (dpos ≟f lookupv UnitDimensional unp) .does
    then lookupv un unp else + 0

  Dimensional→Unit : Dimensional → Unit
  Dimensional→Unit dim =
    tabulateV λ unpos →
      if lookupv UnitStandard unpos
      then lookupv dim (lookupv UnitDimensional unpos) else + 0

  normalizeUnit : Unit → Unit
  normalizeUnit = Dimensional→Unit ∘ Unit→Dimensional

  Unit→Measure : Unit → ℚ
  Unit→Measure unit = prodℚv $ zipWithV (λ (q , nz) un → _**_ q un ⦃ nz ⦄) UnitProportionNZ unit
```

## Examples

These are some examples of the use of the functions above.

```
  private
    m = m^ (+ 1)
    s = s^ (+ 1)
    ms = ms^ (+ 1)
    m/s = m /u s
    km = km^ (+ 1)

    _ : Unit→Dimensional m ≡ + 1 ∷ + 0 ∷ []
    _ = refl

    _ : Unit→Dimensional m/s ≡ + 1 ∷ - (+ 1) ∷ []
    _ = refl

    _ : Unit→Dimensional km ≡ + 1 ∷ + 0 ∷ []
    _ = refl

    _ : normalizeUnit m ≡ + 1 ∷ + 0 ∷ + 0 ∷ + 0 ∷ []
    _ = refl

    _ : normalizeUnit km ≡ + 1 ∷ + 0 ∷ + 0 ∷ + 0 ∷ []
    _ = refl

    _ : normalizeUnit m/s ≡ + 1 ∷ + 0 ∷ - (+ 1) ∷ + 0 ∷ []
    _ = refl
```

## Measure definition

The Measure definition is the same as the case above.

```
  record Measure (unit : Unit) : Set where
    constructor ⟦_⟧
    field
      measure : ℚ
    NonZero : Set
    NonZero = ℚ.NonZero measure
```

The `std` function got the measure in the standard unit (such as a meter or a second).

```
    std : ℚ
    std = measure *q Unit→Measure unit
```

```
  open Measure

  private
    variable
      u u₁ u₂ : Unit
```

## Measure operations

The definition of multiplication, addition, and division is like the case above,
except that they use the `std` function,

```
  _*m_ : Measure u₁ → Measure u₂ → Measure (normalizeUnit (u₁ *u u₂))
  x *m y = ⟦ std x *q std y ⟧

  _/m_ : Measure u₁ → (y : Measure u₂) → ⦃ _ : NonZero y ⦄ → Measure (normalizeUnit (u₁ /u u₂))
  x /m y = ⟦ _÷_ (std x) (std y) ⦃ trustMe ⦄ ⟧
    where
      postulate
        trustMe : ℚ.NonZero (std y)

  _+m_ : Measure u → Measure u → Measure u
  ⟦ x ⟧ +m ⟦ y ⟧ = ⟦ x +q y ⟧

  _⋆_ : ℚ → (u : Unit) → Measure u
  q ⋆ _ = ⟦ q ⟧

  _⋆⋆_ = λ q u → ((+ q) /q 1) ⋆ u

  distanceF : Measure m/s
            → Measure s
            → Measure m
  distanceF speed time = speed *m time

  speed : (distance : Measure m)
          (time     : Measure s) ⦃ _ : NonZero time ⦄
                    → Measure m/s
  speed distance time = distance /m time
```

## Examples

Some examples using the code.

```
  private
    ⦅_⦆ : ℕ → Measure u
    ⦅ n ⦆ = ⟦ + n /q 1 ⟧

    dist : Measure m
    dist = ⦅ 6 ⦆

    speed' : Measure m/s
    speed' = ⦅ 3 ⦆

    time' : Measure s
    time' = ⦅ 2 ⦆

    time'' : Measure ms
    time'' = ⦅ 2 ⦆

    _ : Unit→Measure m ≡ + 1 /q 1
    _ = refl

    _ : std dist ≡ + 6 /q 1
    _ = refl

    _ : speed' ≡ speed dist time' ⦃ _ ⦄
    _ = refl

    _ : dist ≡ distanceF speed' time'
    _ = refl
```

The biggest difference is now in multiplication.
Because the equality of vectors is easy to verify,
it is now possible to make tests with multiplication and division.
The results are always normalized, so there is no kilometer and
milliseconds after multiplication or division.

```
    _ : (2 ⋆⋆ m/s) *m (2 ⋆⋆ m/s)
      ≡ (4 ⋆⋆ (m/s *u m/s))
    _ = refl

    _ : (2 ⋆⋆ km) *m (6 ⋆⋆ m/s)
      ≡ (12000 ⋆⋆ (m *u m/s))
    _ = refl

    _ : (_/m_ (10 ⋆⋆ m) (2 ⋆⋆ ms) ⦃ _ ⦄)
      ≡ (5000 ⋆⋆ (m /u s))
    _ = refl
```
