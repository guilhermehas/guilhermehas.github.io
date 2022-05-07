---
date: 2022-06-06
title: Using pattern match in your favor
author: Guilherme
---

# Motivation

When I was proving a theorem of multiplication of two national numbers in Cubical Agda,
I had to pattern match integers in 3 cases (positive, negative and zero).
However, I would like to pattern match them in just two cases: zero or not zero.
For that, it is necessary to create a record with that information and I will show it below.

# Imports

Importing from [Agda standard library](https://github.com/agda/agda-stdlib).

```
open import Function
open import Data.Unit hiding (_≟_)
open import Data.Empty
open import Data.Bool hiding (_≟_)
open import Data.Nat
  using (zero; suc)
open import Data.Integer renaming (NonZero to NonZeroℤ)
open import Data.Integer.Properties
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

private variable
  z : ℤ

```

# Creating patterns

It is good to create some patterns to avoid unnecessary repetitions.

```
pattern +z = +[1+ _ ]
pattern -z = -[1+ _ ]
```

# Non zero definition

Because of the way that integers are defined in the library,
it is necessary to break it in 3 cases to figure out if it is zero or not.

```
NonZero? : ℤ → Bool
NonZero? +0 = false
NonZero? +z = true
NonZero? -z = true
```

# Record Integer

To be possible to pattern match integer in two cases,
it is necessary to add a boolean that represents if the integer is zero or not.
With that boolean, it is necessary a proof that this boolean is true and false when
the integer is not zero or zero respectively.

```
infix 6 _⟦_⟧⟦_⟧

record Int : Set where
  constructor _⟦_⟧⟦_⟧
  field
    int : ℤ
    nonZero? : Bool
    nonZero?-≡ : NonZero? int ≡ nonZero?

  NonZero : Set
  NonZero = T nonZero?

open Int
```

# Integer patterns

These patterns (`≡0` and `≢0`) have just the information if the integer is zero or not.

```
pattern intnz x = _⟦_⟧⟦_⟧ _ x _
pattern ≡0 = intnz false
pattern ≢0 = intnz true
```

# Integer multiplication

The multiplication of Int are the same of ℤ and the product of them are non zero if both integers are non zero.

```
infixl 7 _·_

_·_ : Int → Int → Int
(x ⟦ nx ⟧⟦ nx≡ ⟧) · (y ⟦ ny ⟧⟦ ny≡ ⟧)
  = x * y ⟦ nx ∧ ny ⟧⟦ α x y nx ny {nx≡} {ny≡} ⟧ where
```

The hardest part is to prove that the product of x and y are non zero if and only if x and y are non zero.
When both are non zero, it is necessary to patten match when they are positive and negative.
When one of them is zero, the product is zero by the definition of multiplication.
It is necessary to do the rewrite when zero is multiplied in the right side.

```
  α : ∀ x y nx ny → {NonZero? x ≡ nx} → {NonZero? y ≡ ny}
    → NonZero? (x * y) ≡ nx ∧ ny
  α +z +z true true = refl
  α +z -z true true = refl
  α -z +z true true = refl
  α -z -z true true = refl
  α +0 y  false _   = refl
  α +[1+ n ] +0 true false rewrite *-comm +[1+ n ] +0 = refl
  α -[1+ n ] +0 true false rewrite *-comm -[1+ n ] +0 = refl
```

# Final theorem

This theorem is necessary to solve a problem of rational numbers.
Let two equals rational numbers `p = w ÷ x` and `q = z ÷ y`.
Both `x` and `y` are non zero because they are denominators of rational numbers.
Because they are equal, `w * y = z * x`.

I was creating a function to figure out if a rational number is zero or not using quotient types in Cubical Agda.
They are zero if the numerator is zero.
And in Cubical Agda, I have to prove that all rational numbers that are equal to this one have the same property.
In the end, I have to solve this theorem below.

Because of the definitions that I made above, there are just two cases of this product `w * y = z * x`.
When both `w` and `z` are zero or different than zero. In the end, making a record with a boolean make it
possible to just pattern match in the cases that a number is zero or not.

```
theoProd : ∀ x y w z → {NonZero x} → {NonZero y}
  → { w · y ≡ z · x }  → nonZero? w ≡ nonZero? z
theoProd ≢0 ≢0 ≡0 ≡0 = refl
theoProd ≢0 ≢0 ≢0 ≢0 = refl
```
