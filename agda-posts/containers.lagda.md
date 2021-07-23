---
date: 2021-07-19
title: Using Containers in Agda
author: Guilherme
---

# Motivation

Containers are generic data structures and they can represent most of the Agda data types.
The advantages of using them are to prove some properties of their data structure and generate some properties for them. With Agda reflection, it is possible to generate the container associated with the data structure and get the properties and associated structures for free (e.g. deriving a functor for the data types).
[Agda Generic Library](https://github.com/effectfully/Generic) does exactly that, they get the data structure from reflection, transform it to containers, generate the equality for them and return the generated equality for the data structure.

# Imports

Importing agda standard library:

```
module containers where

open import internal-library
open import Agda.Builtin.Equality
open import Level renaming (zero to lzero; suc to lsuc)
import Function as F

open import Data.Container hiding (refl)
open import Data.Container.Combinator
open import Data.W hiding (map)
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Maybe hiding (map)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum hiding (map)
open import Data.Nat
open import Data.Fin renaming (zero to fzero; suc to fsuc) hiding (_+_)
```

# Definition

The container is a record with two fields: Shape and Position.
The shape is its shape type and the position reference each shape for a type.

## Two Container

One of the simplest containers is a container with just two elements (the same as Bool).

```
module TwoContainer where
  Two : Container lzero lzero
  Two = ⊤ ▷ F.const Bool
```

In this example, the shape is the Unit type (the set with just one element) and it has 2 positions.

Now, it is time to interpret this container:

```
  Double' : Set → Set
  Double' = ⟦ Two ⟧
```

And to add their constructors and destructors:

```
  mkDouble' : ∀ {A} → (x y : A) → Double' A
  mkDouble' x y .proj₁ = _
  mkDouble' x y .proj₂ true  = x
  mkDouble' x y .proj₂ false = y

  proj1 : ∀ {A} → Double' A → A
  proj1 (_ , p) = p true

  proj2 : ∀ {A} → Double' A → A
  proj2 (_ , p) = p false
```

To test them, I created a tuple that the first element is false and the second is true.

```
  myTuple = mkDouble' false true
```

When containers really shine is when we get type classes and properties of them for free.
All containers have a functor. So, I will invert the elements of that tuple with `map` that I got from its functor.

```
  inverted = map not myTuple

  _ : proj1 inverted ≡ true
  _ = refl

  _ : proj2 inverted ≡ false
  _ = refl
```

## Two Container with product constructor

Another way of defining a set with two elements is to define it as a product of two sets of one element.

```
module _ where
  Two : Container lzero lzero
  Two = id × id
```

The rest is almost the same:

```
  Double' : Set → Set
  Double' = ⟦ Two ⟧

  mkDouble' : ∀ {A} → (x y : A) → Double' A
  mkDouble' x y = _ , [ F.const x , F.const y ]

  proj1 : ∀ {A} → Double' A → A
  proj1 (_ , p) = p (inj₁ _)

  proj2 : ∀ {A} → Double' A → A
  proj2 (_ , p) = p (inj₂ _)

  myTuple = mkDouble' false true
  inverted = map not myTuple

  _ : proj1 inverted ≡ true
  _ = refl

  _ : proj2 inverted ≡ false
  _ = refl
```

## List Container

In the list container, the shape is the natural number.
So each natural number corresponds to a list of its size.
In the list, the position of each element is between 0 and its size.
So the position is `Fin (length list)`.

```
ListC : Container lzero lzero
ListC = ℕ ▷ Fin
```

Interpreting the list:

```
List : Set → Set
List = ⟦ ListC ⟧
```

Getting their constructors and destructors:

```
[] : {A : Set} → List A
[] = 0 , λ ()

infixr 5 _∷_
_∷_ : {A : Set} → A → List A → List A
(x ∷ (size , fxs)) .proj₁           = suc size
(x ∷ (size , fxs)) .proj₂ fzero     = x
(x ∷ (size , fxs)) .proj₂ (fsuc xs) = fxs xs

head' : {A : Set} → List A → Maybe A
head' (zero , _)    = nothing
head' (suc n , fxs) = just (fxs fzero)

tail' : {A : Set} → List A → List A
tail' (zero ,    _) = 0 , λ ()
tail' (suc n , fxs) = n , fxs F.∘ fsuc
```

The list got the Functor type class for free. So I will show in this example how to use them:

```
list : List ℕ
list = 0 ∷ 1 ∷ 2 ∷ []

listM = map (_+ 10) list

_ : head' (tail' listM) ≡ just 11
_ = refl
```

# Function container

The function container is made using `const[_]⟶_` of the library that has this property:
`⟦ const[ I ]⟶ id ⟧ X ↔ (I → ⟦ id ⟧ X) ↔ (I → F.id X) ↔ (I → X) `.

```
module _ (A : Set) where
  ContainerF : Container lzero lzero
  ContainerF = const[ A ]⟶ id
```

Interpreting it:
```
  A→B' : Set → Set
  A→B' = ⟦ ContainerF ⟧
```

Defining constructors and destructors:
```
module _ {A B : Set} where
  A→B = A→B' A B

  _∘'_ : A→B → A → B
  (_ , f) ∘' a = f (a , _)

  intro : (A → B) → A→B
  intro f = _ , f F.∘ proj₁
```

Using them with the functor that we got for free:

```
_ : map (_+ 10) (intro (_+ 1)) ∘' 0 ≡ 11
_ = refl
```

# Fixpoints

It is also possible to use fixpoints in containers too and the best example is defining natural numbers with them:

```
NatCC : Container lzero lzero
NatCC = Bool ▷ ⊥ <?> ⊤

NatC = μ NatCC

ZeroC : NatC
ZeroC = sup (true , ⊥-elim)

SucC : NatC → NatC
SucC n = sup (false , F.const n)
```
