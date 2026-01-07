---
date: 2021-05-26
title: Defining Natural Numbers using its associativity property in Agda
author: Guilherme
---

# Motivation

When I was looking at how to do simple addition in decimal, I saw that we use the associativity property of natural numbers.
For example, `15 + 26 ≡ (10 + 5) + (20 + 6) ≡ 10 + 20 + (5 + 6) ≡ (10 + 20 + 10) + 1 ≡ 40 + 1 ≡ 41`.
In the following, I saw that it was always possible, with just the associativity property, to transform any addition to `1+(1+(1+...))`.
In Cubical Type Theory, there are quotient types. Therefore, it is possible to create natural numbers with associativity property in their types.
I will use this to prove that natural numbers without zero can be defined using their associativity property.

# Imports

Importing Cubical Libraries:

```
{-# OPTIONS --cubical --guardedness #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.S1
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
  using (Iso; isoToPath)
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Bool
open import Cubical.Data.Int hiding (_+_; _+'_)
open import Cubical.Data.Nat hiding (_+_)
```

To use it later:

```
_≠_ : ∀ {ℓ} {A : Set ℓ} → A → A → _
x ≠ y = ¬ (x ≡ y)
```

# Defintion

The natural numbers are defined using Peano axioms. So a natural number can be zero or the successor of another natural number.

```
data ℕ' : Set where
  zero' : ℕ'
  suc'  : ℕ' → ℕ'
```

But it can also be defined using its associativity property. I will define it starting from one and I will show why this definition is wrong:

```
module wrong-definition where
  infixl 6 _+_
  data N : Set where
    one : N
    _+_ : N → N → N
    assoc : (a b c : N) → a + b + c ≡ a + (b + c)
```

In cubical type theory, there are high inductive types (HITs), so two equalities are not always the same. Because of that, `one + one + one + one` can be equal to `one + (one + (one + one))` in two ways:

```
  o+o+o+o : N
  o+o+o+o = one + one + one + one

  o+[o+[o+o]] : N
  o+[o+[o+o]] = one + (one + (one + one))

  o≡[o] : Set
  o≡[o] = o+o+o+o ≡ o+[o+[o+o]]

  o≡[o]₁ : o≡[o]
  o≡[o]₁ = o+o+o+o
    ≡⟨ assoc _ _ _ ⟩
    (one + one + (one + one))
    ≡⟨ assoc _ _ _ ⟩
    o+[o+[o+o]] ∎

  o≡[o]₂ : o≡[o]
  o≡[o]₂ = o+o+o+o
    ≡⟨ cong (_+ one) (assoc _ _ _) ⟩
    one + (one + one) + one
    ≡⟨ assoc _ _ _ ⟩
    one + ((one + one) + one)
    ≡⟨ cong (one +_) (assoc _ _ _) ⟩
    o+[o+[o+o]] ∎
```

Now, I will prove that both of these equalities (`o≡[o]₁` and `o≡[o]₂`) are different:

```
  parity : N → Bool
  parity one = true
  parity (m + n) = parity m ⊕ parity n
  parity (assoc m n l i) = sym (⊕-assoc (parity m) (parity n) (parity l)) i

  _ : parity (one + one) ≡ false
  _ = refl

  _ : ∀ i → parity (assoc one one one i) ≡ true
  _ = λ i → refl

  model : N → S¹
  model one = base
  model (_ + _) = base
  model (assoc x _ _ i) = (if parity x then refl else loop) i

  toΩS¹ : o≡[o] → ΩS¹
  toΩS¹ = cong model

  toℤ : o≡[o] → ℤ
  toℤ p = winding (toΩS¹ p)

  o≡[o]₁-ℤ : toℤ o≡[o]₁ ≡ pos 1
  o≡[o]₁-ℤ = refl

  o≡[o]₂-ℤ : toℤ o≡[o]₂ ≡ pos 0
  o≡[o]₂-ℤ = refl


  f : o≡[o] → ℕ
  f n = abs (toℤ n)

  _ : f o≡[o]₁ ≡ 1
  _ = refl

  _ : f o≡[o]₂ ≡ 0
  _ = refl

  o≡[o]₁≠o≡[o]₂ : o≡[o]₁ ≠ o≡[o]₂
  o≡[o]₁≠o≡[o]₂ p = snotz (cong f p)
```

The secret to prove it is to try to find a function `f` that goes from each equality to a different value.
In the code above, the first equality (`o≡[o]₁`) goes to 1 while the second (o≡[o]₂) goes to 0.
So proving that `f o≡[o]₁ ≠ f o≡[o]₂`, I got `o≡[o]₁ ≠ o≡[o]₂`.

Because of the problem that two equalities are not always the same in Cubical Type Theory, it is usually necessary to truncate the Set. So the natural numbers will be defined in this way:

```
infixl 6 _+_
data N : Set where
  one : N
  _+_ : N → N → N
  assoc : (a b c : N) → a + b + c ≡ a + (b + c)
  trunc : isSet N
```

In Agda, it is possible to overload the natural numbers. So when I write `1`, it will be `one`; when I write `2`, it will be `one + one` and so on.
I will define the overload for this Natural number:

```
open import Cubical.Data.Nat.Literals public

constraintNumber : ℕ → Set
constraintNumber zero = ⊥
constraintNumber (suc _) = ⊤

fromNat' : (n : ℕ) ⦃ _ : constraintNumber n ⦄ → N
fromNat' zero ⦃ () ⦄
fromNat' (suc zero) = one
fromNat' (suc (suc n)) = fromNat' (suc n) + one

instance
  NumN : HasFromNat N
  NumN = record { Constraint = constraintNumber ; fromNat = fromNat' }

idN : N → N
idN n = n

_ : idN 1 ≡ one
_ = refl

_ : idN 2 ≡ one + one
_ = refl

_ : idN 3 ≡ one + one + one
_ = refl
```

To use these natural numbers, it is good to have eliminators:

```
module Elim {ℓ'} {B : N → Type ℓ'}
  (one* : B one) (_+*_ : {m n : N} → B m → B n → B (m + n))
  (assoc* : {x y z : N} (x' : B x) (y' : B y) (z' : B z)
            → PathP (λ i → B (assoc x y z i))
            ((x' +* y') +* z') (x' +* (y' +* z')))
  (trunc* : (n : N) → isSet (B n)) where

  f : (n : N) → B n
  f one = one*
  f (m + n) = f m +* f n
  f (assoc x y z i) = assoc* (f x) (f y) (f z) i
  f (trunc m n p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc* (f m) (f n)
    (cong f p) (cong f q) (trunc m n p q) i j

module ElimProp {ℓ'} {B : N → Type ℓ'} (BProp : {n : N} → isProp (B n))
  (one* : B one) (_+*_ : {m n : N} → B m → B n → B (m + n)) where

  f : (n : N) → B n
  f = Elim.f {B = B} one* _+*_
        (λ {x} {y} {z} x' y' z' →
          toPathP (BProp (transp (λ i → B (assoc x y z i)) i0
          ((x' +* y') +* z')) (x' +* (y' +* z'))))
        λ n → isProp→isSet BProp

module Rec {ℓ'} {B : Type ℓ'} (BType : isSet B)
  (one* : B) (_+*_ : B → B → B)
  (assoc* : (a b c : B) → (a +* b) +* c ≡ a +* (b +* c)) where

  f : N → B
  f = Elim.f one* (λ m n → m +* n) assoc* λ _ → BType
```

## Proving isomorphism of natural numbers with associativity and Peano natural numbers

First, we will define the natural numbers starting from one:

```
data N' : Set where
  one' : N'
  s : N' → N'
```


Let's define the isomorphism:

```
to : N' → N
from : N → N'
from∘to : ∀ a → from (to a) ≡ a
to∘from : ∀ n → to (from n) ≡ n

iso : Iso N N'
iso .Iso.fun = from
iso .Iso.inv = to
iso .Iso.rightInv = from∘to
iso .Iso.leftInv = to∘from
```

With the isomorphism, it is possible to prove the equality of the two sets with univalence:

```
N≡N' : N ≡ N'
N≡N' = isoToPath iso
```

Let's define the definition of addition and prove the associativity property of Peano natural numbers to use it later:

```
_+'_ : N' → N' → N'
one' +' b = s b
s a +' b = s (a +' b)

assoc' : ∀ a b c → (a +' b) +' c ≡ a +' (b +' c)
assoc' one' b c i = s (b +' c)
assoc' (s a) b c i = s (assoc' a b c i)
```

I will assume that the Peano natural numbers are a set and I will prove the easiest parts of the definitions above with this information.

```
N'-Set : isSet N'

to one' = 1
to (s a) = 1 + to a

from one = one'
from (a + b) = from a +' from b
from (assoc a b c i) = assoc' (from a) (from b) (from c) i
from (trunc m n p q i j) =
  N'-Set _ _ (λ k → from (p k)) (λ k → from (q k)) i j

from∘to one' _ = one'
from∘to (s a) i = s (from∘to a i)
```

To prove that Peano natural numbers are a set, I will use the theorem that every discrete type is a set.

```
N'-Discrete : Discrete N'

N'-Set = Discrete→isSet N'-Discrete
```

It is straightforward to prove that Peano natural numbers are discrete:

```
dec : N' → N'
dec one' = one'
dec (s m) = m

suc-eq : ∀ {m n} → s m ≡ s n → m ≡ n
suc-eq eq i = dec (eq i)

P : N' -> Set
P one' = ⊤
P (s _) = ⊥

N'-Discrete one' one' = yes λ i → one'
N'-Discrete one' (s n) = no λ eq → transport (λ j → P (eq j)) tt
N'-Discrete (s m) one' = no λ eq → transport (λ j → P (eq (~ j))) tt
N'-Discrete (s m) (s n) with N'-Discrete m n
... | yes eq = yes (cong s eq)
... | no ¬eq = no λ eq → ¬eq (suc-eq eq)
```

The last thing to prove is `to∘from` using the elimination of naturals and the following addition lemma:

```
add-lemma : ∀ a b → to (a +' b) ≡ to a + to b

to∘from = ElimProp.f (trunc _ _) (λ i → one)
  λ {a} {b} m n → add-lemma (from a) (from b) ∙ (λ i → m i + n i)

add-lemma one' b = refl
add-lemma (s a) b = (λ i → one + (add-lemma a b i))
  ∙ sym (assoc one (to a) (to b))
```

# Applications

## Vectors

In the same way that natural numbers are defined using their associativity property, vectors can also be defined in this way:

```
infixl 20 _++_
data Vec (A : Set) : N → Set where
  [_] : A → Vec A one
  _++_ : ∀ {m n} (xs : Vec A m) (ys : Vec A n) → Vec A (m + n)
  assoc : ∀ {m n p} (xs : Vec A m) (ys : Vec A n) (zs : Vec A p)
    → PathP (λ i → Vec A (assoc m n p i)) (xs ++ ys ++ zs) (xs ++ (ys ++ zs))
  isSetVec : ∀ {n} → isSet (Vec A n)

exVec₁ : Vec N 1
exVec₁ = [ 1 ]

exVec₂ : Vec N 3
exVec₂ = [ 3 ] ++ [ 2 ] ++ [ 1 ]
```
