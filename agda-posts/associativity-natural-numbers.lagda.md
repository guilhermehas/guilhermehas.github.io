---
date: 2021-05-22
title: Defining Natural Numbers using its associativity property
author: Guilherme
---

# Defining Natural Numbers using its associativity property

```
{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetTruncation
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso; isoToPath)
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤)
```

The natural numbers are defined using Peano axioms. So a natural number can be zero or the successor of another natural number.

```
data ℕ : Set where
  zero : ℕ
  suc  : ℕ
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

Because of this problem, in Cubical Type Theory, it is usually necessary to truncate the Set. So the natural numbers will be defined in this way:

```
data N : Set where
  one : N
  _+_ : N → N → N
  assoc : (a b c : N) → (a + b) + c ≡ a + (b + c)
  trunc : isSet N
```

To use them, it is good to have eliminators:

```
module Elim {ℓ'} {B : N → Type ℓ'}
  (one* : B one) (_+*_ : {m n : N} → B m → B n → B (m + n))
  (assoc* : {x y z : N} (x' : B x) (y' : B y) (z' : B z)
            → PathP (λ i → B (assoc x y z i)) ((x' +* y') +* z') (x' +* (y' +* z')))
  (trunc* : (n : N) → isSet (B n)) where

  f : (n : N) → B n
  f one = one*
  f (m + n) = f m +* f n
  f (assoc x y z i) = assoc* (f x) (f y) (f z) i
  f (trunc m n p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc* (f m) (f n) (cong f p) (cong f q) (trunc m n p q) i j

module ElimProp {ℓ'} {B : N → Type ℓ'} (BProp : {n : N} → isProp (B n))
  (one* : B one) (_+*_ : {m n : N} → B m → B n → B (m + n)) where

  f : (n : N) → B n
  f = Elim.f {B = B} one* _+*_
        (λ {x} {y} {z} x' y' z' →
          toPathP (BProp (transp (λ i → B (assoc x y z i)) i0 ((x' +* y') +* z')) (x' +* (y' +* z'))))
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

to one' = one
to (s a) = one + to a

from one = one'
from (a + b) = from a +' from b
from (assoc a b c i) = assoc' (from a) (from b) (from c) i
from (trunc m n p q i j) = N'-Set _ _ (λ k → from (p k)) (λ k → from (q k)) i j

from∘to one' i = one'
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
P (s n) = ⊥

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
add-lemma (s a) b = (λ i → one + (add-lemma a b i)) ∙ sym (assoc one (to a) (to b))
```
