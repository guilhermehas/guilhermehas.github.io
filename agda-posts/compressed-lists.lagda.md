---
date: 2021-05-31
title: Compressed lists in Cubical Agda
author: Guilherme
---

# Motivation

There is a simple problem of string compression that can be found in
[Hacker Rank](https://www.hackerrank.com/challenges/string-compression/problem)
or in [LeetCode](https://leetcode.com/problems/string-compression/) that consists of compressing
each element of string by the number of times that
it appears. For example, "aa" is compressed to "a2" and "bbccc" is compressed to "b2c3".
In this post, I will create a data structure in cubical Agda that has compressed and uncompressed formats.

# Imports

Importing Cubical Libraries:

```
{-# OPTIONS --cubical --guardedness #-}

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import Cubical.Data.Nat

module _ where
  module compListMod {ℓ} (A : Set ℓ) (discA : Discrete A) where
```

# Definition

Compressed lists can be an empty list or a valued repeated one or more times joined with another compressed list.
Two compressed lists are equal when they are joined with the same value. For example: "a1a2" ≡ "a3" ≡ "a1a2".
In the next lines, the definition of compressed lists with these properties:

```
    infixr 5 _qt1+_∷_
    data CompressedList : Set ℓ where
      []           : CompressedList
      _qt1+_∷_       : A → ℕ → CompressedList → CompressedList
      sameQuantity : (m n : ℕ) (x : A) (xs : CompressedList)
        → x qt1+ m ∷ x qt1+ n ∷ xs ≡ x qt1+ 1 + m + n ∷ xs
      isSetComp    : isSet CompressedList
```


# Transforming compressed lists

From compressed lists, I will generate their lists. For example, "a2" will be transformed to "aa".

```
    _qtL1+_∷_ : A → ℕ → List A → List A
    ListSet : isSet (List A)

    compToList : CompressedList → List A
    compToList [] = []
    compToList (x qt1+ n ∷ xs) = x qtL1+ n ∷ compToList xs
    compToList (sameQuantity zero n x xs i) = x ∷ (x qtL1+ n ∷ compToList xs)
    compToList (sameQuantity (suc m) n x xs i) = x ∷ compToList (sameQuantity m n x xs i)
    compToList (isSetComp xs ys p q i j) =
      ListSet _ _ (λ k → compToList (p k)) (λ k → compToList (q k)) i j

    x qtL1+ zero ∷ xs = x ∷ xs
    x qtL1+ suc n ∷ xs = x ∷ (x qtL1+ n ∷ xs)

    ListSet = Discrete→isSet (discreteList discA)
```

The `Discrete→isSet` is an important theorem. It needs to be used because if there are multiple ways of a value of
a list is equal to another value of the list, the proof can become very messy or maybe impossible to do.


The simplest way to transform a list into a compressed list is to associate the quantity of 1 of each element of the list
in the following lines:

```
    listToComp : List A → CompressedList
    listToComp [] = []
    listToComp (x ∷ xs) = x qt1+ 0 ∷ listToComp xs
```


# Examples

Some examples of the use of compressed lists:

```
  open compListMod ℕ discreteℕ

  _ : compToList (100 qt1+ 0 ∷ []) ≡ 100 ∷ []
  _ = refl

  _ : compToList (200 qt1+ 1 ∷ 100 qt1+ 2 ∷ []) ≡ 200 ∷ 200 ∷ 100 ∷ 100 ∷ 100 ∷ []
  _ = refl

  _ : listToComp (100 ∷ []) ≡ 100 qt1+ 0 ∷ []
  _ = refl

  _ : listToComp (200 ∷ 200 ∷ 100 ∷ []) ≡ 200 qt1+ 1 ∷ 100 qt1+ 0 ∷ []
  _ = sameQuantity 0 0 200 (100 qt1+ 0 ∷ [])
```
