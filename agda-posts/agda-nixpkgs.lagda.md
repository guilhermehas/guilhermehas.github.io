---
date: 2022-03-18
title: How an Agda package in Nixpkgs should be
author: Guilherme
---

# Motivation

Looking at how Agda was compiled in
[Nixpkgs](https://github.com/NixOS/nixpkgs/blob/nixos-unstable/pkgs/build-support/agda/default.nix),
I saw that the code is with a lot of noise that obscures the important information.
To solve this problem, I use the concepts of this
[YouTube video](https://youtu.be/vNwukfhsOME)
to refactor my code trying to transform everything that is possible into data.

# Imports

Importing from [Agda standard library](https://github.com/agda/agda-stdlib).

```
open import Data.Nat
open import Data.Bool
open import Data.String
open import Data.List
open import Function
```

# Defining a package

An executable file is a program that will run such as Agda, GHC, Idris...
I will assume it is as a Set, but this definition can be improved later.

```
module agda-nixpkgs
  (Executable : Set)
  where
```

A package in  will be formed by a name, a version, a list of extensions
(such as ".agda" for Agda files or ".doc" for Word files), a list of their developers, and an executable file.

```
record Package : Set where
  field
    name : String
    version : ℕ
    extensions : List String
    developers : List String
    executable : Executable

open Package
```

# Defining an Agda Package

I will define GHC as a Set of GHC compilers, so each version of the GHC compiler belongs to this set.
In addition, each Agda Library also belongs to the AgdaLibrary set.

```
module _
  (GHC : Set)
  (AgdaLibrary : Set)
  where
```

Instead of giving information in the command line of what the Agda command should be,
it is better to have a record type of different options.
This approach avoids error mistakes and make the code more restrict.
The options will be the GHC compiler, the libraries that Agda will use,
and if it will use or not the local interfaces option.

```
  record AgdaOptions : Set where
    field
      ghc : GHC
      libraries : List AgdaLibrary
      localInterfaces : Bool

  open AgdaOptions
```

## Example

To make an example of the Agda package, it will be necessary to define an Agda Builder
that generates an Agda executable from their options.
In addition, I created a default GHC compiler and some Agda Libraries to use as examples.

```
  module _
    (agdaBuilder : AgdaOptions → Executable)
    (defaultGHC : GHC)
    (cubical agda-stdlib : AgdaLibrary)
    where
```

The default option is with the default GHC compiler, with no libraries and without using the local interface option.

```
    defaultAgdaOptions : AgdaOptions
    ghc defaultAgdaOptions = defaultGHC
    libraries defaultAgdaOptions = []
    localInterfaces defaultAgdaOptions = false
```

I created this operator `^∙` to add new libraries in Agda Options.

```
    _^∙_ : AgdaOptions → AgdaLibrary → AgdaOptions
    ghc (opts ^∙ lbry) = opts .ghc
    libraries (opts ^∙ lbry) = lbry ∷ opts .libraries
    localInterfaces (opts ^∙ lbry) = opts .localInterfaces

    infixl 5 _^∙_
```

Finally, the Agda Package with Cubical and Standard Libraries.

```
    agdaPackage : Package
    name agdaPackage = "agda"
    version agdaPackage = 1
    extensions agdaPackage = "agda" ∷ [ "lagda" ]
    developers agdaPackage = [ "Ulf Norell" ]
    executable agdaPackage = agdaBuilder $ defaultAgdaOptions ^∙ cubical ^∙ agda-stdlib
```
