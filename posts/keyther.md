---
date: 2026-01-07
title: KeYther
author: Guilherme
---
# Achievements

It is a great news that we published *An Axiomatisation of Solidity Memory and Storage* in the
23rd International Conference on Software Engineering and Formal Methods.

# Introduction

KeYther is a theorem prover that I am creating for Solidity, which is the main programming language for the biggest smart contract plataform: Ethereum. KeYther is based on KeY system, that is used to verify Java programs using dynamic logic (which is a proof calculus on symbolic execution).

The basis of a program logic for a programming language is the formalisation of the data types offered by, and definable in, the language. In this work, we already did an axiomatisation of Solidity's data types, which is essentially an algebraic specification of these data types. The axioms, or rules, are meant to symbolically execute operations on symbolic expressions appearing in logical formulas. In future work, this axiomatisation will be embedded in a (symbolic execution based) proof calculus for Solidity dynamic logic. However, it can be equally used by other verification approaches, based on Hoare logic or weakest precondition calculi.

## Memory

In our work, we started by formalising the memory model that works like a memory table with pointers. Because of that, the copy is shallow. In addition, Solidty has arbitrarily nested data structures. So we formalizing memory by creating an identity for each structure, and nested structures are formalized as a list of fields.

## Storage

For the storage, they work as value data types. So we formalized it in two ways: lazy and eager:

- In eager, the storage is formalized as a tree, which is more intuitive.
- In lazy approach, the storage is formalized as a list of keys and values. So it has a flat data structure.

## Storage and Memory

In Solidity, it is possible to copy from storage to memory and vice-versa. We did also both formalization of lazy and eager copy.
The eager does the "real copy" while the lazy looks what the eager approach is suposed to do. We did some formalization in Lean theorem prover that the eager approach respect the lazy definition.

# Related Work

The work of Diego Marmsoler and Achim D. Brucker of **Denotational semantics of Solidity in Isabelle/HOL** has the axiomatization of memory and storage, but it is still not enough for high degree of automation.

The paper **SMT-Friendly Formalization of the Solidity Memory Model** has good automation because it relies on Boogie, which uses Z3 (an SMT solver). However, the memory and storage are still not fully automatizes.

Solidifier is another great theorem prover with high level of automation. However, it is a bounded model checker, so it can not verify  big and complex programs.

In conclusion, our work is the only one with full formalization of memory and storage and with high degree of automation.
