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

Diego Marmsoler and Achim D. Brucker formalised a denotational semantics of Solidity in Is-
abelle/HOL, while our approach is rule-based. Their storage model uses strings
as locations to represent addresses, thus realizing storage as a flat mapping from
locations to values, which is closer to our lazy modeling approach. String con-
catenation is used to compute, e.g. the location of the value of a key for a map
in storage, while we use an explicit algebra of paths of fields to navigate to the
struct to be accessed. This provides us with more structure without needing to
resort to string operations. We maintain a similar difference concerning mem-
ory. While their memory model is close to ours, they represent roots as natural
numbers and use them as seeds to compose strings of derived identities. This
requires complex string operations when reasoning about identities.

A further difference is that when copying reference values from storage to
memory, their approach is eager (using an explicit iteration function), while our
approach performs the copying lazily and only on-demand. We also proved that
our lazy copy is observationally equivalent to the eager version. The verification
approach described in *Deductive verification of Solidity smart contracts with SSCalc* is based on these semantics.

Jiao Jiao, Shang-Wei Lin and Jun Sun developed an operational semantics for Solidity within
the K-framework. The semantics is less abstract and closer to low-level
representations. To the best of our understanding, they model both memory
and storage as a list/mapping from addresses to values.

From these, the one closest to our work is *SMT-Friendly Formalization of the Solidity Memory
Model*. Its authors present an SMT-friendly encoding of Solidity’s data areas into the SMT-Lib format. This en-coding, which optimizes for SMT solvers (e.g., packing access paths into lists
of integers), uses SMT-Libs’ tuples and native arrays to encode structs and
(dynamic) arrays. Their approach is closer to an eager encoding than to ours.
Since our focus is on semi-automatic proving with user interaction, our encod-
ing is more human-friendly and aids users in comprehending intermediate proof
states. Another difference to our approach is the treatment of struct (and array)
initialization. When reading a value from a struct that has still its default value,
their formalization requires instantiating a binder (qualifier) to access the value.
Our approach does not require any instantiation, and the default initialization
is simply modeled by the axiomatization of reading from an empty struct.

We briefly discuss the remaining two model checking approaches: The pa-
per *SolCMC: Solidity Compiler’s Model Checker* does not
detail their formalization of storage and memory. In its absence,
we conducted a few experiments with the following outcome: Their modeling
works for (at least common) cases that involve storage, but does not support
memory-related use cases like shallow embedding. It is therefore more suitable
for bug-finding, and as it is part of the official Solidity compiler, we assume the
focus is on finding bugs while maintaining short compile times.

Solidifier uses Boogie as an intermediate language and Corral as
its solver backend. Their storage model is incomplete, neither deletion nor the
’empty’ push are supported. This might be a consequence of the relatively old
Solidity version on which their tool and approach are based. For the formalization
of initial values of struct fields (and similar) the same observations as for
*SMT-Friendly Formalization of the Solidity Memory Model* hold.
