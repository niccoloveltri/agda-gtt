# Guarded Recursion in Agda via Sized Types

In type theory, programming and reasoning with possibly
non-terminating programs and potentially infinite objects is achieved
using coinductive types. Recursively defined programs of these types
need to be productive to guarantee the consistency of the type
system. Proof assistants such as Agda and Coq traditionally employ
strict syntactic productivity checks, which commonly make programming
with coinductive types convoluted. One way to overcome this issue is
by encoding productivity at the level of types so that the type system
forbids the implementation of non-productive corecursive programs. In
this paper we compare two different approaches to type-based
productivity: guarded recursion and sized types. More specifically, we
show how to simulate guarded recursion in Agda using sized types. We
formalize the syntax of a simple type theory for guarded recursion,
which is a variant of Atkey and McBride’s calculus for productive
coprogramming. Then we give a denotational semantics using presheaves
over the preorder of sizes. Sized types are fundamentally used to
interpret the characteristic features of guarded recursion, notably
the fixpoint combinator.

Structure of the code:
- Prelude.agda: preliminary functions, syntax of GTT and example of streams
- Presheaves.agda: definition of presheaves and natural transformations, operations on presheaves
- GTT/Structure.agda: Interpretation of types, contexts, terms, substitutions and definitional equalities
- GTT/Typeformers.agda: categorical semantics of GTT
- Soundness.agda: soundness and consistency of GTT

The formalization uses Agda 2.5.4.2 and Agda standard library 0.16
 The file Everything.agda contains the whole formalization.
