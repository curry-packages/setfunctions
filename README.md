setfunctions: Encapsulate non-deterministic computations
========================================================

This package contains an implementation of set functions.
The general idea of set functions is described in:

> S. Antoy, M. Hanus: Set Functions for Functional Logic Programming
> Proc. 11th International Conference on Principles and Practice
> of Declarative Programming (PPDP'09), pp. 73-82, ACM Press, 2009

The general concept of set functions is as follows.
If `f` is an n-ary function, then `(setn f)` is a set-valued
function that collects all non-determinism caused by f (but not
the non-determinism caused by evaluating arguments!) in a set.
Thus, `(setn f a1 ... an)` returns the set of all
values of `(f b1 ... bn)` where `b1`,...,`bn` are values
of the arguments `a1`,...,`an` (i.e., the arguments are
evaluated "outside" this capsule so that the non-determinism
caused by evaluating these arguments is not captured in this capsule
but yields several results for `(setn...)`.
Similarly, logical variables occuring in `a1`,...,`an` are not bound
inside this capsule (in PAKCS they cause a suspension until
they are bound).

*Remark:*
Since there is no special syntax for set functions,
one has to write `(setn f)` for the set function of the
_n-ary top-level function_ `f`.
The correct usage of set functions is currently not checked by
the compiler, i.e., one can also write unintended uses
like `set0 ((+1) (1 ? 2))`.
In order to check the correct use of set functions,
it is recommended to apply the tool
[CurryCheck](https://cpm.curry-lang.org/pkgs/currycheck.html)
on Curry programs which reports illegal uses of set functions
(among other properties).

The set of values returned by a set function is represented
by an abstract type `Values` on which several operations are
defined in this module. Actually, it is a multiset of values,
i.e., duplicates are not removed.

The handling of failures and nested occurrences of set functions
is not specified in the previous paper. Thus, a detailed description
of the semantics of set functions as implemented in this library
can be found in the paper

> J. Christiansen, M. Hanus, F. Reck, D. Seidel:
> A Semantics for Weakly Encapsulated Search in Functional Logic Programs
> Proc. 15th International Conference on Principles and Practice
> of Declarative Programming (PPDP'13), pp. 49-60, ACM Press, 2013

Note that the implementation of this library uses multisets
instead of sets. Thus, the result of a set function might
contain multiple values. From a declarative point of view,
this is not relevant. It has the advantage that equality
is not required on values, i.e., encapsulated values can also
be functional.

The PAKCS implementation of set functions has several restrictions,
in particular:

1. The multiset of values is completely evaluated when demanded.
   Thus, if it is infinite, its evaluation will not terminate
   even if only some elements (e.g., for a containment test)
   are demanded. However, for the emptiness test, at most one
   value will be computed
2. The arguments of a set function are strictly evaluated before
   the set functions itself will be evaluated.
3. If the multiset of values contains unbound variables,
   the evaluation suspends.

--------------------------------------------------------------------------

Note that the functionality of this package is largely contained
in the modules `Control.Search/...` of the
[base package](https://cpm.curry-lang.org/pkgs/base.html)
since version 3.3.0, which is part of newer Curry distributions.

--------------------------------------------------------------------------
