SPL
* the simply-typed lambda calculus can be used to express elements of proof
theory in the form of ``higher-order abstract syntax''.
* several languages allow the programmer to manipulate these objects
* embedded implication used to express hypothetical judgments in natural
deduction
* languages such as lambda-Prolog provide support for manipulating objects
expressed in higher-order syntax; useful for implementing theorem provers for
logics specified by LF, for example.
* Higher-order syntax and hypothetical judgments supported by many theorem
provers
* Another approach using Coq represented terms as functions mapping arguments
of type L to terms of type L and defining semantics on these functions
(nonstandard?)
CPL
Little experience in using higher-order syntax and hypothetical judgments
in proofs.
* Previous work on using higher-order syntax in proofs include, Elf but it
cannot express induction principles (no quantification over predicates) so
some proof work had to be offloaded to other tools.
WTD
* Utilise induction in the system Coq along with second-order syntax and
embedded implication to define a small functional language (contains only abs
and app)
* Small functional language defined: adequacy of syntax proven.
* The use of higher-order syntax to define the object language means that
alpha convertible terms in the object language map to alpha convertible terms
in Coq
* Beta reduction defined using a substitution inductive predicate
* Work up to extensional equality (consider object language terms as equiv.
classes of terms that are extensionally equal).
ROF
* Coq inductive types express more than what the object language is capable,
needed a predicate to defined well-formedness; those terms which correspond
to programs in the object language.
* Syntax chosen to represent object language in Coq simplifies proof details
* don't require to mention variables or fresh variables not occurring in terms
in the proofs for substitution and well-formedness (``valid'')
* Plan to generalise their specification of syntax
* Proof of Church-Rosser property
* Adequacy of semantic definitions
* ``meta'' theorems?
IMP
* Step towards HOAS support
