# sequoia

Sequoia is an implementation of classical logic in a sequent calculus, embedded in intuitionistic logic. It is implemented as a Haskell EDSL, and is fairly full-featured, if sparsely documented (at best).

Sequoia is experimental; do not use it to pilot spacecraft, unless you really, really want to.


## Sequent calculus

A sequent states that, together, all the things to the left of the ⊢ symbol (called turnstile, pronounced “proves”) suffice to prove at least one of the things on the right:

> all of these → Γ ⊢ Δ ← prove some of these

The elements of Γ are treated conjunctively (hence all), while the elements of Δ are treated disjunctively. Computationally, we interpret ⊢ as a kind of function, Γ as a kind of sequence, and Δ as a kind of choice, and thus we can think of Γ as inputs and Δ as outputs.

Sequents are rarely seen alone, however, and instead are grouped with premises written above a line (the “line of inference”) to make rules, like this rule I’ll name “dull”:

> Γ ⊢ Δ\
> ——— dull\
> Γ ⊢ Δ

Typically we read these bottom-up; this says “to infer that Γ proves Δ, we must prove that Γ proves Δ.” (This is true, though not particularly helpful.)

Axioms are rules which can be employed without any further premises. For example the `init` rule states that an input in Γ can become an output in Δ:

> —————— init\
> A, Γ ⊢ Δ, A

Rules take premises to conclusions (the sequent underneath the line), and thus the line of inference can be understood as another kind of function arrow, mapping zero or more premise sequents to a conclusion sequent. And since sequents are themselves a kind of function, mapping hypotheses to consequents, we can see that sequent calculus proofs correspond with higher-order functional programs.

For that reason, sequoia can map rules like `init` straightforwardly onto functions like `id`, and the implementation further takes full advantage of the relationship beween the sequent calculus and continuation-passing style to provide a full suite of polarized connectives (datatypes corresponding to logical operators), including positive and negative falsities, truths, disjunctions, conjunctions, implications, quantifiers, etc.

Furthermore, sequoia offers introduction and elimination rules for aach connective, grouped together into a typeclass. (This is done to allow for different sets of rules, even for the same connectives, to be used for e.g. linear logics, altho I haven’t implemented this yet.) The built-in type `Seq` in `Sequoia.Sequent` implements all of them. Inverses are also available where provable, as are many algebraic properties for the connectives.

It is possible to perform effects, but this hasn’t been explored much yet. However, you’ve got the full power of call/CC available, not to mention delimited continuations (`Sequoia.Calculus.Control`), and while it isn’t particularly convenient at the moment, there’s even a monad transformer to lift actions into sequents.
