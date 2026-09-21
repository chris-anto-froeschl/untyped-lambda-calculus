/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic

/-! # Definitions of α-equivalence

Five definitions of α-equivalence from [Crole2012], each capturing the same equivalence
relation on expressions:

* `∼p`  (Definition 3.1): Permutation-based with non-occurrence side condition (`AlphaEquiv`)
* `∼p#` (Definition 3.2): Permutation-based with freshness side condition (`AlphaEquivPFresh`)
* `∼¹p` (Definition 3.3): Permutation-based with non-occurrence on bodies only (`AlphaEquivP1`)
* `∼r`  (Definition 3.4): Traditional renaming axiom with non-occurrence (`AlphaEquivR`)
* `∼r#` (Definition 3.5): Renaming axiom with freshness (`AlphaEquivRFresh`)

The first three definitions use the notion of *atom swapping* (transposition), introduced in
[Gabbay2002] (Section 2, page 3), as a primitive operation for defining α-equivalence. The
key observation from [Gabbay2002] is that α-equivalence can be defined using the notion of
atom swapping in lieu of the traditional renaming/substitution approach.

The last two definitions use the traditional capture-avoiding substitution (renaming) axiom.

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012]
* [M. Gabbay and A. Pitts, *A New Approach to Abstract Syntax with Variable Binding*][Gabbay2002]

## Notation

Following the paper [Crole2012], we use the following correspondence between the paper's
abstract syntax and the λ-calculus terms:

| Paper         | Lean                |
|---------------|---------------------|
| `a`           | `Term.var x`        |
| `P(E₁, E₂)`   | `Term.app m1 m2`    |
| `B([a]E)`     | `Term.abs x m`      |
| `(z a) · E`   | `m.swap x z`        |
| `E{a'/a}`     | `m.subst a (var a')`|
| `π · E`       | `m.permute π`       |

-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.Named.Untyped.Term

blueprint_comment /-- \section{Some definitions of $\alpha$-equivalence}

The five relations below, together with the two variants of \cref{prop:4-3}, are the
definitions of Section 3 of [Crole2012], stated using the permutation action and the
capture-avoiding substitution of Section 2. -/

@[blueprint "def:agreement-set"
  (title := "Agreement set")
  (statement := /-- For permutations $\pi, \pi'$ of the set of atoms $\mathbb{A}$, the
    \emph{agreement set} is
    \[ AS(\pi, \pi') \;\overset{\text{def}}{=}\;
       \{\, a \in \mathbb{A} \mid \pi(a) = \pi'(a) \,\}. \]
    ([Crole2012], Section 2.) -/)]
def agreementSet (f g : Var → Var) : Set Var := { x | f x = g x }

@[blueprint "def:disagreement-set"
  (title := "Disagreement set")
  (statement := /-- For permutations $\pi, \pi'$ of the set of atoms $\mathbb{A}$, the
    \emph{disagreement set} is
    \[ DS(\pi, \pi') \;\overset{\text{def}}{=}\;
       \{\, a \in \mathbb{A} \mid \pi(a) \neq \pi'(a) \,\}. \]
    ([Crole2012], Section 2.) -/)]
def disagreementSet (f g : Var → Var) : Set Var := { x | f x ≠ g x }

/-- The action `π · E` of a permutation on a term, as used in [Crole2012].

Since some lemmas in section 6 are proven for general permutations, we have to introduce
this notion here aswell and derive the special case using `swap` accordingly.
-/
@[blueprint "def:permutation-action"
  (title := "Permutation action on expressions")
  (statement := /-- The action $\pi \cdot E$ of a (finitely supported) permutation $\pi$ of atoms
    on an expression $E$ is defined by recursion on $E$:
    \[ \pi \cdot a \;\overset{\text{def}}{=}\; \pi(a), \qquad
       \pi \cdot P(E_1, E_2) \;\overset{\text{def}}{=}\; P(\pi \cdot E_1, \pi \cdot E_2), \qquad
       \pi \cdot B([a]E) \;\overset{\text{def}}{=}\; B([\pi \cdot a]\,\pi \cdot E). \]
    ([Crole2012], Section 2.) -/)]
def permute (m : Term Var) (π : Equiv.Perm Var) : Term Var :=
  match m with
  | var x => var (π x)
  | abs x m => abs (π x) (m.permute π)
  | app m n => app (m.permute π) (n.permute π)

/-- The action of the transposition `(x y)` on a term: simultaneously swaps all occurrences
of `x` and `y`. Corresponds to `(x y) · E` in [Crole2012] (Section 2).

`swap` is is one special case of a permutation: the transposition that exchanges exactly two atoms
a and b and fixes everything else.
-/
@[blueprint "def:swap"
  (title := "Atom swapping")
  (statement := /-- For atoms $x, y$, the transposition $(x\,y)$ is the permutation exchanging $x$
    and $y$ and fixing every other atom; its action $(x\,y) \cdot E$ on an expression $E$ is the
    special case of \cref{def:permutation-action} in which $\pi$ is a transposition, so that
    $(x\,y) \cdot E$ is $E$ with all occurrences of $x$ and $y$ swapped.
    ([Crole2012], Section 2; [Gabbay2002], Section 2.) -/)]
def swap (m : Term Var) (x y : Var) : Term Var := m.permute (Equiv.swap x y)

/-- **Definition 3.2** [Crole2012]: `∼p#` - α-equivalence via permutation with freshness
side condition.

The rule `pi#` uses the freshness condition `z # a, b, E, E'`
(i.e., `z ∉ fv(E) ∪ fv(E') ∪ {a, b}`) instead of the non-occurrence condition
`z ∉ vars(E) ∪ vars(E') ∪ {a, b}` used in Definition 3.1 (`AlphaEquiv`).
-/
@[blueprint "def:alpha-p-fresh"
  (title := "Definition 3.2: the relation $\\sim_{p\\#}$")
  (statement := /-- The binary relation $\sim_{p\#}$ on the set of expressions is inductively
    defined by
    \[ \frac{}{a \sim_{p\#} a}\ \textit{atom} \qquad
       \frac{E_1 \sim_{p\#} E_1' \quad E_2 \sim_{p\#} E_2'}
            {P(E_1,E_2) \sim_{p\#} P(E_1',E_2')}\ \textit{pcg} \qquad
       \frac{(z\,a) \cdot E \sim_{p\#} (z\,b) \cdot E'}
            {B([a]E) \sim_{p\#} B([b]E')}\ \pi\#
       \quad [\, z \mathrel{\#} a, b, E, E' \,] \]
    where the side condition $z \mathrel{\#} a, b, E, E'$ means that $z$ differs from $a$ and $b$
    and has no free occurrence in $E$ or $E'$.
    ([Crole2012], Definition 3.2.) -/)]
inductive AlphaEquivPFresh : Term Var → Term Var → Prop where
  | var {x : Var} : AlphaEquivPFresh (var x) (var x)
  | abs {y x1 x2 : Var} {m1 m2 : Term Var} :
    y ∉ ({x1, x2} : Finset Var) ∪ m1.fv ∪ m2.fv →
    AlphaEquivPFresh (m1.swap x1 y) (m2.swap x2 y) →
    AlphaEquivPFresh (abs x1 m1) (abs x2 m2)
  | app {m1 n1 m2 n2 : Term Var} :
    AlphaEquivPFresh m1 n1 → AlphaEquivPFresh m2 n2 →
    AlphaEquivPFresh (app m1 m2) (app n1 n2)

/-- **Definition 3.3** [Crole2012]: `∼¹p` - α-equivalence via permutation with non-occurrence
restricted to the bodies only.

This definition is analogous to the definition of α-equivalence for λ-expressions in
[Gabbay1999a] (Theorem 2.1, page 216). The notation `∼¹p` arises from three variants `∼ⁱp`
of `∼p` considered in Proposition 4.3 of [Crole2012].
-/
@[blueprint "def:alpha-p1"
  (title := "Definition 3.3: the relation $\\sim^1_p$")
  (statement := /-- The binary relation $\sim^1_p$ on expressions is defined by the rules of
    \cref{def:alpha-p}, but with the rule $\pi$ replaced by
    \[ \frac{(z\,a) \cdot E \sim^1_p (z\,b) \cdot E'}
            {B([a]E) \sim^1_p B([b]E')}\ \pi_1 \quad [\, z \not\vartriangleright E, E' \,] \]
    that is, the witness $z$ is only required not to occur in the two bodies.
    ([Crole2012], Definition 3.3.) -/)]
inductive AlphaEquivP1 : Term Var → Term Var → Prop where
  | var {x : Var} : AlphaEquivP1 (var x) (var x)
  | abs {y x1 x2 m1 m2} :
    y ∉ m1.vars ∪ m2.vars →
    AlphaEquivP1 (m1.rename x1 y) (m2.rename x2 y) →
    AlphaEquivP1 (abs x1 m1) (abs x2 m2)
  | app {m1 n1 m2 n2 : Term Var} :
    AlphaEquivP1 m1 n1 → AlphaEquivP1 m2 n2 →
    AlphaEquivP1 (app m1 m2) (app n1 n2)

/-- The relation `∼²p` from Proposition 4.3:
the `pi2` witness need only differ from the two binding variables. -/
@[blueprint "def:alpha-p2"
  (title := "The relation $\\sim^2_p$ of Proposition 4.3")
  (statement := /-- The binary relation $\sim^2_p$ on expressions is defined by the rules of
    \cref{def:alpha-p}, but with the rule $\pi$ replaced by
    \[ \frac{(z\,a) \cdot E \sim^2_p (z\,b) \cdot E'}
            {B([a]E) \sim^2_p B([b]E')}\ \pi_2 \quad [\, z \not\vartriangleright a, b \,] \]
    that is, the witness $z$ need only differ from the two binding atoms.
    ([Crole2012], Proposition 4.3.) -/)]
inductive AlphaEquivP2 : Term Var → Term Var → Prop where
  | var {x : Var} : AlphaEquivP2 (var x) (var x)
  | abs {z x1 x2 : Var} {m1 m2 : Term Var} :
    z ∉ ({x1, x2} : Finset Var) →
    AlphaEquivP2 (m1.swap z x1) (m2.swap z x2) →
    AlphaEquivP2 (abs x1 m1) (abs x2 m2)
  | app {m1 n1 m2 n2 : Term Var} :
    AlphaEquivP2 m1 n1 → AlphaEquivP2 m2 n2 →
    AlphaEquivP2 (app m1 m2) (app n1 n2)

/-- The relation `∼³p` from Proposition 4.3: the `pi3` rule has no side condition. -/
@[blueprint "def:alpha-p3"
  (title := "The relation $\\sim^3_p$ of Proposition 4.3")
  (statement := /-- The binary relation $\sim^3_p$ on expressions is defined by the rules of
    \cref{def:alpha-p}, but with the rule $\pi$ replaced by
    \[ \frac{(z\,a) \cdot E \sim^3_p (z\,b) \cdot E'}
            {B([a]E) \sim^3_p B([b]E')}\ \pi_3 \]
    which carries no side condition at all.
    ([Crole2012], Proposition 4.3.) -/)]
inductive AlphaEquivP3 : Term Var → Term Var → Prop where
  | var {x : Var} : AlphaEquivP3 (var x) (var x)
  | abs {z x1 x2 : Var} {m1 m2 : Term Var} :
    AlphaEquivP3 (m1.swap z x1) (m2.swap z x2) →
    AlphaEquivP3 (abs x1 m1) (abs x2 m2)
  | app {m1 n1 m2 n2 : Term Var} :
    AlphaEquivP3 m1 n1 → AlphaEquivP3 m2 n2 →
    AlphaEquivP3 (app m1 m2) (app n1 n2)

/-- **Definition 3.4** [Crole2012]: `∼r` - α-equivalence via the traditional renaming axiom
with non-occurrence side condition.

This definition is analogous to the definition of α-equivalence for λ-expressions most commonly
found in the literature. One of the first formal presentations is in [Church1941] and the same,
though rather less formal approach is taken by [Barendregt1985] (Definition 2.1.11).
-/
@[blueprint "def:alpha-r"
  (title := "Definition 3.4: the relation $\\sim_r$")
  (statement := /-- The binary relation $\sim_r$ on expressions is inductively defined by
    \[ \frac{}{E \sim_r E}\ \textit{ref} \qquad
       \frac{E_1 \sim_r E_2}{E_2 \sim_r E_1}\ \textit{sym} \qquad
       \frac{E_1 \sim_r E_2 \quad E_2 \sim_r E_3}{E_1 \sim_r E_3}\ \textit{trs} \]
    \[ \frac{E_1 \sim_r E_1' \quad E_2 \sim_r E_2'}
            {P(E_1,E_2) \sim_r P(E_1',E_2')}\ \textit{pcg} \qquad
       \frac{E \sim_r E'}{B([a]E) \sim_r B([a]E')}\ \textit{bcg} \]
    \[ \frac{}{B([a]E) \sim_r B([a']E\{a'/a\})}\ \alpha
       \quad [\, a' \not\vartriangleright a, E \,] \]
    where $E\{a'/a\}$ is capture-avoiding substitution and the side condition
    $a' \not\vartriangleright a, E$ says that $a'$ differs from $a$ and does not occur at all
    in $E$.
    ([Crole2012], Definition 3.4.) -/)]
inductive AlphaEquivR : Term Var → Term Var → Prop where
  | refl {m : Term Var} : AlphaEquivR m m
  | symm {m1 m2 : Term Var} : AlphaEquivR m1 m2 → AlphaEquivR m2 m1
  | trans {m1 m2 m3 : Term Var} : AlphaEquivR m1 m2 → AlphaEquivR m2 m3 → AlphaEquivR m1 m3
  | app {m1 n1 m2 n2 : Term Var} :
    AlphaEquivR m1 n1 → AlphaEquivR m2 n2 →
    AlphaEquivR (app m1 m2) (app n1 n2)
  | abs_congr {x : Var} {m m' : Term Var} :
    AlphaEquivR m m' →
    AlphaEquivR (abs x m) (abs x m')
  | alpha {x x' : Var} {m : Term Var} :
    x' ∉ ({x} : Finset Var) ∪ m.vars →
    AlphaEquivR (abs x m) (abs x' (m.subst x (var x')))

/-- **Definition 3.5** [Crole2012]: `∼r#` - α-equivalence via the renaming axiom with
freshness side condition.

Same as `∼r` (Definition 3.4), but the renaming axiom uses a freshness side condition
(`a' ∉ {a} ∪ fv(E)`) instead of a non-occurrence condition (`a' ∉ {a} ∪ vars(E)`).

This is analogous to the definition of α-equivalence for λ-expressions one finds in
[Hindley1988] (Section 1B, page 9).
-/
@[blueprint "def:alpha-r-fresh"
  (title := "Definition 3.5: the relation $\\sim_{r\\#}$")
  (statement := /-- The binary relation $\sim_{r\#}$ on expressions is defined by the rules of
    \cref{def:alpha-r}, but with the rule $\alpha$ replaced by
    \[ \frac{}{B([a]E) \sim_{r\#} B([a']E\{a'/a\})}\ \alpha\#
       \quad [\, a' \mathrel{\#} a, E \,] \]
    whose side condition only requires $a'$ to differ from $a$ and to have no \emph{free} occurrence
    in $E$.
    ([Crole2012], Definition 3.5.) -/)]
inductive AlphaEquivRFresh : Term Var → Term Var → Prop where
  | refl {m : Term Var} : AlphaEquivRFresh m m
  | symm {m1 m2 : Term Var} :
    AlphaEquivRFresh m1 m2 → AlphaEquivRFresh m2 m1
  | trans {m1 m2 m3 : Term Var} :
    AlphaEquivRFresh m1 m2 → AlphaEquivRFresh m2 m3 →
    AlphaEquivRFresh m1 m3
  | app {m1 m1' m2 m2' : Term Var} :
    AlphaEquivRFresh m1 m1' → AlphaEquivRFresh m2 m2' →
    AlphaEquivRFresh (app m1 m2) (app m1' m2')
  | abs_congr {x : Var} {m m' : Term Var} :
    AlphaEquivRFresh m m' →
    AlphaEquivRFresh (abs x m) (abs x m')
  | alpha {x x' : Var} {m : Term Var} :
    x' ∉ ({x} : Finset Var) ∪ m.fv →
    AlphaEquivRFresh (abs x m) (abs x' (m.subst x (var x')))

end LambdaCalculus.Named.Untyped.Term

end Cslib
