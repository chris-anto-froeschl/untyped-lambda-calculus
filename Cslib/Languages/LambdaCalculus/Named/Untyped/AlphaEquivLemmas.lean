/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Architect
public import Cslib.Languages.LambdaCalculus.Named.Untyped.Properties

/-! # The lemmas of Section 6.1 of [Crole2012]

This file formalises the expression lemmas of Section 6.1.

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012], Section 6.1
-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.Named.Untyped.Term

blueprint_comment /-- \section{Lemmas on expressions}

The lemmas of Section 6.1 of [Crole2012], which support the proofs of the equalities of
Section 4. -/

omit [HasFresh Var] in
/-- Lemma 6.2 part 1 [Crole2012]: Permutations on agreement set result in same term. -/
@[blueprint "lem:6-2-1"
  (latexEnv := "lemma")
  (title := "Lemma 6.2(1): permutations agreeing on occurring atoms")
  (statement := /-- For any expression $E$ and permutations $\pi, \pi'$,
    \[ \mathrm{occ}(E) \subseteq AS(\pi, \pi') \implies \pi \cdot E = \pi' \cdot E. \]
    ([Crole2012], Lemma 6.2 part 1.) -/)]
lemma permute_eq_of_vars_subset_agreementSet (m : Term Var) (π π' : Equiv.Perm Var)
  (h : (m.vars : Set Var) ⊆ agreementSet π π') :
  m.permute π = m.permute π' := by
    induction m with
    | var x => simp_all [permute, vars, agreementSet, vars]
    | abs x m ih =>
      have hx : π x = π' x := h (by simp [vars])
      have hm : m.permute π = m.permute π' := ih fun y hy => h (by simp [vars, hy])
      simp [permute, hx, hm]
    | app m n ihm ihn =>
      have hm : m.permute π = m.permute π' := ihm fun y hy => h (by simp [vars, hy])
      have hn : n.permute π = n.permute π' := ihn fun y hy => h (by simp [vars, hy])
      simp [permute, hm, hn]

omit [HasFresh Var] in
/-- Lemma 6.2 part 1 [Crole2012] (specialized): Swaps on non occuring variables result in same
term -/
@[blueprint "lem:6-2-1-swap"
  (latexEnv := "lemma")
  (title := "Lemma 6.2(1) for transpositions")
  (statement := /-- For any expression $E$ and atoms $a, u, z$ with
    $u \not\vartriangleright E$ and $z \not\vartriangleright E$,
    \[ (z\,u) \cdot (u\,a) \cdot E = (z\,a) \cdot E. \]
    This is the instance of \cref{lem:6-2-1} used in [Crole2012] in the proofs of Theorems 4.2
    and 4.4. -/)]
lemma swap_comp_eq_of_not_mem_vars {m : Term Var} {a u z : Var}
  (hu : u ∉ m.vars) (hz : z ∉ m.vars) :
  (m.swap u a).swap z u = m.swap z a := by
    unfold swap
    let π :=  (Equiv.swap z u) * (Equiv.swap u a)
    let π' := Equiv.swap z a
    have h : (m.vars : Set Var) ⊆ agreementSet π π' := by
      intro x hx
      simp only [agreementSet, Set.mem_ofPred_eq, π, π', Equiv.Perm.coe_mul, Function.comp_apply]
      grind
    rw [permute_permute m (Equiv.swap u a) (Equiv.swap z u)]
    exact permute_eq_of_vars_subset_agreementSet m π π' h

/-- Lemma 6.2 part 2 [Crole2012]: Same as 6.1 but wrt free variables and alpha equivalence. -/
@[blueprint "lem:6-2-2"
  (latexEnv := "lemma")
  (title := "Lemma 6.2(2): permutations agreeing on free atoms")
  (statement := /-- For any expression $E$ and permutations $\pi, \pi'$,
    \[ \mathrm{free}(E) \subseteq AS(\pi, \pi') \implies \pi \cdot E \sim_p \pi' \cdot E. \]
    ([Crole2012], Lemma 6.2 part 2.) -/)]
lemma permute_alphaEquiv_of_fv_subset_agreementSet (m : Term Var) (π π' : Equiv.Perm Var)
  (h : (m.fv : Set Var) ⊆ agreementSet π π') :
  (m.permute π) =α (m.permute π') := by
    induction m generalizing π π' with
    | var x =>
      unfold permute
      have hx : π x = π' x := by
        unfold agreementSet at h
        apply h
        unfold fv
        rw [Finset.coe_singleton, Set.mem_singleton_iff]
      rw [hx]
      exact AlphaEquiv.var
    | app m n ihm ihn =>
      have hm : (m.permute π) =α (m.permute π') := by
        apply ihm
        intro x hx
        apply h
        unfold fv
        simp_all
      have hn : (n.permute π) =α (n.permute π') := by
        apply ihn
        intro x hx
        apply h
        unfold fv
        simp_all
      apply AlphaEquiv.app hm hn
    | abs a m ih =>
      let z := HasFresh.fresh ((m.permute π).vars ∪ (m.permute π').vars ∪ {π a, π' a})
      have hz := HasFresh.fresh_notMem ((m.permute π).vars ∪ (m.permute π').vars ∪ {π a, π' a})
      have hzπ : z ∉ (m.permute π).vars := by simp_all [z]
      have hzπ' : z ∉ (m.permute π').vars := by simp_all [z]
      have hbody :
        (m.permute (π.trans (Equiv.swap (π a) z))) =α (m.permute (π'.trans (Equiv.swap (π' a) z)))
        := by
          apply ih
          intro x hx
          simp only [agreementSet, Set.mem_ofPred_eq, Equiv.trans_apply]
          by_cases hxa : x = a
          · simp_all
          · have hagree : π x = π' x := h (by simp [fv, hx, hxa])
            have hπxa : π x ≠ π a := fun he => hxa (π.injective he)
            have hπ'xa : π' x ≠ π' a := fun he => hxa (π'.injective he)
            have hπ'xπa : π' x ≠ π a := by simp_all
            have hπxz : π x ≠ z := by
              intro he
              apply hzπ
              rw [← he, vars_either_fv_or_bv]
              apply Finset.mem_union_left
              rw [permute_fv]
              exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
            have hπ'xz : π' x ≠ z := by simp_all
            simp [Equiv.swap_apply_def, hπ'xa, hπ'xπa, hπ'xz, hagree]
      rw [← permute_trans, ← permute_trans, permute_swap, permute_swap] at hbody
      rw [swap_eq_rename_of_not_mem_vars hzπ, swap_eq_rename_of_not_mem_vars hzπ'] at hbody
      unfold permute
      apply AlphaEquiv.abs (y := z) (by simp_all [z]) hbody

/-- Lemma 6.2 part 2 [Crole2012] (specialized). -/
@[blueprint "lem:6-2-2-swap"
  (latexEnv := "lemma")
  (title := "Lemma 6.2(2) for transpositions")
  (statement := /-- For any expression $E$ and atoms $a, u, z$ with
    $u \mathrel{\#} E$ and $z \mathrel{\#} E$,
    \[ (z\,u) \cdot (u\,a) \cdot E \sim_p (z\,a) \cdot E. \]
    This is the instance of \cref{lem:6-2-2} used in [Crole2012] in the proof of Theorem 4.1. -/)]
lemma swap_comp_alphaEquiv_of_not_mem_fv {m : Term Var} {a u z : Var}
  (hu : u ∉ m.fv) (hz : z ∉ m.fv) :
  ((m.swap u a).swap z u) =α (m.swap z a) := by
    let π := (Equiv.swap u a).trans (Equiv.swap z u)
    let π' := Equiv.swap z a
    have h : (m.fv : Set Var) ⊆ agreementSet π π' := by
      intro x hx
      unfold agreementSet
      rw [Set.mem_ofPred_eq]
      grind
    have h' := permute_alphaEquiv_of_fv_subset_agreementSet m π π' h
    rw [← permute_trans, permute_swap, permute_swap, permute_swap] at h'
    exact h'

/-- Renaming toward a completely fresh variable agrees, up to `∼r`, with capture-avoiding
substitution of that variable.

This is the `rename`-form of the paper's Lemma 6.3. -/
@[blueprint "lem:6-3-rename"
  (latexEnv := "lemma")
  (title := "Lemma 6.3, in naive-renaming form")
  (statement := /-- For any atoms $a, z$ and any expression $E$ with
    $z \not\vartriangleright E$,
    \[ E[a \mapsto z] \sim_r E\{z/a\} \]
    where $E[a \mapsto z]$ is the naive renaming of \cref{def:rename}. This is the form in which
    the induction of Lemma 6.3 of [Crole2012] is carried out here. -/)]
lemma alphaEquivR_rename_subst_var {m : Term Var} {x z : Var} (hz : z ∉ m.vars) :
    AlphaEquivR (m.rename x z) (m.subst x (var z)) := by
  induction m with
  | var y =>
    -- The steps for atoms are easy.
    by_cases hyx : y = x <;> simp [rename, subst, hyx, AlphaEquivR.refl]
  | app m1 m2 ih1 ih2 =>
    -- ... and so are the steps for `P(E₁, E₂)`, by `pcg`.
    simp only [rename, subst]
    apply AlphaEquivR.app (ih1 (by simp_all [vars])) (ih2 (by simp_all [vars]))
  | abs y m ih =>
    have hzy : z ≠ y := by grind [vars]
    by_cases hyx : y = x
    · -- (Case `a = b` of the paper): the binder itself is renamed, and the rule `α` is used.
      subst y
      simp only [rename, subst, reduceIte]
      apply AlphaEquivR.symm
      apply AlphaEquivR.trans (AlphaEquivR.alpha (x' := z) (by grind [vars]))
      apply AlphaEquivR.abs_congr
      exact (ih (by grind [vars])).symm
    · -- (Case `a ≠ b` of the paper): `z ≠ b`, so no capture, and `bcg` applies.
      have hyz : y ≠ z := Ne.symm hzy
      simp only [rename, subst, hyx, reduceIte, fv, hyz, Finset.mem_singleton, not_false_eq_true]
      apply AlphaEquivR.abs_congr
      exact ih (by grind [vars])

/-- Lemma 6.3 [Crole2012]: `z ̸▹ E ⟹ (z a) · E ∼r E{z/a}`. -/
@[blueprint "lem:6-3"
  (latexEnv := "lemma")
  (title := "Lemma 6.3: swapping versus substitution, for $\\sim_r$")
  (statement := /-- For any atoms $a$ and $z$ and any expression $E$,
    \[ z \not\vartriangleright E \implies (z\,a) \cdot E \sim_r E\{z/a\}. \]
    ([Crole2012], Lemma 6.3.) -/)]
lemma alphaEquivR_swap_subst_var {m : Term Var} {a z : Var} (hz : z ∉ m.vars) :
    AlphaEquivR (m.swap z a) (m.subst a (var z)) := by
  rw [swap_comm, swap_eq_rename_of_not_mem_vars hz]
  exact alphaEquivR_rename_subst_var hz

/-- The `rename`-form of the paper's Lemma 6.4: the induction of
`alphaEquivR_rename_subst_var` with every use of the rule `α` replaced by `α#`. -/
@[blueprint "lem:6-4-rename"
  (latexEnv := "lemma")
  (title := "Lemma 6.4, in naive-renaming form")
  (statement := /-- For any atoms $a, z$ and any expression $E$ with
    $z \not\vartriangleright E$,
    \[ E[a \mapsto z] \sim_{r\#} E\{z/a\}. \]
    This is \cref{lem:6-3-rename} with every use of the rule $\alpha$ replaced by $\alpha\#$. -/)]
lemma alphaEquivRFresh_rename_subst_var {m : Term Var} {x z : Var}
    (hz : z ∉ m.vars) :
    AlphaEquivRFresh (m.rename x z) (m.subst x (var z)) := by
  induction m with
  | var y =>
    by_cases hyx : y = x <;> simp [rename, subst, hyx, AlphaEquivRFresh.refl]
  | app m1 m1 ih1 ih2 =>
    simp only [rename, subst]
    apply AlphaEquivRFresh.app
    · exact ih1 (by grind [vars])
    · exact ih2 (by grind [vars])
  | abs y m ih =>
    have hzy : z ≠ y := by grind [vars]
    by_cases hyx : y = x
    · -- The only step of the induction that uses `α`; here `α#` is used instead, which is
      -- legitimate because `z ̸▹ E` implies `z # E`.
      subst y
      simp only [rename, subst, reduceIte]
      apply AlphaEquivRFresh.symm
      apply AlphaEquivRFresh.trans
        (AlphaEquivRFresh.alpha (x' := z) (by grind [vars, vars_either_fv_or_bv]))
      apply AlphaEquivRFresh.abs_congr
      exact (ih (by grind [vars])).symm
    · have hyz : y ≠ z := Ne.symm hzy
      simp only [rename, subst, hyx, reduceIte, fv, hyz, Finset.mem_singleton, not_false_eq_true]
      apply AlphaEquivRFresh.abs_congr
      exact ih (by grind [vars])

/-- Lemma 6.4 [Crole2012]: `z ̸▹ E ⟹ (z a) · E ∼r# E{z/a}`. -/
@[blueprint "lem:6-4"
  (latexEnv := "lemma")
  (title := "Lemma 6.4: swapping versus substitution, for $\\sim_{r\\#}$")
  (statement := /-- For any atoms $a$ and $z$ and any expression $E$,
    \[ z \not\vartriangleright E \implies (z\,a) \cdot E \sim_{r\#} E\{z/a\}. \]
    ([Crole2012], Lemma 6.4.) -/)]
lemma alphaEquivRFresh_swap_subst_var {m : Term Var} {a z : Var} (hz : z ∉ m.vars) :
    AlphaEquivRFresh (m.swap z a) (m.subst a (var z)) := by
  rw [swap_comm, swap_eq_rename_of_not_mem_vars hz]
  exact alphaEquivRFresh_rename_subst_var hz

/-- Lemma 6.6 [Crole2012]: We can always re-name bound atoms so that a particular atom does not
occur. -/
@[blueprint "lem:6-6"
  (latexEnv := "lemma")
  (title := "Lemma 6.6: avoiding an atom, for $\\sim_r$")
  (statement := /-- For all expressions $E$ and atoms $a$,
    \[ a \mathrel{\#} E \implies (\exists \hat{E})\,
       (a \not\vartriangleright \hat{E} \wedge \hat{E} \sim_r E). \]
    Informally, bound atoms can always be renamed so that a particular atom does not occur; this
    may be regarded as a form of Barendregt's variable convention.
    ([Crole2012], Lemma 6.6.) -/)]
lemma alphaEquivR_avoid_var {m : Term Var} {a : Var} (ha : a ∉ m.fv) :
    ∃ m', a ∉ m'.vars ∧ AlphaEquivR m' m := by
  induction m with
  | var y => exact ⟨var y, by simp_all [vars, fv], AlphaEquivR.refl⟩
  | app m1 m2 ih1 ih2 =>
    obtain ⟨n1, hn1, he1⟩ := ih1 (by simp_all [fv])
    obtain ⟨n2, hn2, he2⟩ := ih2 (by simp_all [fv])
    exact ⟨app n1 n2, by simp_all [vars], AlphaEquivR.app he1 he2⟩
  | abs y E ih =>
    by_cases hay : a = y
    · -- The paper's case `a = b`: pick `z ̸▹ a, E` and use `B([a]E) ∼r B([z]E{z/a})`.
      -- Renaming the binder `a` also renames every occurrence of `a` in the body, so a
      -- single step suffices and no appeal to the induction hypothesis is needed.
      subst hay
      obtain ⟨z, hz⟩ := HasFresh.fresh_exists (E.vars ∪ {a})
      have hzE : z ∉ E.vars := by simp_all
      have haz : a ≠ z := by grind
      use abs z (E.rename a z)
      split_ands
      · have hanin := rename_remove (m := E) (x := a) (y := z) haz
        simp_all [vars]
      · have halpha : AlphaEquivR (abs a E) (abs z (E.subst a (var z))) :=
          AlphaEquivR.alpha (by simp_all)
        have hren : AlphaEquivR (E.rename a z) (E.subst a (var z)) :=
          alphaEquivR_rename_subst_var hzE
        exact (AlphaEquivR.abs_congr hren).trans halpha.symm
    · -- The paper's case `a ̸▹ free(E)`, which "is easy": the induction hypothesis applies.
      obtain ⟨E', hE', he⟩ := ih (by simp_all [fv])
      exact ⟨abs y E', by grind [vars], AlphaEquivR.abs_congr he⟩

/-- Lemma 6.6 [Crole2012] for `∼p`. The proof is almost a exact copy `alphaEquivR_avoid_var`
This is not derivable from Theorem 4.4 since its argument depends on it
- resulting in a cycle if done so. -/
@[blueprint "lem:6-6-p"
  (latexEnv := "lemma")
  (title := "Lemma 6.6 for $\\sim_p$")
  (statement := /-- For all expressions $E$ and atoms $a$,
    \[ a \mathrel{\#} E \implies (\exists \hat{E})\,
       (a \not\vartriangleright \hat{E} \wedge \hat{E} \sim_p E). \]
    This is \cref{lem:6-6} with $\sim_r$ replaced by $\sim_p$. It cannot be obtained from
    \cref{lem:6-6} through Theorem 4.4, because the proof of that theorem uses this statement. -/)]
lemma alphaEquiv_avoid_var {m : Term Var} {a : Var} (ha : a ∉ m.fv) :
    ∃ m', a ∉ m'.vars ∧ m' =α m := by
  induction m with
  | var y => exact ⟨var y, by simp_all [vars, fv], AlphaEquiv.refl _⟩
  | app m1 m2 ih1 ih2 =>
    obtain ⟨n1, hn1, he1⟩ := ih1 (by simp_all [fv])
    obtain ⟨n2, hn2, he2⟩ := ih2 (by simp_all [fv])
    exact ⟨app n1 n2, by simp_all [vars], AlphaEquiv.app he1 he2⟩
  | abs y E ih =>
    by_cases hay : a = y
    · -- The paper's case `a = b`: renaming the binder `a` to a completely fresh `z` renames
      -- every occurrence of `a`, so no appeal to the induction hypothesis is needed.
      subst hay
      obtain ⟨z, hz⟩ := HasFresh.fresh_exists (E.vars ∪ {a})
      have hzE : z ∉ E.vars := by simp_all
      have haz : a ≠ z := by grind
      use abs z (E.rename a z)
      split_ands
      · have hanin := rename_remove (m := E) (x := a) (y := z) haz
        simp_all [vars]
      · apply AlphaEquiv.symm
        apply AlphaEquiv.abs_rename hz
    · obtain ⟨E', hE', he⟩ := ih (by simp_all [fv])
      exact ⟨abs y E', by simp_all [vars], AlphaEquiv.abs_congr he⟩

/-- The `∼p`-form of Lemma 6.3, in `rename` shape.

Same induction as `alphaEquivR_rename_subst_var`, with the rule `α` replaced
by `AlphaEquiv.abs_rename`. -/
@[blueprint "lem:6-3-p"
  (latexEnv := "lemma")
  (title := "Lemma 6.3 for $\\sim_p$, in naive-renaming form")
  (statement := /-- For any atoms $a, a'$ and any expression $E$ with
    $a' \not\vartriangleright E$,
    \[ E[a \mapsto a'] \sim_p E\{a'/a\}. \]
    This is \cref{lem:6-3-rename} with $\sim_r$ replaced by $\sim_p$. -/)]
lemma rename_alphaEquiv_subst_var {m : Term Var} {x x' : Var} (hx' : x' ∉ m.vars) :
    (m.rename x x') =α (m.subst x (var x')) := by
  induction m with
  | var y =>
    by_cases hyx : y = x <;> simpa only [rename, subst, hyx, reduceIte] using AlphaEquiv.refl _
  | app m1 m2 ih1 ih2 =>
    simp only [rename, subst]
    exact AlphaEquiv.app (ih1 (by grind [vars])) (ih2 (by grind [vars]))
  | abs y m ih =>
    have hx'y : x' ≠ y := by simp_all [vars]
    by_cases hyx : y = x
    · -- The binder is the substituted atom: on the right the substitution is shadowed, on the
      -- left the binder is renamed, and the two are related by a single α-renaming.
      subst y
      simp only [rename, subst, reduceIte]
      exact (AlphaEquiv.abs_rename (by simp_all [vars])).symm
    · have hyx' : y ≠ x' := Ne.symm hx'y
      simp only [rename, subst, hyx, reduceIte, fv, hyx', Finset.mem_singleton, not_false_eq_true]
      exact AlphaEquiv.abs_congr (ih (by simp_all [vars]))

/-- First half of Lemma 6.5: substituting an atom which is merely *fresh* for `m` is,
up to `∼p`, the same as transposing it with the substituted atom. -/
@[blueprint "lem:6-5-subst-swap"
  (latexEnv := "lemma")
  (title := "Substituting a fresh atom is a transposition")
  (statement := /-- For any expression $E$ and atoms $a, a'$ with $a' \mathrel{\#} E$,
    \[ E\{a'/a\} \sim_p (a\,a') \cdot E. \]
    This is the first of the two ingredients of \cref{lem:6-5}: note that $a'$ is only required
    to be fresh for $E$, bound occurrences being renamed away first using
    \cref{lem:6-6-p}. -/)]
lemma subst_var_alphaEquiv_swap {m : Term Var} {a a' : Var} (ha' : a' ∉ m.fv) :
    (m[a := var a']) =α (m.swap a a') := by
  -- Use Lemma 6.6
  obtain ⟨n, hn, hnm⟩ := alphaEquiv_avoid_var ha'
  have h1 : (m[a := var a']) =α (n[a := var a']) :=
    subst.preserve_AlphaEquiv hnm.symm (AlphaEquiv.refl _)
  -- Use Lemma 6.3: substitution is renaming, and renaming is the transposition.
  have h2 : (n[a := var a']) =α (n.swap a a') := by
    rw [swap_eq_rename_of_not_mem_vars hn]
    exact (rename_alphaEquiv_subst_var hn).symm
  exact (h1.trans h2).trans (AlphaEquiv.swap_preserve hnm)

/-- Second half of Lemma 6.5: if `z` and `a'` are fresh

for `m`, then the transpositions `(z a)` and `(z a')(a a')` agree on `free(E)` — both send `a`
to `z` and fix every other free atom — so by Lemma 6.2(2) they act alike up to `∼p`. -/
@[blueprint "lem:6-5-swap-swap"
  (latexEnv := "lemma")
  (title := "Splitting a transposition through a fresh atom")
  (statement := /-- For any expression $E$ and atoms $z, a, a'$ with $z \mathrel{\#} E$ and
    $a' \mathrel{\#} E$,
    \[ (z\,a) \cdot E \sim_p (z\,a') \cdot (a\,a') \cdot E. \]
    This is the second ingredient of \cref{lem:6-5}: the two permutations agree on
    $\mathrm{free}(E)$, so \cref{lem:6-2-2} applies. -/)]
lemma swap_alphaEquiv_swap_swap {m : Term Var} {z a a' : Var}
    (hz : z ∉ m.fv) (ha' : a' ∉ m.fv) :
    (m.swap z a) =α ((m.swap a a').swap z a') := by
  unfold swap
  rw [permute_permute]
  apply permute_alphaEquiv_of_fv_subset_agreementSet m
  intro x hx
  rw [Finset.mem_coe] at hx
  unfold agreementSet
  aesop

/-- `swapChain [(z₁, a₁, a'₁), ..., (zₙ, aₙ, a'ₙ)] E` is `(z₁ a₁) · ... · (zₙ aₙ) · E`;
the head of the list carries the outermost swap. -/
@[blueprint "def:swap-chain"
  (title := "Chain of transpositions")
  (statement := /-- Given a finite list of triples of atoms $(z_1, a_1, a_1'), \dots,
    (z_n, a_n, a_n')$ and an expression $E$, the expression
    \[ (z_1\,a_1) \cdot \ldots \cdot (z_n\,a_n) \cdot E \]
    which is the left-hand side of \cref{lem:6-5}. -/)]
def swapChain : List (Var × Var × Var) → Term Var → Term Var
  | [], m => m
  | (z, a, _) :: L, m => (swapChain L m).swap z a

/-- `substSwapChain [(z₁, a₁, a'₁), ..., (zₙ, aₙ, a'ₙ)] E` is
`(z₁ a'₁) · ... · (zₙ a'ₙ) · E{a'₁/a₁} ... {a'ₙ/aₙ}`:
the head of the list carries the outermost swap and the innermost substitution. -/
@[blueprint "def:subst-swap-chain"
  (title := "Chain of transpositions after a chain of substitutions")
  (statement := /-- Given a finite list of triples of atoms $(z_1, a_1, a_1'), \dots,
    (z_n, a_n, a_n')$ and an expression $E$, the expression
    \[ (z_1\,a_1') \cdot \ldots \cdot (z_n\,a_n') \cdot
       E\{a_1'/a_1\} \ldots \{a_n'/a_n\} \]
    which is the right-hand side of \cref{lem:6-5}. -/)]
def substSwapChain : List (Var × Var × Var) → Term Var → Term Var
  | [], m => m
  | (z, a, a') :: L, m => (substSwapChain L (m.subst a (var a'))).swap z a'

/-- The atoms mentioned by a list of triples. -/
@[blueprint "def:chain-atoms"
  (title := "Atoms of a chain")
  (statement := /-- The list of all atoms $z_i, a_i, a_i'$ mentioned by a list of triples
    $(z_1, a_1, a_1'), \dots, (z_n, a_n, a_n')$. Its being repetition-free is the
    pairwise-disjointness hypothesis of \cref{lem:6-5}. -/)]
def chainAtoms (L : List (Var × Var × Var)) : List Var :=
  L.flatMap fun t => [t.1, t.2.1, t.2.2]

omit [DecidableEq Var] [HasFresh Var] in
/-- Every component of a triple in the list is one of the atoms of the list. -/
lemma mem_chainAtoms {L : List (Var × Var × Var)} {t : Var × Var × Var} (ht : t ∈ L) :
    t.1 ∈ chainAtoms L ∧ t.2.1 ∈ chainAtoms L ∧ t.2.2 ∈ chainAtoms L := by
  split_ands <;> exact List.mem_flatMap.mpr ⟨t, ht, by simp⟩

omit [HasFresh Var] in
/-- Chains of swaps preserve α-equivalence (an iterated application of Lemma 6.1). -/
lemma swapChain_congr (L : List (Var × Var × Var)) {m n : Term Var} (h : m =α n) :
    (swapChain L m) =α (swapChain L n) := by
  induction L with
  | nil => exact h
  | cons t T ih => exact AlphaEquiv.swap_preserve ih

/-- Chains of substitutions followed by swaps preserve α-equivalence. -/
lemma substSwapChain_congr (L : List (Var × Var × Var)) {m n : Term Var} (h : m =α n) :
    (substSwapChain L m) =α (substSwapChain L n) := by
  induction L generalizing m n with
  | nil => exact h
  | cons t T ih =>
    exact AlphaEquiv.swap_preserve (ih (subst.preserve_AlphaEquiv h (AlphaEquiv.refl _)))

omit [HasFresh Var] in
/-- Two transpositions with disjoint supports commute in their action on terms. -/
lemma swap_swap_comm {m : Term Var} {z a u v : Var}
    (huz : u ≠ z) (hua : u ≠ a) (hvz : v ≠ z) (hva : v ≠ a) :
    (m.swap z a).swap u v = (m.swap u v).swap z a := by
  unfold swap
  rw [permute_permute, permute_permute]
  congr 1
  ext x
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  grind

omit [HasFresh Var] in
/-- A swap by atoms which the chain does not mention may be pushed through the chain. -/
lemma swapChain_swap_comm {u v : Var}
    (L : List (Var × Var × Var)) (m : Term Var) (hu : u ∉ chainAtoms L) (hv : v ∉ chainAtoms L) :
    (swapChain L m).swap u v = swapChain L (m.swap u v) := by
  induction L with
  | nil => rfl
  | cons t T ih =>
    obtain ⟨z, a, a'⟩ := t
    simp only [chainAtoms, List.flatMap_cons, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at hu hv
    change ((swapChain T m).swap z a).swap u v = (swapChain T (m.swap u v)).swap z a
    rw [swap_swap_comm hu.1.1 hu.1.2.1 hv.1.1 hv.1.2.1, ih hu.2 hv.2]

/-- Lemma 6.5 [Crole2012].

The paper's hypotheses `zᵢ ̸▹ E` are weakened here to `zᵢ # E`.

Intuitively: nothing in this proof ever looks at the bound atoms of `E`.

The two facts it is assembled from are both invariant under `∼p` and mention only free atoms:
- substituting a fresh atom is a transposition (`subst_var_alphaEquiv_swap`),
- and two permutations that agree on `free(E)` act alike
  (`swap_alphaEquiv_swap_swap`, i.e. Lemma 6.2(2)).
A bound occurrence of `zᵢ` is therefore harmless: it can always be renamed away first (Lemma 6.6),
which is exactly what `subst_var_alphaEquiv_swap` does internally.

The paper needs `zᵢ ̸▹ E` because it argues with the substitution itself, where a
bound `zᵢ` would be captured. -/
@[blueprint "lem:6-5"
  (latexEnv := "lemma")
  (title := "Lemma 6.5: chains of transpositions versus chains of substitutions")
  (statement := /-- Let the atoms $z_i, a_i, a_i'$ be pairwise disjoint across all $i$. Then for
    every expression $E$ with $z_i \mathrel{\#} E$ and $a_i' \mathrel{\#} E$ for all $i$,
    \[ (z_1\,a_1) \cdot \ldots \cdot (z_n\,a_n) \cdot E \sim_p
       (z_1\,a_1') \cdot \ldots \cdot (z_n\,a_n') \cdot
       E\{a_1'/a_1\} \ldots \{a_n'/a_n\}. \]
    ([Crole2012], Lemma 6.5.) The hypotheses $z_i \not\vartriangleright E$ of the paper are
    weakened here to $z_i \mathrel{\#} E$, which suffices because both ingredients of the proof
    are invariant under $\sim_p$ and mention only free atoms. -/)]
theorem alphaEquiv_swapChain (L : List (Var × Var × Var)) (m : Term Var)
    -- zᵢ ≠ aᵢ and zᵢ ≠ aᵢ'
    (hnd : (chainAtoms L).Nodup)
    -- zᵢ # E (implicity zᵢ,  # aᵢ, aᵢ', E via above inequality)
    (hz : ∀ t ∈ L, t.1 ∉ m.fv)
    -- aᵢ' # E
    (ha' : ∀ t ∈ L, t.2.2 ∉ m.fv) :
    (swapChain L m) =α (substSwapChain L m) := by
  induction L generalizing m with
  | nil => exact AlphaEquiv.refl _
  | cons t T ih =>
    obtain ⟨z, a, a'⟩ := t
    have hconv : chainAtoms ((z, a, a') :: T) = z :: a :: a' :: chainAtoms T := List.toList_toArray
    rw [hconv] at hnd
    simp only [List.nodup_cons, List.mem_cons] at hnd
    obtain ⟨h1, h2, h3, hndT⟩ := hnd
    have hzT : z ∉ chainAtoms T := by simp_all
    have haT : a ∉ chainAtoms T := by simp_all
    have hzm : z ∉ m.fv := hz (z, a, a') (by simp)
    have ha'm : a' ∉ m.fv := ha' (z, a, a') (by simp)
    -- The head substitution is a transposition, up to `∼p`.
    have hsub : (m[a := var a']) =α (m.swap a a') := subst_var_alphaEquiv_swap ha'm
    -- The remaining atoms are still fresh for the transposed term, so the induction hypothesis
    -- applies to it.
    have hIH : (swapChain T (m.swap a a')) =α (substSwapChain T (m.swap a a')) := by
      apply ih (m.swap a a') hndT
      · intro s hs
        have hs_atoms : s.1 ∈ chainAtoms T := (mem_chainAtoms hs).1
        have hsa : s.1 ≠ a := by
          intro h
          subst a
          exact haT hs_atoms
        have hsa' : s.1 ≠ a' := by
          intro h
          subst a'
          exact h3 hs_atoms
        have hsm : s.1 ∉ m.fv := by
          apply hz s
          exact List.mem_cons_of_mem _ hs
        exact fresh_swap hsa hsa' hsm
      · intro s hs
        have hs_atoms : s.2.2 ∈ chainAtoms T := (mem_chainAtoms hs).2.2
        have hsa : s.2.2 ≠ a := by
          intro h
          subst a
          exact haT hs_atoms
        have hsa' : s.2.2 ≠ a' := by
          intro h
          subst a'
          exact h3 hs_atoms
        have hsm : s.2.2 ∉ m.fv := by
          apply ha' s
          exact List.mem_cons_of_mem _ hs
        exact fresh_swap hsa hsa' hsm
    -- Both head swaps commute past the rest of the chain, ...
    have e1 : (swapChain T m).swap z a = swapChain T (m.swap z a) :=
      swapChain_swap_comm T m hzT haT
    have e2 : (swapChain T (m.swap a a')).swap z a' = swapChain T ((m.swap a a').swap z a') :=
      swapChain_swap_comm T _ hzT h3
    -- ... and between them sits the permutation identity `(z a) ∼ (z a')(a a')` on `free(E)`.
    have core : (swapChain T (m.swap z a)) =α (swapChain T ((m.swap a a').swap z a')) :=
      swapChain_congr T (swap_alphaEquiv_swap_swap hzm ha'm)
    have tail : ((swapChain T (m.swap a a')).swap z a')
        =α ((substSwapChain T (m[a := var a'])).swap z a') :=
      (AlphaEquiv.swap_preserve hIH).trans
        (AlphaEquiv.swap_preserve (substSwapChain_congr T hsub.symm))
    change ((swapChain T m).swap z a) =α ((substSwapChain T (m[a := var a'])).swap z a')
    rw [e1]
    rw [e2] at tail
    exact core.trans tail

/-- The one-variable case of Lemma 6.5 [Crole2012] (`n = 1` of `alphaEquiv_swapChain`).

This is the step which the paper carries out inside the proof of Theorem 4.4 for the rule `α`. -/
@[blueprint "lem:6-5-one"
  (latexEnv := "lemma")
  (title := "Lemma 6.5 for a single triple of atoms")
  (statement := /-- For any expression $E$ and atoms $z, a, a'$ with
    $z \not\vartriangleright E$, $z \neq a$, $a \neq a'$ and $a' \mathrel{\#} E$,
    \[ (z\,a) \cdot E \sim_p (z\,a') \cdot E\{a'/a\}. \]
    This is the case $n = 1$ of \cref{lem:6-5}, which is the step carried out in [Crole2012]
    inside the proof of Theorem 4.4 for the rule $\alpha$. -/)]
lemma alphaEquiv_swap_subst_var {m : Term Var} {z a a' : Var}
    (hz : z ∉ m.vars) (hza : z ≠ a) (haa' : a ≠ a') (ha' : a' ∉ m.fv) :
    (m.swap z a) =α ((m[a := var a']).swap z a') := by
  have hzfv : z ∉ m.fv := by simp_all [vars_either_fv_or_bv]
  by_cases hza' : z = a'
  · -- Degenerate case: the swap on the right is the identity and only Lemma 6.3 is left.
    subst hza'
    rw [swap_self, swap_comm]
    exact (subst_var_alphaEquiv_swap ha').symm
  · exact alphaEquiv_swapChain [(z, a, a')] m
      (by simp [chainAtoms, hza, haa', hza']) (by simp_all) (by simpa using ha')

end LambdaCalculus.Named.Untyped.Term

end Cslib
