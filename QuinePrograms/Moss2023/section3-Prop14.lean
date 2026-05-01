import Mathlib
import QuinePrograms.Moss2023.section2_1
import QuinePrograms.Moss2023.section3

/-!
# Proposition 14, alternative proof

This file re-proves `mem_equiv_e_of_isAddOf_of_equiv_e` from section 3,
following the proof of Proposition 14 in Moss (2023) directly:
induction on the number of rewrite steps `n` in a chain `t →ⁿ e`,
case-analysing the first step. No appeal to normal forms is made in
the inductive argument; the only normal-form reasoning enters at the
boundary that converts `t ≡ e` into `t ⟶* e`, exactly as the paper
implicitly does.

The narrative is in three acts:

1. `add_equiv_e_incomplete` -- the most literal rendering of the paper's
   "induction on `n`" template, with `induction n generalizing a b`
   plus a WF self-recursion to handle the `addAssoc` subcase. This
   attempt **fails**: we leave the `decreasing_by` obligation as
   `sorry` and explain why it cannot be discharged.
2. `add_rewN_e_strong` -- the fix. We strengthen the statement so the
   IH is available at *every* chain length `k ≤ N` (a "budget"
   variant) and induct on the budget. This avoids the mismatch that
   sank `add_equiv_e_incomplete`.
3. `add_equiv_e'` -- the two-summand corollary, an immediate
   wrapper around `add_rewN_e_strong`. Proposition 14 itself
   (`mem_equiv_e_of_isAddOf_of_equiv_e'`) follows by induction on
   `IsAddOf`, calling `add_equiv_e'` at the binary `comb` step.
-/

namespace Moss.Section3

open Moss.EquationalLogic

/-! ## Length-indexed rewriting helpers

`RewN` and the conversions `rewN_of_rewriteStar`, `rewN_toEquiv`,
`rewN_to_rewriteStar` come from `section3.lean`. Here we add two
small `RewN`-specific helpers used in the induction step below. -/

theorem RewN.add_left_lift {a a' : Tm Var} (b : Tm Var) :
    ∀ {n : ℕ}, RewN n a a' → RewN n (a + b) (a' + b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      change a = a' at h
      subst h
      rfl
  | succ n ih =>
      intro h
      obtain ⟨v, hstep, hrest⟩ := h
      exact ⟨v + b, Rewrite.add_left hstep, ih hrest⟩

theorem RewN.trans : ∀ {n m : ℕ} {t u v : Tm Var},
    RewN n t u → RewN m u v → RewN (n + m) t v := by
  intro n m
  induction n with
  | zero =>
      intro t u v h₁ h₂
      change t = u at h₁
      subst h₁
      simpa using h₂
  | succ n ih =>
      intro t u v h₁ h₂
      obtain ⟨w, hstep, hrest⟩ := h₁
      rw [Nat.succ_add]
      exact ⟨w, hstep, ih hrest h₂⟩

/-! ## Act 1: a literal "induction on `n`" attempt -- and why it fails

This is the most direct rendering of the paper's "induction on `n`"
template, using **no** strong-induction trick. We do
`induction n generalizing a b` for the chain, and in the `addAssoc`
subcase we self-recurse on `add_equiv_e_incomplete` itself for the inner sum
`σ 1 + σ 2 ≡ e`. Termination of this recursion ought to be witnessed
by the size of the input sum (`(σ 0 + σ 1) + σ 2` strictly contains
`σ 1 + σ 2`).

This attempt **fails**, and the failure is instructive. We leave the
discharging obligation as `sorry` so the obstruction is visible.

* Why natural induction alone is not enough.
  After the step `(σ 0 + σ 1) + σ 2 ⟶ σ 0 + (σ 1 + σ 2)` the IH
  gives `σ 0 ≡ e` and `σ 1 + σ 2 ≡ e`. To finish we need `σ 1 ≡ e`
  and `σ 2 ≡ e` from `σ 1 + σ 2 ≡ e`. The IH expects a `RewN n` chain,
  not an `≡`; converting via `equiv_e_iff_rewriteStar_e` produces some
  `m`, but `m ≤ n` is not known, so the IH does not apply.

* Why WF self-recursion does not patch it.
  Recursing on `add_equiv_e_incomplete` for `σ 1 + σ 2 ≡ e` looks fine --
  that sum is structurally smaller than `(σ 0 + σ 1) + σ 2`. But
  `induction n generalizing a b` reverts and re-introduces `a, b`,
  *decoupling* the locals from the WF recursor's parameters. The
  obligation Lean produces is
    `sizeOf (σ 1 + σ 2) < sizeOf (a✝² + b✝)`
  where `a✝², b✝` are the WF-aux's abstract parameters. There is no
  equation in scope linking `a✝² + b✝` to `(σ 0 + σ 1) + σ 2`, so
  this inequality is **unprovable from the local context**, regardless
  of how cleverly `sizeOf` (or any custom size) is set up.

The take-away: this scope mismatch is intrinsic to mixing two
recursion principles (outer WF + inner `induction _ generalizing _`).
Act 2 fixes it by pre-strengthening the hypothesis so the IH is
available at any chain length. -/

theorem add_equiv_e_incomplete {a b : Tm Var} (h : (a + b) ≡ Tm.e) :
    (a ≡ Tm.e) ∧ (b ≡ Tm.e) := by
  -- Convert to a length-indexed chain.
  obtain ⟨n, hn⟩ := rewN_of_rewriteStar ((equiv_e_iff_rewriteStar_e _).mp h)
  -- Natural induction on `n`, generalizing the summands.
  induction n generalizing a b with
  | zero =>
      exfalso
      change (a + b : Tm Var) = Tm.e at hn
      injection hn with hf
      cases hf
  | succ n IH =>
      obtain ⟨v, hstep, hrest⟩ := hn
      generalize hw : (a + b : Tm Var) = w at hstep
      cases hstep with
      | @step e he σ =>
          rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          -- The four `∘ₐ`-headed axioms are impossible: `w` has `+` at top.
          all_goals try (exfalso; injection hw with hf _; cases hf; done)
          · -- addE
            injection hw with _ h_args
            have h0 := congrFun h_args 0
            have h1 := congrFun h_args 1
            simp only [Fin.isValue, Matrix.cons_val_zero, Tm.vx, Term.subst,
              Matrix.cons_val_one, Matrix.cons_val_fin_one, Tm.e_subst] at h0 h1
            subst h0; subst h1
            have hrest' : RewN n (σ 0) Tm.e := by
              simpa [Ax.addE, Tm.vx] using hrest
            exact ⟨rewN_toEquiv hrest', Equiv.refl _⟩
          · -- eAdd
            injection hw with _ h_args
            have h0 := congrFun h_args 0
            have h1 := congrFun h_args 1
            simp only [Fin.isValue, Matrix.cons_val_zero, Tm.vx, Tm.e_subst,
              Matrix.cons_val_one, Matrix.cons_val_fin_one, Term.subst] at h0 h1
            subst h0; subst h1
            have hrest' : RewN n (σ 0) Tm.e := by
              simpa [Ax.eAdd, Tm.vx] using hrest
            exact ⟨Equiv.refl _, rewN_toEquiv hrest'⟩
          · -- **addAssoc** -- the obstruction lives here.
            injection hw with _ h_args
            have h0 := congrFun h_args 0
            have h1 := congrFun h_args 1
            simp only [Fin.isValue, Matrix.cons_val_zero, Tm.vx, Tm.vy, Tm.vz,
              Term.subst, Matrix.cons_val_one, Matrix.cons_val_fin_one,
              Tm.add_subst] at h0 h1
            subst h0; subst h1
            have hrest' : RewN n (σ 0 + (σ 1 + σ 2)) Tm.e := by
              simpa [Ax.addAssoc, Tm.vx, Tm.vy, Tm.vz] using hrest
            obtain ⟨h_s0, h_sum12⟩ := IH (rewN_toEquiv hrest') hrest'
            -- Self-recursive call. The WF obligation it produces is
            --   `sizeOf (σ 1 + σ 2) < sizeOf (a✝² + b✝)`,
            -- which is **unprovable** -- see the doc-comment above.
            obtain ⟨h_s1, h_s2⟩ := add_equiv_e_incomplete h_sum12
            exact ⟨Equiv.trans (Equiv.addCongr h_s0 h_s1) (Equiv.addE _), h_s2⟩
      | @congr f args i u' hcongr =>
          cases f
          -- `d`/`e`/`app` heads cannot equal `Sym.add`.
          all_goals try (exfalso; injection hw with hf _; cases hf; done)
          -- Only the `add` case remains.
          injection hw with _ h_args
          have hargs_eq : args = ![a, b] := by
            funext j; fin_cases j
            · exact (congrFun h_args 0).symm
            · exact (congrFun h_args 1).symm
          subst hargs_eq
          fin_cases i
          · -- i = 0: a ⟶ u', v = u' + b.
            have hr' : Rewrite a u' := by simpa using hcongr
            have hrest' : RewN n (u' + b) Tm.e := by
              have heq : (Term.func (S := S3) Sym.add
                            (Function.update ![a, b]
                              ((fun i : Fin (S3.arity Sym.add) => i)
                                ⟨0, by decide⟩) u')) = u' + b := by
                change _ = Term.func (S := S3) Sym.add ![u', b]
                congr 1; funext j; fin_cases j <;> rfl
              rw [heq] at hrest; exact hrest
            obtain ⟨h_u', h_b⟩ := IH (rewN_toEquiv hrest') hrest'
            exact ⟨Equiv.trans (Rewrite.toDerivable hr') h_u', h_b⟩
          · -- i = 1: b ⟶ u', v = a + u'.
            have hr' : Rewrite b u' := by simpa using hcongr
            have hrest' : RewN n (a + u') Tm.e := by
              have heq : (Term.func (S := S3) Sym.add
                            (Function.update ![a, b]
                              ((fun i : Fin (S3.arity Sym.add) => i)
                                ⟨1, by decide⟩) u')) = a + u' := by
                change _ = Term.func (S := S3) Sym.add ![a, u']
                congr 1; funext j; fin_cases j <;> rfl
              rw [heq] at hrest; exact hrest
            obtain ⟨h_a, h_u'⟩ := IH (rewN_toEquiv hrest') hrest'
            exact ⟨h_a, Equiv.trans (Rewrite.toDerivable hr') h_u'⟩
termination_by sizeOf (a + b)
decreasing_by
  -- Goal Lean produces here:
  --   `sizeOf (σ 1 + σ 2) < sizeOf (a✝² + b✝)`
  -- where `a✝², b✝` are the WF recursor's parameters and `σ 1, σ 2`
  -- are local terms. There is no hypothesis tying them, so the
  -- inequality cannot be discharged.
  sorry

/-! ## Act 2: the fix -- strong induction with an explicit budget

To get past the obstruction in `add_equiv_e_incomplete`, we package an explicit
"budget" `N` and prove the result for **every** chain length `k ≤ N`,
inducting on `N`. The IH is then available at any sub-budget, so the
`addAssoc` subcase can recurse twice (once on `(σ 0, σ 1 + σ 2)`, then
again on the inner `(σ 1, σ 2)` whose chain length `kp` is bounded by
`k' ≤ N`).

We make the bound on the *output* chain lengths explicit too: from
`RewN n (a + b) e` we get `RewN ka a e` and `RewN kb b e` with
`ka + kb ≤ n`. The bound is what lets the IH apply to the strictly
shorter chains in the `addAssoc` subcase. -/

theorem add_rewN_e_strong :
    ∀ (n : ℕ) {a b : Tm Var}, RewN n (a + b) Tm.e →
      ∃ ka kb, RewN ka a Tm.e ∧ RewN kb b Tm.e ∧ ka + kb ≤ n := by
  -- Strengthen to "for all `k ≤ N`" and induct on `N`.
  suffices aux : ∀ (N : ℕ), ∀ k, k ≤ N → ∀ {a b : Tm Var},
      RewN k (a + b) Tm.e →
      ∃ ka kb, RewN ka a Tm.e ∧ RewN kb b Tm.e ∧ ka + kb ≤ k by
    intro n a b hr
    exact aux n n (le_refl n) hr
  intro N
  induction N with
  | zero =>
      intro k hk a b hr
      have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      exfalso
      change (a + b : Tm Var) = Tm.e at hr
      injection hr with hf
      cases hf
  | succ N IH =>
      intro k hk a b hr
      cases k with
      | zero =>
          exfalso
          change (a + b : Tm Var) = Tm.e at hr
          injection hr with hf
          cases hf
      | succ k' =>
          have hk'N : k' ≤ N := Nat.le_of_succ_le_succ hk
          obtain ⟨v, hstep, hrest⟩ := hr
          generalize hw : (a + b : Tm Var) = w at hstep
          cases hstep with
          | @step e he σ =>
              rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
              -- The four `∘ₐ`-headed axioms are impossible: `w` has `+` at top.
              all_goals try (exfalso; injection hw with hf _; cases hf; done)
              · -- **addE**: `a + b = (σ 0) + e`. So `a = σ 0`, `b = e`.
                injection hw with _ h_args
                have h0 := congrFun h_args 0
                have h1 := congrFun h_args 1
                simp only [Fin.isValue, Matrix.cons_val_zero, Tm.vx, Term.subst,
                  Matrix.cons_val_one, Matrix.cons_val_fin_one, Tm.e_subst] at h0 h1
                subst h0; subst h1
                have hrest' : RewN k' (σ 0) Tm.e := by
                  simpa [Ax.addE, Tm.vx] using hrest
                exact ⟨k', 0, hrest', rfl, by omega⟩
              · -- **eAdd**: `a + b = e + (σ 0)`. So `a = e`, `b = σ 0`.
                injection hw with _ h_args
                have h0 := congrFun h_args 0
                have h1 := congrFun h_args 1
                simp only [Fin.isValue, Matrix.cons_val_zero, Tm.vx, Tm.e_subst,
                  Matrix.cons_val_one, Matrix.cons_val_fin_one, Term.subst] at h0 h1
                subst h0; subst h1
                have hrest' : RewN k' (σ 0) Tm.e := by
                  simpa [Ax.eAdd, Tm.vx] using hrest
                exact ⟨0, k', rfl, hrest', by omega⟩
              · -- **addAssoc**: `a + b = (σ 0 + σ 1) + σ 2`.
                -- So `a = σ 0 + σ 1`, `b = σ 2`. `v = σ 0 + (σ 1 + σ 2)`.
                injection hw with _ h_args
                have h0 := congrFun h_args 0
                have h1 := congrFun h_args 1
                simp only [Fin.isValue, Matrix.cons_val_zero, Tm.vx, Tm.vy, Tm.vz,
                  Term.subst, Matrix.cons_val_one, Matrix.cons_val_fin_one,
                  Tm.add_subst] at h0 h1
                subst h0; subst h1
                have hrest' : RewN k' (σ 0 + (σ 1 + σ 2)) Tm.e := by
                  simpa [Ax.addAssoc, Tm.vx, Tm.vy, Tm.vz] using hrest
                -- IH at `k' ≤ N` on the split `(σ 0, σ 1 + σ 2)`.
                obtain ⟨k₁, kp, hk₁, hkp, hsum₁⟩ := IH k' hk'N hrest'
                -- IH at `kp ≤ N` on the split `(σ 1, σ 2)`.
                have hkpN : kp ≤ N := by omega
                obtain ⟨k₂, k₃, hk₂, hk₃, hsum₂⟩ := IH kp hkpN hkp
                -- Build `RewN (k₁ + 1 + k₂) (σ 0 + σ 1) e`:
                --   `σ 0 + σ 1 →^{k₁} e + σ 1 →¹ σ 1 →^{k₂} e`.
                have stepFull : RewN (k₁ + 1 + k₂) (σ 0 + σ 1) Tm.e :=
                  RewN.trans (RewN.trans (RewN.add_left_lift _ hk₁)
                    (⟨σ 1, Rewrite.eAdd _, rfl⟩ : RewN 1 (Tm.e + σ 1) (σ 1))) hk₂
                exact ⟨k₁ + 1 + k₂, k₃, stepFull, hk₃, by omega⟩
          | @congr f args i u' hcongr =>
              cases f
              -- `d`/`e`/`app` heads cannot equal `Sym.add`.
              all_goals try (exfalso; injection hw with hf _; cases hf; done)
              -- Only the `add` case remains.
              injection hw with _ h_args
              have hargs_eq : args = ![a, b] := by
                funext j; fin_cases j
                · exact (congrFun h_args 0).symm
                · exact (congrFun h_args 1).symm
              subst hargs_eq
              fin_cases i
              · -- `i = 0`: `a ⟶ u'`. `v = u' + b`.
                have hr' : Rewrite a u' := by simpa using hcongr
                have hrest' : RewN k' (u' + b) Tm.e := by
                  have heq : (Term.func (S := S3) Sym.add
                                (Function.update ![a, b]
                                  ((fun i : Fin (S3.arity Sym.add) => i)
                                    ⟨0, by decide⟩) u')) = u' + b := by
                    change _ = Term.func (S := S3) Sym.add ![u', b]
                    congr 1; funext j; fin_cases j <;> rfl
                  rw [heq] at hrest; exact hrest
                obtain ⟨ka', kb, hka', hkb, hsum⟩ := IH k' hk'N hrest'
                exact ⟨ka' + 1, kb, ⟨u', hr', hka'⟩, hkb, by omega⟩
              · -- `i = 1`: `b ⟶ u'`. `v = a + u'`.
                have hr' : Rewrite b u' := by simpa using hcongr
                have hrest' : RewN k' (a + u') Tm.e := by
                  have heq : (Term.func (S := S3) Sym.add
                                (Function.update ![a, b]
                                  ((fun i : Fin (S3.arity Sym.add) => i)
                                    ⟨1, by decide⟩) u')) = a + u' := by
                    change _ = Term.func (S := S3) Sym.add ![a, u']
                    congr 1; funext j; fin_cases j <;> rfl
                  rw [heq] at hrest; exact hrest
                obtain ⟨ka, kb', hka, hkb', hsum⟩ := IH k' hk'N hrest'
                exact ⟨ka, kb' + 1, hka, ⟨u', hr', hkb'⟩, by omega⟩

/-! ## Act 3: the two-summand corollary

`add_equiv_e'` is a one-line wrapper around `add_rewN_e_strong`:
convert the equiv to a chain, apply the strong lemma, convert back. -/

theorem add_equiv_e' {a b : Tm Var} (h : (a + b) ≡ Tm.e) :
    (a ≡ Tm.e) ∧ (b ≡ Tm.e) := by
  obtain ⟨n, hn⟩ := rewN_of_rewriteStar ((equiv_e_iff_rewriteStar_e _).mp h)
  obtain ⟨_, _, hka, hkb, _⟩ := add_rewN_e_strong n hn
  exact ⟨rewN_toEquiv hka, rewN_toEquiv hkb⟩

/-! ## Proposition 14, restated

This is the same statement as `mem_equiv_e_of_isAddOf_of_equiv_e` in
section 3, but the proof now goes through `add_equiv_e'` (induction on
chain length, no normal-form lemma) rather than the normal-form route. -/

theorem mem_equiv_e_of_isAddOf_of_equiv_e' :
    ∀ {t : Tm Var} {us : List (Tm Var)},
      IsAddOf us t → (t ≡ Tm.e) → ∀ u ∈ us, (u ≡ Tm.e) := by
  intro t us hAdd
  induction hAdd with
  | one t' =>
      intro h u hu
      rw [List.mem_singleton.mp hu]
      exact h
  | @comb as bs ta tb _ _ ihAs ihBs =>
      intro h u hu
      have ⟨hta, htb⟩ := add_equiv_e' h
      rcases List.mem_append.mp hu with h_in_as | h_in_bs
      · exact ihAs hta u h_in_as
      · exact ihBs htb u h_in_bs

end Moss.Section3
