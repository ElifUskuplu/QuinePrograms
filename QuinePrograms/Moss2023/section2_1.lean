import Mathlib

/-!
# §2.1: Equational logic, term rewriting, and computable algebras

The paper's §2.1 sets up equational logic and term rewriting "very
shortly" (p. 4). It introduces equational provability `t ≡ u`, the
notion of orienting a set of equations as a rewriting system, and
states Theorem 2: if `E` is a finite set of equations that can be
oriented to give a *terminating and confluent* rewriting system,
then every term has a unique normal form `nf t`, and `t ≡ u` iff
`nf t = nf u` (citing Meseguer–Goguen 1985, Thm. 51).

This file develops the same framework in Lean. We define:

* `Signature`, `Term`, and substitution (the carrier of the
  equational logic);
* equational derivability `Derivable E t u`, written `t ≡[E] u`,
  with constructors `ax`, `refl`, `symm`, `trans`, and `congr`;
* oriented one-step rewriting `Rewrite E t u`, its reflexive-
  transitive closure `RewriteStar E t u`, and the predicates
  `IsNormalForm`, `Terminating`, `Confluent`.

The Lean `Derivable.ax` constructor takes a substituted instance of
an axiom, fusing the paper's "axiom" and "substitution" rules into
one. The main result of the file, `derivable_iff_nf_eq`, is exactly
Theorem 2, proved via existence (termination), uniqueness
(confluence), and joinability of derivable equations.

The paper also cites Theorem 3 (Perkins) , undecidability of the
word problem in general , as a contrast; we do not formalise it
here. -/

namespace Moss.EquationalLogic

/-! ## Signatures, terms, and substitution

A `Signature` is a set of function symbols with arities. A `Term`
over a signature `S` and a variable type `V` is either a variable
or a function-symbol applied to the right number of subterms.
Substitution `t.subst σ` plugs each variable through `σ`. An
`Equation` is just an ordered pair of terms , orientation
(`lhs → rhs` vs. `rhs → lhs`) is supplied later by the rewriting
system. -/

structure Signature where
  Symbol : Type
  arity  : Symbol → Nat

inductive Term (S : Signature) (V : Type) : Type where
  | var  (v : V) : Term S V
  | func (f : S.Symbol) (args : Fin (S.arity f) → Term S V) : Term S V

namespace Term
variable {S : Signature} {V W : Type}

@[simp] def subst (σ : V → Term S W) : Term S V → Term S W
  | var v       => σ v
  | func f args => func f (fun i => (args i).subst σ)

end Term

structure Equation (S : Signature) (V : Type) where
  lhs : Term S V
  rhs : Term S V

variable {S : Signature} {V : Type}

/-! ## Equational derivability `t ≡[E] u`

The paper writes (p. 4): "We write `t ≡ u` if `E ⊢ t = u` using `E`
and the inference rules of equational logic. These rules are the
reflexive, symmetric, and transitive properties of equality,
substitution, and congruence for all function symbols." We bake
substitution into the `ax` constructor: every substituted instance
of an `E`-axiom is a derivable equation. The remaining four
constructors are the obvious closure properties. -/

inductive Derivable (E : Set (Equation S V)) : Term S V → Term S V → Prop
  | ax     {e : Equation S V} (he : e ∈ E) (σ : V → Term S V) :
      Derivable E (e.lhs.subst σ) (e.rhs.subst σ)
  | refl   (t : Term S V) : Derivable E t t
  | symm   {t u : Term S V} :
      Derivable E t u → Derivable E u t
  | trans  {t u v : Term S V} :
      Derivable E t u → Derivable E u v → Derivable E t v
  | congr  (f : S.Symbol) {a₁ a₂ : Fin (S.arity f) → Term S V} :
      (∀ i, Derivable E (a₁ i) (a₂ i)) →
      Derivable E (.func f a₁) (.func f a₂)

scoped notation:50 t " ≡[" E "] " u => Derivable E t u

/-! ## Oriented one-step rewriting

The paper: "An *orientation of an equation* is a declaration that
one of the two sides is the *left* and the other is the *right*,
and in a term rewriting system with an oriented set of equations,
one has to use the equations in the 'left to right' way." (p. 4)

We model a single rewrite step `Rewrite E t u` as either an axiom
firing (`step`) or a rewrite at one argument position of a
function symbol (`congr`). Reflexive-transitive closure gives
`RewriteStar E t u`, abbreviated `t →* u`. A term `t` is in
*normal form* if no rewrite fires on it; the system is *terminating*
if the inverse rewrite relation is well-founded, and *confluent* if
any two divergent rewrites can be joined. -/

inductive Rewrite (E : Set (Equation S V)) : Term S V → Term S V → Prop
  | step  {e : Equation S V} (he : e ∈ E) (σ : V → Term S V) :
      Rewrite E (e.lhs.subst σ) (e.rhs.subst σ)
  | congr (f : S.Symbol) (args : Fin (S.arity f) → Term S V)
          (i : Fin (S.arity f)) {t : Term S V} :
      Rewrite E (args i) t →
      Rewrite E (.func f args) (.func f (Function.update args i t))

def RewriteStar (E : Set (Equation S V)) : Term S V → Term S V → Prop :=
  Relation.ReflTransGen (Rewrite E)

def IsNormalForm (E : Set (Equation S V)) (t : Term S V) : Prop :=
  ∀ u, ¬ Rewrite E t u

/-- Convenience lemma for normal-formhood of constants (arity-0 symbols):
    when `f` has arity 0, the `congr` step is vacuous (no argument positions),
    so the only possible redex is an axiom instance whose `lhs` starts with
    `f`. Used in §3.3 to show `Tm.e` and `Tm.d` are normal forms in one line,
    there it suffices to check that no axiom's `lhs` matches the head symbol. -/
lemma IsNormalForm.of_arity_zero {E : Set (Equation S V)}
    {f : S.Symbol} (args : Fin (S.arity f) → Term S V)
    (h_ar : S.arity f = 0)
    (h_no_redex : ∀ e ∈ E, ∀ σ : V → Term S V,
                  e.lhs.subst σ ≠ Term.func f args) :
    IsNormalForm E (Term.func f args) := by
  intro u hu
  generalize hw : (Term.func f args : Term S V) = w at hu
  cases hu with
  | step he σ => exact (h_no_redex _ he σ hw.symm).elim
  | congr g args' i _ =>
      injection hw with hg _
      subst hg
      exact (h_ar ▸ i).elim0

def Terminating (E : Set (Equation S V)) : Prop :=
  WellFounded (fun u t => Rewrite E t u)

def Confluent (E : Set (Equation S V)) : Prop :=
  ∀ {t u v : Term S V}, RewriteStar E t u → RewriteStar E t v →
    ∃ w, RewriteStar E u w ∧ RewriteStar E v w

/-! ## Soundness: rewriting is contained in derivability

Every rewrite step (and hence every rewrite chain) is in particular
an equational derivation. The paper takes this for granted; we
record it explicitly because the main theorem of the file flows
from `RewriteStar` to `Derivable` and back. -/

theorem Rewrite.toDerivable {E : Set (Equation S V)} :
    ∀ {t u : Term S V}, Rewrite E t u → Derivable E t u := by
  intro t u h
  induction h with
  | step he σ => exact Derivable.ax he σ
  | congr f args i _ ih =>
      apply Derivable.congr f
      intro j
      rcases eq_or_ne j i with rfl | hij
      · simp only [Function.update_self]; exact ih
      · simp only [Function.update_of_ne hij]; exact .refl _

theorem RewriteStar.toDerivable {E : Set (Equation S V)} :
    ∀ {t u : Term S V}, RewriteStar E t u → Derivable E t u := by
  intro t u h
  induction h with
  | refl => exact .refl _
  | tail _ hr ih => exact .trans ih hr.toDerivable

/-! ## Theorem 2: unique normal forms

The paper (p. 5): "Suppose that `E` is a finite set of equations
which can be oriented to give a term rewrite system *which is*
terminating *and* confluent. Then every term `t` has a unique
normal form `nf(t)`. Moreover, we have `t ≡ u iff nf(t) = nf(u)`."

We split the proof into three pieces:

* termination yields *existence* of a normal form, by well-founded
  recursion on the rewrite relation;
* confluence yields *uniqueness* , two rewrite-paths from `t` to
  normal forms can be joined, and a normal form rewrites only to
  itself;
* confluence again yields *joinability* of derivable equations:
  every derivable equation `t ≡ u` admits a common reduct.
  Combined with uniqueness this gives `t ≡ u ↔ nf t = nf u`.

Two helper lemmas about `RewriteStar` are recorded first, since
they are reused in the §3.3 proofs as well. -/

/-! Two `RewriteStar` lemmas that the rest of the file (and §3.3)
    will use repeatedly: a normal form rewrites only to itself, and
    `RewriteStar` lifts through arbitrary positions of a function
    symbol (the multi-step analogue of `Rewrite.congr`). -/

namespace RewriteStar
variable {E : Set (Equation S V)}

lemma eq_of_isNormalForm {t u : Term S V}
    (hn : IsNormalForm E t) (h : RewriteStar E t u) : t = u := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hc, _⟩
  · rfl
  · exact absurd hc (hn c)

lemma func_update (f : S.Symbol) (args : Fin (S.arity f) → Term S V)
    (i : Fin (S.arity f)) {t : Term S V}
    (h : RewriteStar E (args i) t) :
    RewriteStar E (.func f args) (.func f (Function.update args i t)) := by
  -- Lift the rewriting through the map `x ↦ func f (update args i x)`.
  have hlift : ∀ a b, Rewrite E a b →
        Rewrite E (.func f (Function.update args i a))
                  (.func f (Function.update args i b)) := by
    intro a b hr
    have h1 : Rewrite E ((Function.update args i a) i) b := by
      rw [Function.update_self]; exact hr
    have step := Rewrite.congr f (Function.update args i a) i h1
    rwa [Function.update_idem] at step
  have lifted := Relation.ReflTransGen.lift
    (fun x => (.func f (Function.update args i x) : Term S V)) hlift h
  simp only [Function.update_eq_self] at lifted
  exact lifted

lemma func {f : S.Symbol} {a₁ a₂ : Fin (S.arity f) → Term S V}
    (h : ∀ i, RewriteStar E (a₁ i) (a₂ i)) :
    RewriteStar E (.func f a₁) (.func f a₂) := by
  let merge : Nat → Fin (S.arity f) → Term S V :=
    fun k i => if i.val < k then a₂ i else a₁ i
  have h0 : merge 0 = a₁ := by funext i; simp [merge]
  have hN : merge (S.arity f) = a₂ := by
    funext i; simp [merge, i.isLt]
  suffices hsteps : ∀ k, k ≤ S.arity f →
      RewriteStar E (.func f a₁) (.func f (merge k)) by
    have := hsteps (S.arity f) le_rfl
    rwa [hN] at this
  intro k
  induction k with
  | zero =>
      intro _
      rw [h0]
      exact Relation.ReflTransGen.refl
  | succ k ih =>
      intro hk
      have hkN : k < S.arity f := Nat.lt_of_succ_le hk
      have ih' := ih (Nat.le_of_lt hkN)
      refine Relation.ReflTransGen.trans ih' ?_
      have heq : merge (k+1)
          = Function.update (merge k) ⟨k, hkN⟩ (a₂ ⟨k, hkN⟩) := by
        funext i
        by_cases hi : i = ⟨k, hkN⟩
        · subst hi
          simp [merge, Function.update_self]
        · rw [Function.update_of_ne hi]
          have hne : i.val ≠ k := fun heq => hi (Fin.ext heq)
          simp only [merge]
          split_ifs with h1 h2
          · rfl
          · exfalso; omega
          · exfalso; omega
          · rfl
      rw [heq]
      have hread : merge k ⟨k, hkN⟩ = a₁ ⟨k, hkN⟩ := by
        simp only [merge]; rw [if_neg (Nat.lt_irrefl k)]
      have hstar : RewriteStar E (merge k ⟨k, hkN⟩) (a₂ ⟨k, hkN⟩) := by
        rw [hread]; exact h ⟨k, hkN⟩
      exact func_update f (merge k) ⟨k, hkN⟩ hstar

end RewriteStar

/-! Existence (from termination, by well-founded recursion) and
    uniqueness (from confluence, by joining and applying
    `eq_of_isNormalForm` on each side) of normal forms. The
    classical-choice combinator `nf` then picks the unique normal
    form, with `nf_isNormalForm` and `rewriteStar_nf` as its
    defining specs. -/

lemma exists_normal_form_of_terminating {E : Set (Equation S V)}
    (hT : Terminating E) (t : Term S V) :
    ∃ n, IsNormalForm E n ∧ RewriteStar E t n := by
  induction t using WellFounded.induction (r := fun u t => Rewrite E t u) hT with
  | _ t ih =>
    by_cases h : ∃ u, Rewrite E t u
    · obtain ⟨u, hu⟩ := h
      obtain ⟨n, hn, hstar⟩ := ih u hu
      exact ⟨n, hn, Relation.ReflTransGen.head hu hstar⟩
    · push Not at h
      exact ⟨t, h, Relation.ReflTransGen.refl⟩

lemma normal_form_unique {E : Set (Equation S V)} (hC : Confluent E)
    {t n₁ n₂ : Term S V}
    (hn₁ : IsNormalForm E n₁) (h₁ : RewriteStar E t n₁)
    (hn₂ : IsNormalForm E n₂) (h₂ : RewriteStar E t n₂) :
    n₁ = n₂ := by
  obtain ⟨w, hw₁, hw₂⟩ := hC h₁ h₂
  exact (RewriteStar.eq_of_isNormalForm hn₁ hw₁).trans
        (RewriteStar.eq_of_isNormalForm hn₂ hw₂).symm

theorem exists_unique_nf {E : Set (Equation S V)}
    (hT : Terminating E) (hC : Confluent E) (t : Term S V) :
    ∃! n, IsNormalForm E n ∧ RewriteStar E t n := by
  obtain ⟨n, hn, hstar⟩ := exists_normal_form_of_terminating hT t
  refine ⟨n, ⟨hn, hstar⟩, ?_⟩
  rintro m ⟨hm, hm_star⟩
  exact normal_form_unique hC hm hm_star hn hstar

noncomputable def nf {E : Set (Equation S V)}
    (hT : Terminating E) (hC : Confluent E) (t : Term S V) : Term S V :=
  Classical.choose (exists_unique_nf hT hC t).exists

theorem nf_isNormalForm {E : Set (Equation S V)}
    (hT : Terminating E) (hC : Confluent E) (t : Term S V) :
    IsNormalForm E (nf hT hC t) :=
  (Classical.choose_spec (exists_unique_nf hT hC t).exists).1

theorem rewriteStar_nf {E : Set (Equation S V)}
    (hT : Terminating E) (hC : Confluent E) (t : Term S V) :
    RewriteStar E t (nf hT hC t) :=
  (Classical.choose_spec (exists_unique_nf hT hC t).exists).2

lemma nf_eq_of_isNormalForm {E : Set (Equation S V)}
    (hT : Terminating E) (hC : Confluent E) {t n : Term S V}
    (hn : IsNormalForm E n) (hstar : RewriteStar E t n) :
    nf hT hC t = n :=
  normal_form_unique hC (nf_isNormalForm hT hC t)
    (rewriteStar_nf hT hC t) hn hstar

lemma nf_eq_of_rewriteStar {E : Set (Equation S V)}
    (hT : Terminating E) (hC : Confluent E) {t u : Term S V}
    (h : RewriteStar E t u) : nf hT hC t = nf hT hC u :=
  nf_eq_of_isNormalForm hT hC (nf_isNormalForm hT hC u)
    (h.trans (rewriteStar_nf hT hC u))

/-! Joinability of derivable equations: every equation derivable
    in `E` admits a common reduct, i.e. `t` and `u` rewrite to a
    common term. Induction on the derivation: `ax` and `refl` give
    immediate joins, `symm` swaps sides, `trans` invokes confluence
    to merge the two intermediate joins, and `congr` uses the
    multi-step lift `RewriteStar.func`.

    Combined with uniqueness, joinability gives the iff that closes
    Theorem 2: `t ≡ u ↔ nf t = nf u`. -/

lemma joinable_of_derivable {E : Set (Equation S V)} (hC : Confluent E)
    {t u : Term S V} (h : Derivable E t u) :
    ∃ w, RewriteStar E t w ∧ RewriteStar E u w := by
  induction h with
  | ax he σ =>
      exact ⟨_, Relation.ReflTransGen.single (Rewrite.step he σ),
              Relation.ReflTransGen.refl⟩
  | refl t =>
      exact ⟨t, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | symm _ ih =>
      obtain ⟨w, h₁, h₂⟩ := ih
      exact ⟨w, h₂, h₁⟩
  | trans _ _ ih₁ ih₂ =>
      obtain ⟨w₁, h_t_w₁, h_u_w₁⟩ := ih₁
      obtain ⟨w₂, h_u_w₂, h_v_w₂⟩ := ih₂
      obtain ⟨w, h_w₁_w, h_w₂_w⟩ := hC h_u_w₁ h_u_w₂
      exact ⟨w,
        Relation.ReflTransGen.trans h_t_w₁ h_w₁_w,
        Relation.ReflTransGen.trans h_v_w₂ h_w₂_w⟩
  | congr f _ ih =>
      choose w hw₁ hw₂ using ih
      exact ⟨.func f w, RewriteStar.func hw₁, RewriteStar.func hw₂⟩

theorem derivable_iff_nf_eq {E : Set (Equation S V)}
    (hT : Terminating E) (hC : Confluent E) (t u : Term S V) :
    Derivable E t u ↔ nf hT hC t = nf hT hC u := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨w, h_t_w, h_u_w⟩ := joinable_of_derivable hC h
    rw [nf_eq_of_rewriteStar hT hC h_t_w,
        nf_eq_of_rewriteStar hT hC h_u_w]
  · have h₁ : Derivable E t (nf hT hC t) :=
      RewriteStar.toDerivable (rewriteStar_nf hT hC t)
    have h₂ : Derivable E u (nf hT hC u) :=
      RewriteStar.toDerivable (rewriteStar_nf hT hC u)
    rw [← h] at h₂
    exact h₁.trans h₂.symm

end Moss.EquationalLogic
