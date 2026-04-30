import Mathlib
import QuinePrograms.Moss2023.section2_1

/-!
# Section 3: Equational logic of diagonalization

This file follows Section 3 of Moss (2023), "An Equational Logic of
Self-Expressing Computer Programs".

The signature has two constants `d`, `e` and two binary operations
`+` (sequencing) and `@` (application). Figure 2 of the paper gives
the seven defining equations. Equational provability is denoted `≡`,
single-step rewriting `⟶`, and its reflexive-transitive closure `⟶*`.
The paper's rewriting system is taken to be terminating and confluent
(Proposition 7, verified externally with AProVE/ConCon and recorded
here as the only two axioms of the file).

The narrative milestones, in the order they appear below:

* Figure 2 , defining equations.
* §3.3 , rewriting system, normal forms (via Theorem 2 of §2.1),
  Definition 8 (quines, twins), Examples 9 and 10, Proposition 11
  (head of an `@`-normal-form is `d`), Definition 12 (the classes
  `N`, `N@`, `N+`), Proposition 13 (`N` = closed normal forms),
  Proposition 14 (a `+`-tree `≡ e` makes every leaf `≡ e`), and
  Proposition 15 (no `e` in `N`-elements; shape of `nf (t ∘ₐ u)`).
* §3.4 , Definition 16 (the `d`-count), Proposition 17 (small
  `d`-counts), Lemma 18 (rewriting does not decrease `d`-count when
  `e` is absent), Theorem 19 (the only quines are `e` and `d ∘ₐ d`),
  Proposition 20 (no cycles of length ≥ 2).
-/

namespace Moss.Section3

open Moss.EquationalLogic

/-! ## The Section 3 signature

The paper introduces "constants `d` and `e`, and also two binary
function symbols, `@` (for application) and `+` (for concatenation)"
(p. 6). We encode them as a four-symbol signature: `d`, `e` of arity
0 and `add`, `app` of arity 2. -/

inductive Sym | d | e | add | app
deriving DecidableEq, Repr

def Sym.arity : Sym → Nat
  | .d   => 0
  | .e   => 0
  | .add => 2
  | .app => 2

abbrev S3 : Signature where
  Symbol := Sym
  arity  := Sym.arity

/-! ## Variables and term constructors

The framework allows any variable type; we use `Var := Nat`
(countably many variables, as is conventional). The constants and
binary operations of the paper are exposed via the smart
constructors `Tm.d`, `Tm.e`, `Tm.add`, `Tm.app`, and the operations
are notated `+` and `∘ₐ` to match the paper's `+` and `@`
(written `∘ₐ` here only to avoid clashing with Lean's `@`). -/

abbrev Var : Type := Nat

abbrev Tm (V : Type) := Term S3 V

namespace Tm
variable {V W : Type}

def d : Tm V := .func Sym.d Fin.elim0

def e : Tm V := .func Sym.e Fin.elim0

def add (a b : Tm V) : Tm V := .func Sym.add ![a, b]

def app (a b : Tm V) : Tm V := .func Sym.app ![a, b]

end Tm

instance {V : Type} : Add (Tm V) := ⟨Tm.add⟩

scoped infixl:70 " ∘ₐ " => Tm.app

/-! Substitution computes through the smart constructors: pushing
    a substitution past a constant leaves it alone, and past a binary
    operation it lifts to its arguments. These are simp-normal forms
    used silently throughout the file. -/

namespace Tm
variable {V W : Type}

@[simp] lemma d_subst (σ : V → Tm W) : (Tm.d : Tm V).subst σ = Tm.d := by
  change (Term.func (S := S3) Sym.d Fin.elim0).subst σ
       = Term.func (S := S3) Sym.d Fin.elim0
  simp only [Term.subst]
  congr 1; funext i; exact i.elim0

@[simp] lemma e_subst (σ : V → Tm W) : (Tm.e : Tm V).subst σ = Tm.e := by
  change (Term.func (S := S3) Sym.e Fin.elim0).subst σ
       = Term.func (S := S3) Sym.e Fin.elim0
  simp only [Term.subst]
  congr 1; funext i; exact i.elim0

@[simp] lemma add_subst (a b : Tm V) (σ : V → Tm W) :
    (a + b).subst σ = a.subst σ + b.subst σ := by
  change (Term.func (S := S3) Sym.add ![a, b]).subst σ
       = Term.func (S := S3) Sym.add ![a.subst σ, b.subst σ]
  simp only [Term.subst]
  congr 1; funext i
  fin_cases i <;> rfl

@[simp] lemma app_subst (a b : Tm V) (σ : V → Tm W) :
    (a ∘ₐ b).subst σ = (a.subst σ) ∘ₐ (b.subst σ) := by
  change (Term.func (S := S3) Sym.app ![a, b]).subst σ
       = Term.func (S := S3) Sym.app ![a.subst σ, b.subst σ]
  simp only [Term.subst]
  congr 1; funext i
  fin_cases i <;> rfl

/-! The paper writes the equations of Figure 2 over the three
    metavariables `x, y, z`. Pick three concrete elements of `Var`
    to play those roles. `Derivable.ax` substitutes arbitrary terms
    for them, so any axiom instance phrased with `vx, vy, vz` is
    universally generic. -/

abbrev vx : Tm Var := .var 0
abbrev vy : Tm Var := .var 1
abbrev vz : Tm Var := .var 2

end Tm

/-! ## Figure 2 of the paper: the seven defining equations

These are the equations the paper proposes for the language with
constants `d`, `e` and binary operations `+`, `@`. They state that
`+` has `e` as a (two-sided) unit, that `+` is associative, that
applying a sum `(x + y)` is the same as composing the two
applications, and three rules involving `d`: `(d @ x) @ y` "runs
`x` after concatenating `x` to the left of the input", `e` is the
identity for `@`, and `d @ e` is `e`. The set `E_S3` is the finite
set of these seven equations, each a value of `Equation S3 Var`. -/

namespace Ax
open Tm

def addE : Equation S3 Var := ⟨vx + e, vx⟩
def eAdd : Equation S3 Var := ⟨e + vx, vx⟩
def addAssoc : Equation S3 Var := ⟨(vx + vy) + vz, vx + (vy + vz)⟩
def addApp : Equation S3 Var := ⟨(vx + vy) ∘ₐ vz, vy ∘ₐ (vx ∘ₐ vz)⟩
def dApp : Equation S3 Var := ⟨(d ∘ₐ vx) ∘ₐ vy, vx ∘ₐ (vy + vx)⟩
def eApp : Equation S3 Var := ⟨e ∘ₐ vx, vx⟩
def dAppE : Equation S3 Var := ⟨d ∘ₐ e, e⟩

end Ax

def E_S3 : Set (Equation S3 Var) :=
  {Ax.addE, Ax.eAdd, Ax.addAssoc, Ax.addApp, Ax.dApp, Ax.eApp, Ax.dAppE}

namespace Ax

lemma addE_mem : addE ∈ E_S3 := by simp [E_S3]
lemma eAdd_mem : eAdd ∈ E_S3 := by simp [E_S3]
lemma addAssoc_mem : addAssoc ∈ E_S3 := by simp [E_S3]
lemma addApp_mem : addApp ∈ E_S3 := by simp [E_S3]
lemma dApp_mem : dApp ∈ E_S3 := by simp [E_S3]
lemma eApp_mem : eApp ∈ E_S3 := by simp [E_S3]
lemma dAppE_mem : dAppE ∈ E_S3 := by simp [E_S3]

end Ax

/-! ## The equational theory `≡`

`t ≡ u` denotes `Derivable E_S3 t u`: the relation generated from
`E_S3` by the rules of equational logic (reflexivity, symmetry,
transitivity, substitution, and congruence for every function
symbol). All of the paper's reasoning at the level "`t = u` follows
from Figure 2" is captured by `≡`. -/

abbrev Equiv (t u : Tm Var) : Prop := Derivable E_S3 t u

scoped infix:50 " ≡ " => Moss.Section3.Equiv

namespace Equiv

theorem refl (t : Tm Var) : t ≡ t := Derivable.refl t

theorem symm {t u : Tm Var} (h : t ≡ u) : u ≡ t := Derivable.symm h

theorem trans {t u v : Tm Var} (h₁ : t ≡ u) (h₂ : u ≡ v) : t ≡ v :=
  Derivable.trans h₁ h₂

/-! Each axiom of Figure 2, ready-to-use at arbitrary terms.
    Internally they are `Derivable.ax` applied to the corresponding
    member of `E_S3`, with `vx, vy, vz` substituted by the chosen
    arguments. -/

theorem addE (a : Tm Var) : (a + Tm.e) ≡ a := by
  have h := Derivable.ax (E := E_S3) (e := Ax.addE) Ax.addE_mem
              (fun n => match n with | 0 => a | _ => Tm.d)
  simpa [Ax.addE, Tm.vx] using h

theorem eAdd (a : Tm Var) : (Tm.e + a) ≡ a := by
  have h := Derivable.ax (E := E_S3) (e := Ax.eAdd) Ax.eAdd_mem
              (fun n => match n with | 0 => a | _ => Tm.d)
  simpa [Ax.eAdd, Tm.vx] using h

theorem addAssoc (a b c : Tm Var) : ((a + b) + c) ≡ (a + (b + c)) := by
  have h := Derivable.ax (E := E_S3) (e := Ax.addAssoc) Ax.addAssoc_mem
              (fun n => match n with | 0 => a | 1 => b | 2 => c | _ => Tm.d)
  simpa [Ax.addAssoc, Tm.vx, Tm.vy, Tm.vz] using h

theorem addApp (a b c : Tm Var) : ((a + b) ∘ₐ c) ≡ (b ∘ₐ (a ∘ₐ c)) := by
  have h := Derivable.ax (E := E_S3) (e := Ax.addApp) Ax.addApp_mem
              (fun n => match n with | 0 => a | 1 => b | 2 => c | _ => Tm.d)
  simpa [Ax.addApp, Tm.vx, Tm.vy, Tm.vz] using h

theorem dApp (a b : Tm Var) : ((Tm.d ∘ₐ a) ∘ₐ b) ≡ (a ∘ₐ (b + a)) := by
  have h := Derivable.ax (E := E_S3) (e := Ax.dApp) Ax.dApp_mem
              (fun n => match n with | 0 => a | 1 => b | _ => Tm.d)
  simpa [Ax.dApp, Tm.vx, Tm.vy] using h

theorem eApp (a : Tm Var) : (Tm.e ∘ₐ a) ≡ a := by
  have h := Derivable.ax (E := E_S3) (e := Ax.eApp) Ax.eApp_mem
              (fun n => match n with | 0 => a | _ => Tm.d)
  simpa [Ax.eApp, Tm.vx] using h

theorem dAppE : (Tm.d ∘ₐ Tm.e) ≡ Tm.e := by
  have h := Derivable.ax (E := E_S3) (e := Ax.dAppE) Ax.dAppE_mem
              (fun _ => Tm.d)
  simpa [Ax.dAppE] using h

/-! Congruence for `+` and `∘ₐ`: if their arguments are pairwise
    `≡`, so are the resulting compound terms. These are the
    equational-logic congruence rules specialised to our two
    function symbols. -/

theorem addCongr {t₁ t₂ u₁ u₂ : Tm Var}
    (h₁ : t₁ ≡ t₂) (h₂ : u₁ ≡ u₂) : (t₁ + u₁) ≡ (t₂ + u₂) := by
  change Derivable E_S3
    (Term.func (S := S3) Sym.add ![t₁, u₁])
    (Term.func (S := S3) Sym.add ![t₂, u₂])
  refine Derivable.congr (S := S3) (E := E_S3) Sym.add ?_
  intro i; fin_cases i
  · simpa using h₁
  · simpa using h₂

theorem appCongr {t₁ t₂ u₁ u₂ : Tm Var}
    (h₁ : t₁ ≡ t₂) (h₂ : u₁ ≡ u₂) : (t₁ ∘ₐ u₁) ≡ (t₂ ∘ₐ u₂) := by
  change Derivable E_S3
    (Term.func (S := S3) Sym.app ![t₁, u₁])
    (Term.func (S := S3) Sym.app ![t₂, u₂])
  refine Derivable.congr (S := S3) (E := E_S3) Sym.app ?_
  intro i; fin_cases i
  · simpa using h₁
  · simpa using h₂

/-! One-sided congruence helpers, used pervasively below to thread
    `≡` through a single argument of `+` or `∘ₐ`. -/

theorem addLeftCongr {t₁ t₂ : Tm Var} (h : t₁ ≡ t₂) (u : Tm Var) :
    (t₁ + u) ≡ (t₂ + u) := addCongr h (refl u)

theorem addRightCongr (t : Tm Var) {u₁ u₂ : Tm Var} (h : u₁ ≡ u₂) :
    (t + u₁) ≡ (t + u₂) := addCongr (refl t) h

theorem appLeftCongr {t₁ t₂ : Tm Var} (h : t₁ ≡ t₂) (u : Tm Var) :
    (t₁ ∘ₐ u) ≡ (t₂ ∘ₐ u) := appCongr h (refl u)

theorem appRightCongr (t : Tm Var) {u₁ u₂ : Tm Var} (h : u₁ ≡ u₂) :
    (t ∘ₐ u₁) ≡ (t ∘ₐ u₂) := appCongr (refl t) h

end Equiv

/-! ## §3.3 Rewriting system and normal forms

The paper writes (p. 8): "We construct a rewriting system R by
taking the pairs `(ℓ, r)` whenever `ℓ = r` is an equation in the
system. That is, we orient all equations in Figure 2 left-to-right,
as they are written." Single-step rewriting under `E_S3` is `⟶`,
its reflexive-transitive closure is `⟶*`. -/

abbrev Rewrite (t u : Tm Var) : Prop := Moss.EquationalLogic.Rewrite E_S3 t u

abbrev RewriteStar (t u : Tm Var) : Prop := Moss.EquationalLogic.RewriteStar E_S3 t u

scoped infix:50 " ⟶ "  => Moss.Section3.Rewrite

scoped infix:50 " ⟶* " => Moss.Section3.RewriteStar

namespace Rewrite

/-! Each Figure 2 axiom, packaged as a single rewrite step at
    arbitrary arguments. Same template as the `≡` versions, but
    using `Rewrite.step` rather than `Derivable.ax`. -/

open Moss.EquationalLogic (Rewrite)

theorem addE (a : Tm Var) : (a + Tm.e) ⟶ a := by
  have h := Rewrite.step (E := E_S3) (e := Ax.addE) Ax.addE_mem
              (fun n => match n with | 0 => a | _ => Tm.d)
  simpa [Ax.addE, Tm.vx] using h

theorem eAdd (a : Tm Var) : (Tm.e + a) ⟶ a := by
  have h := Rewrite.step (E := E_S3) (e := Ax.eAdd) Ax.eAdd_mem
              (fun n => match n with | 0 => a | _ => Tm.d)
  simpa [Ax.eAdd, Tm.vx] using h

theorem addAssoc (a b c : Tm Var) : ((a + b) + c) ⟶ (a + (b + c)) := by
  have h := Rewrite.step (E := E_S3) (e := Ax.addAssoc) Ax.addAssoc_mem
              (fun n => match n with | 0 => a | 1 => b | 2 => c | _ => Tm.d)
  simpa [Ax.addAssoc, Tm.vx, Tm.vy, Tm.vz] using h

theorem addApp (a b c : Tm Var) : ((a + b) ∘ₐ c) ⟶ (b ∘ₐ (a ∘ₐ c)) := by
  have h := Rewrite.step (E := E_S3) (e := Ax.addApp) Ax.addApp_mem
              (fun n => match n with | 0 => a | 1 => b | 2 => c | _ => Tm.d)
  simpa [Ax.addApp, Tm.vx, Tm.vy, Tm.vz] using h

theorem dApp (a b : Tm Var) : ((Tm.d ∘ₐ a) ∘ₐ b) ⟶ (a ∘ₐ (b + a)) := by
  have h := Rewrite.step (E := E_S3) (e := Ax.dApp) Ax.dApp_mem
              (fun n => match n with | 0 => a | 1 => b | _ => Tm.d)
  simpa [Ax.dApp, Tm.vx, Tm.vy] using h

theorem eApp (a : Tm Var) : (Tm.e ∘ₐ a) ⟶ a := by
  have h := Rewrite.step (E := E_S3) (e := Ax.eApp) Ax.eApp_mem
              (fun n => match n with | 0 => a | _ => Tm.d)
  simpa [Ax.eApp, Tm.vx] using h

theorem dAppE : (Tm.d ∘ₐ Tm.e) ⟶ Tm.e := by
  have h := Rewrite.step (E := E_S3) (e := Ax.dAppE) Ax.dAppE_mem
              (fun _ => Tm.d)
  simpa [Ax.dAppE] using h

/-! Congruence helpers: lift a single-side rewrite through `+` and `∘ₐ`.
    Specialise `Rewrite.congr` at `Sym.add` / `Sym.app` and rewrite the
    `Function.update` to a literal `![·, ·]`. -/

theorem app_left {a a' b : Tm Var} (h : a ⟶ a') : (a ∘ₐ b) ⟶ (a' ∘ₐ b) := by
  change Rewrite (Term.func Sym.app ![a, b]) (Term.func Sym.app ![a', b])
  have hupd : (Function.update ![a, b] (0 : Fin 2) a' : Fin 2 → Tm Var) = ![a', b] := by
    funext i; fin_cases i <;> simp
  rw [← hupd]
  exact Rewrite.congr (E := E_S3) Sym.app ![a, b] (0 : Fin 2) (by simpa using h)

theorem app_right {a b b' : Tm Var} (h : b ⟶ b') : (a ∘ₐ b) ⟶ (a ∘ₐ b') := by
  change Rewrite (Term.func Sym.app ![a, b]) (Term.func Sym.app ![a, b'])
  have hupd : (Function.update ![a, b] (1 : Fin 2) b' : Fin 2 → Tm Var) = ![a, b'] := by
    funext i; fin_cases i <;> simp
  rw [← hupd]
  exact Rewrite.congr (E := E_S3) Sym.app ![a, b] (1 : Fin 2) (by simpa using h)

theorem add_left {a a' b : Tm Var} (h : a ⟶ a') : (a + b) ⟶ (a' + b) := by
  change Rewrite (Term.func Sym.add ![a, b]) (Term.func Sym.add ![a', b])
  have hupd : (Function.update ![a, b] (0 : Fin 2) a' : Fin 2 → Tm Var) = ![a', b] := by
    funext i; fin_cases i <;> simp
  rw [← hupd]
  exact Rewrite.congr (E := E_S3) Sym.add ![a, b] (0 : Fin 2) (by simpa using h)

theorem add_right {a b b' : Tm Var} (h : b ⟶ b') : (a + b) ⟶ (a + b') := by
  change Rewrite (Term.func Sym.add ![a, b]) (Term.func Sym.add ![a, b'])
  have hupd : (Function.update ![a, b] (1 : Fin 2) b' : Fin 2 → Tm Var) = ![a, b'] := by
    funext i; fin_cases i <;> simp
  rw [← hupd]
  exact Rewrite.congr (E := E_S3) Sym.add ![a, b] (1 : Fin 2) (by simpa using h)

end Rewrite

/-! ### Proposition 7: termination and confluence

The paper's Proposition 7 says that the rewriting system derived
from Figure 2 is terminating and confluent. The paper verifies this
externally (Appendix A: AProVE for termination, ConCon/TRS.tool for
confluence). We import the two statements here as axioms. -/

axiom terminating_E_S3 : Terminating E_S3

axiom confluent_E_S3 : Confluent E_S3

/-! ### Theorem 2 specialised to `E_S3`

Once Proposition 7 is in hand, Theorem 2 of §2.1 (Meseguer–Goguen)
gives every term a unique normal form `nf t`. The paper's key
consequence , `t ≡ u` iff `nf t = nf u` , is `equiv_iff_nf_eq`.
The derived facts `nf_isNormalForm`, `rewriteStar_nf`,
`nf_eq_self_of_isNF`, and `nf_eq_of_equiv` are the small
toolkit we will use throughout. -/

noncomputable def nf (t : Tm Var) : Tm Var :=
  Moss.EquationalLogic.nf terminating_E_S3 confluent_E_S3 t

theorem nf_isNormalForm (t : Tm Var) :
    IsNormalForm E_S3 (nf t) :=
  Moss.EquationalLogic.nf_isNormalForm terminating_E_S3 confluent_E_S3 t

theorem rewriteStar_nf (t : Tm Var) : t ⟶* nf t :=
  Moss.EquationalLogic.rewriteStar_nf terminating_E_S3 confluent_E_S3 t

theorem equiv_iff_nf_eq (t u : Tm Var) : (t ≡ u) ↔ nf t = nf u :=
  derivable_iff_nf_eq terminating_E_S3 confluent_E_S3 t u

theorem nf_eq_self_of_isNF {t : Tm Var}
    (h : IsNormalForm E_S3 t) : nf t = t :=
  nf_eq_of_isNormalForm terminating_E_S3 confluent_E_S3
    h Relation.ReflTransGen.refl

theorem nf_eq_of_equiv {t u : Tm Var} (h : t ≡ u) : nf t = nf u :=
  (equiv_iff_nf_eq t u).mp h

/-! ### Definition 8: quines and twins

The paper: "A term `t` is a *quine* if it is a normal form and
`t @ e ≡ t`. Terms `t` and `u` are *twins* if they are distinct
normal forms such that `t @ e ≡ u` and `u @ e ≡ t`." These are the
two basic notions Section 3 will classify: Theorem 19 (uniqueness
of quines) and Proposition 20 (no twins or longer cycles). -/

def IsQuine (t : Tm Var) : Prop :=
  IsNormalForm E_S3 t ∧ (t ∘ₐ Tm.e) ≡ t

def IsTwins (t u : Tm Var) : Prop :=
  IsNormalForm E_S3 t ∧
  IsNormalForm E_S3 u ∧
  t ≠ u ∧
  ((t ∘ₐ Tm.e) ≡ u) ∧ ((u ∘ₐ Tm.e) ≡ t)

/-! ### Examples 9 and 10

The paper's Example 9 calls `d ∘ₐ d` "the standard presentation of
quines": `(d ∘ₐ d) ∘ₐ e` rewrites to `d ∘ₐ (e + d)` (rule `dApp`)
and then to `d ∘ₐ d` (rule `eAdd`). The constant `e` is trivially a
quine. Example 10 then exhibits two terms whose application to `e`
*reduces*: `(d ∘ₐ (d + d)) ∘ₐ e` and `(d + d) ∘ₐ e`. To formalise
these we need a few normal-form lemmas about `e`, `d`, `d ∘ₐ d`,
`d + d` and `d ∘ₐ (d + d)`. The two lemmas at the bottom show that
the latter two compositions are *not* in normal form, illustrating
Example 10. -/

private lemma no_axiom_eq_e :
    ∀ e ∈ E_S3, ∀ σ : Var → Tm Var,
      e.lhs.subst σ ≠ Term.func Sym.e Fin.elim0 := by
  intro e he σ hw
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (injection hw with hf _; cases hf)

private lemma no_axiom_eq_d :
    ∀ e ∈ E_S3, ∀ σ : Var → Tm Var,
      e.lhs.subst σ ≠ Term.func Sym.d Fin.elim0 := by
  intro e he σ hw
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (injection hw with hf _; cases hf)

theorem Tm.e_isNF : IsNormalForm E_S3 Tm.e := by
  apply IsNormalForm.of_arity_zero _ rfl
  exact no_axiom_eq_e

theorem Tm.d_isNF : IsNormalForm E_S3 Tm.d := by
  apply IsNormalForm.of_arity_zero _ rfl
  exact no_axiom_eq_d

theorem dd_isNF : IsNormalForm E_S3 (Tm.d ∘ₐ Tm.d) := by
  intro u hu
  generalize hw : ((Tm.d ∘ₐ Tm.d) : Tm Var) = w at hu
  cases hu with
  | step he σ =>
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals (
        injection hw with h_head h_args
        first
        | (cases h_head; done)
        | (have h := congrFun h_args 0
           injection h with hf _
           cases hf
           done)
        | (have h := congrFun h_args 1
           injection h with hf _
           cases hf))
  | congr f args i hr =>
      change Term.func Sym.app ![Tm.d, Tm.d] = Term.func f args at hw
      injection hw with hf hargs
      subst hf
      have hargs' : args = ![Tm.d, Tm.d] := (eq_of_heq hargs).symm
      subst hargs'
      fin_cases i
      · exact Tm.d_isNF _ (by simpa using hr)
      · exact Tm.d_isNF _ (by simpa using hr)

theorem d_plus_d_isNF : IsNormalForm E_S3 (Tm.d + Tm.d) := by
  intro u hu
  generalize hw : ((Tm.d + Tm.d) : Tm Var) = w at hu
  cases hu with
  | step he σ =>
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals (
        injection hw with h_head h_args
        first
        | (cases h_head; done)
        | (have h := congrFun h_args 0
           injection h with hf _
           cases hf)
        | (have h := congrFun h_args 1
           injection h with hf _
           cases hf))
  | congr f args i hr =>
      change Term.func Sym.add ![Tm.d, Tm.d] = Term.func f args at hw
      injection hw with hf hargs
      subst hf
      have hargs' : args = ![Tm.d, Tm.d] := (eq_of_heq hargs).symm
      subst hargs'
      fin_cases i
      · exact Tm.d_isNF _ (by simpa using hr)
      · exact Tm.d_isNF _ (by simpa using hr)

theorem d_d_plus_d_isNF :
    IsNormalForm E_S3 (Tm.d ∘ₐ (Tm.d + Tm.d)) := by
  intro u hu
  generalize hw : ((Tm.d ∘ₐ (Tm.d + Tm.d)) : Tm Var) = w at hu
  cases hu with
  | step he σ =>
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals (
        injection hw with h_head h_args
        first
        | (cases h_head; done)
        | (have h := congrFun h_args 0
           injection h with hf _
           cases hf
           done)
        | (have h := congrFun h_args 1
           injection h with hf _
           cases hf))
  | congr f args i hr =>
      change Term.func Sym.app ![Tm.d, Tm.d + Tm.d] = Term.func f args at hw
      injection hw with hf hargs
      subst hf
      have hargs' : args = ![Tm.d, Tm.d + Tm.d] := (eq_of_heq hargs).symm
      subst hargs'
      fin_cases i
      · exact Tm.d_isNF _ (by simpa using hr)
      · exact d_plus_d_isNF _ (by simpa using hr)

theorem e_quine : IsQuine Tm.e :=
  ⟨Tm.e_isNF, Equiv.eApp Tm.e⟩

theorem dd_quine : IsQuine (Tm.d ∘ₐ Tm.d) := by
  refine ⟨dd_isNF, ?_⟩
  have h₁ : ((Tm.d ∘ₐ Tm.d) ∘ₐ Tm.e) ≡ (Tm.d ∘ₐ (Tm.e + Tm.d)) :=
    Equiv.dApp Tm.d Tm.e
  have h₂ : (Tm.e + Tm.d) ≡ Tm.d := Equiv.eAdd Tm.d
  exact Equiv.trans h₁ (Equiv.appRightCongr Tm.d h₂)

theorem d_d_plus_d_at_e_not_isNF :
    ¬ IsNormalForm E_S3 ((Tm.d ∘ₐ (Tm.d + Tm.d)) ∘ₐ Tm.e) := by
  intro h
  exact h _ (Rewrite.dApp (Tm.d + Tm.d) Tm.e)

theorem d_plus_d_at_e_not_isNF :
    ¬ IsNormalForm E_S3 ((Tm.d + Tm.d) ∘ₐ Tm.e) := by
  intro h
  exact h _ (Rewrite.addApp Tm.d Tm.d Tm.e)

/-! ### Proposition 11

The paper: "If the term `t` is in normal form, then every subterm
of `t` of the form `u @ v` has `u = d`. In particular, if `t` is an
`@`-term which is a normal form, then there is a normal form `u`
such that `t = d @ u`."

Two preliminaries are needed before the proposition itself: the
left and right sub-terms of an `@`-normal-form are themselves
normal forms (otherwise rewriting under congruence would lift to
the whole), and we restrict to *closed* terms (the inductive type
`IsClosed`). The closedness is essential: a variable `a` is
vacuously a normal form but is not `d`, so `a ∘ₐ b` would be a
normal form with non-`d` head if variables were allowed.

The two main results are then:

* `head_eq_d_of_isNormalForm_app` , the inductive content of
  Proposition 11: a closed `a` at the head of an `@`-normal-form
  must equal `d`.
* `isNormalForm_app_eq_d_app` , its packaged form: every closed
  `@`-normal-form has shape `d ∘ₐ u` with `u` itself a normal form.
-/

theorem isNormalForm_of_app_left {a b : Tm Var}
    (h : IsNormalForm E_S3 (a ∘ₐ b)) : IsNormalForm E_S3 a :=
  fun _ ha => h _ (Rewrite.app_left ha)

theorem isNormalForm_of_app_right {a b : Tm Var}
    (h : IsNormalForm E_S3 (a ∘ₐ b)) : IsNormalForm E_S3 b :=
  fun _ hb => h _ (Rewrite.app_right hb)

inductive IsClosed : Tm Var → Prop
  | d : IsClosed Tm.d
  | e : IsClosed Tm.e
  | add {a b : Tm Var} : IsClosed a → IsClosed b → IsClosed (a + b)
  | app {a b : Tm Var} : IsClosed a → IsClosed b → IsClosed (a ∘ₐ b)

theorem head_eq_d_of_isNormalForm_app {a : Tm Var} (hcl : IsClosed a) :
    ∀ b, IsNormalForm E_S3 (a ∘ₐ b) → a = Tm.d := by
  induction hcl with
  | d => intros; rfl
  | e =>
      intro b hnf
      exact (hnf _ (Rewrite.eApp b)).elim
  | @add a₁ a₂ _ _ _ _ =>
      intro b hnf
      exact (hnf _ (Rewrite.addApp a₁ a₂ b)).elim
  | @app a₁ a₂ _ _ iha _ =>
      intro b hnf
      exfalso
      have hnf' : IsNormalForm E_S3 (a₁ ∘ₐ a₂) :=
        isNormalForm_of_app_left hnf
      have hd : a₁ = Tm.d := iha a₂ hnf'
      subst hd
      exact hnf _ (Rewrite.dApp a₂ b)

theorem isNormalForm_app_eq_d_app {a b : Tm Var}
    (hcla : IsClosed a)
    (hnf : IsNormalForm E_S3 (a ∘ₐ b)) :
    ∃ u, (IsNormalForm E_S3 u) ∧ (a ∘ₐ b = Tm.d ∘ₐ u) := by
  refine ⟨b, isNormalForm_of_app_right hnf, ?_⟩
  have ha : a = Tm.d := head_eq_d_of_isNormalForm_app hcla b hnf
  rw [ha]

/-! The analogous fact for `+`: if `a + b` is a normal form, then
    so are both `a` and `b` (a single rewrite under either side
    would lift via congruence to a rewrite of the whole sum). These
    are used pervasively below and in the proof of Proposition 13. -/

theorem isNormalForm_of_add_left {a b : Tm Var}
    (h : IsNormalForm E_S3 (a + b)) : IsNormalForm E_S3 a :=
  fun _ ha => h _ (Rewrite.add_left ha)

theorem isNormalForm_of_add_right {a b : Tm Var}
    (h : IsNormalForm E_S3 (a + b)) : IsNormalForm E_S3 b :=
  fun _ hb => h _ (Rewrite.add_right hb)

/-! ### Definition 12

The paper: "Let `N`, `N+`, `N@` be the smallest sets of terms such
that

  1. `d, e ∈ N`.
  2. `N+ ∪ N@ ⊆ N`.
  3. If `t ∈ N \ {e}`, then `d @ t` belongs to `N@`.
  4. If `n ≥ 2` and `t₁, …, tₙ ∈ N@ ∪ {d}`, then
     `t₁ + (t₂ + ⋯ + (tₙ₋₁ + tₙ) ⋯ ) ∈ N+`."

We encode this via four mutually inductive predicates: `IsN` for
`N`, `IsNApp` for `N@`, `IsNAdd` for `N+`, and `IsNAddAtom` for the
admissible summands `N@ ∪ {d}`. By construction no constructor
introduces a variable, so every member of `N` is closed. -/

mutual
inductive IsN : Tm Var → Prop
  | d : IsN Tm.d
  | e : IsN Tm.e
  | ofApp {t : Tm Var} : IsNApp t → IsN t
  | ofAdd {t : Tm Var} : IsNAdd t → IsN t

inductive IsNApp : Tm Var → Prop
  | mk {s : Tm Var} : IsN s → s ≠ Tm.e → IsNApp (Tm.d ∘ₐ s)

inductive IsNAdd : Tm Var → Prop
  | base {a b : Tm Var} : IsNAddAtom a → IsNAddAtom b → IsNAdd (a + b)
  | cons {a b : Tm Var} : IsNAddAtom a → IsNAdd b → IsNAdd (a + b)

inductive IsNAddAtom : Tm Var → Prop
  | d : IsNAddAtom Tm.d
  | ofApp {t : Tm Var} : IsNApp t → IsNAddAtom t
end

/-! Three small inversion facts about Definition 12: an
    `IsNAddAtom` is never `e` and never of `+`-shape; an `IsNAdd` is
    never `e`. Each follows by `cases` on the corresponding
    inductive. They are repeatedly used in the case analyses of
    Proposition 13 below. -/

theorem IsNAddAtom.ne_e {t : Tm Var} (h : IsNAddAtom t) : t ≠ Tm.e := by
  intro heq
  cases h with
  | d => injection heq with hf _; cases hf
  | ofApp happ =>
      cases happ with
      | mk _ _ => injection heq with hf _; cases hf

theorem IsNAddAtom.not_isSum {t : Tm Var} (h : IsNAddAtom t) :
    ∀ a b : Tm Var, t ≠ a + b := by
  intro a b heq
  cases h with
  | d => injection heq with hf _; cases hf
  | ofApp happ =>
      cases happ with
      | mk _ _ => injection heq with hf _; cases hf

theorem IsNAdd.ne_e {t : Tm Var} (h : IsNAdd t) : t ≠ Tm.e := by
  intro heq
  cases h with
  | base _ _ => injection heq with hf _; cases hf
  | cons _ _ => injection heq with hf _; cases hf

/-! ### Proposition 13 (forward direction)

The paper: "`N` is the set of normal forms." We prove both
inclusions; the forward direction first. Every member of `N` is a
normal form: no Figure 2 rewrite rule can fire at its top, and any
rewrite at a strict subterm would contradict the corresponding
sub-claim by induction. The four mutual theorems mirror the four
mutual inductives `IsN`, `IsNApp`, `IsNAdd`, `IsNAddAtom`. -/

mutual
theorem IsN.isNormalForm : ∀ {t : Tm Var}, IsN t →
    IsNormalForm E_S3 t
  | _, .d        => Tm.d_isNF
  | _, .e        => Tm.e_isNF
  | _, .ofApp h  => IsNApp.isNormalForm h
  | _, .ofAdd h  => IsNAdd.isNormalForm h

theorem IsNApp.isNormalForm : ∀ {t : Tm Var}, IsNApp t →
    IsNormalForm E_S3 t
  | _, @IsNApp.mk s hs hne => by
      intro u hu
      generalize hw : (Tm.d ∘ₐ s) = w at hu
      cases hu with
      | step he σ =>
          rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | (injection hw with hf _; cases hf; done)
            | (injection hw with _ h_args
               have h := congrFun h_args 0
               injection h with hf _; cases hf; done)
            | (injection hw with _ h_args
               have h := congrFun h_args 1
               simp only [Fin.isValue, Matrix.cons_val_one,
                 Matrix.cons_val_fin_one, Tm.e_subst] at h
               exact hne h)
      | congr f args i hr =>
          change Term.func Sym.app ![Tm.d, s] = Term.func f args at hw
          injection hw with hf hargs
          subst hf
          have hargs' : args = ![Tm.d, s] := (eq_of_heq hargs).symm
          subst hargs'
          fin_cases i
          · exact Tm.d_isNF _ (by simpa using hr)
          · exact (IsN.isNormalForm hs) _ (by simpa using hr)

theorem IsNAdd.isNormalForm : ∀ {t : Tm Var}, IsNAdd t →
    IsNormalForm E_S3 t
  | _, @IsNAdd.base a b ha hb => by
      intro u hu
      generalize hw : (a + b) = w at hu
      cases hu with
      | step he σ =>
          rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | (injection hw with hf _; cases hf; done)
            | (injection hw with _ h_args
               have h := congrFun h_args 1
               simp only [Fin.isValue, Matrix.cons_val_one,
                 Matrix.cons_val_fin_one, Tm.e_subst] at h
               exact hb.ne_e h)
            | (injection hw with _ h_args
               have h := congrFun h_args 0
               simp only [Fin.isValue, Matrix.cons_val_zero, Tm.e_subst] at h
               exact ha.ne_e h)
            | (injection hw with _ h_args
               have h := congrFun h_args 0
               simp only [Fin.isValue, Matrix.cons_val_zero,
                 Tm.add_subst, Term.subst] at h
               exact ha.not_isSum _ _ h)
      | congr f args i hr =>
          change Term.func Sym.add ![a, b] = Term.func f args at hw
          injection hw with hf hargs
          subst hf
          have hargs' : args = ![a, b] := (eq_of_heq hargs).symm
          subst hargs'
          fin_cases i
          · exact (IsNAddAtom.isNormalForm ha) _ (by simpa using hr)
          · exact (IsNAddAtom.isNormalForm hb) _ (by simpa using hr)
  | _, @IsNAdd.cons a b ha hb => by
      intro u hu
      generalize hw : (a + b) = w at hu
      cases hu with
      | step he σ =>
          rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | (injection hw with hf _; cases hf; done)
            | (injection hw with _ h_args
               have h := congrFun h_args 1
               simp only [Fin.isValue, Matrix.cons_val_one,
                 Matrix.cons_val_fin_one, Tm.e_subst] at h
               exact hb.ne_e h)
            | (injection hw with _ h_args
               have h := congrFun h_args 0
               simp only [Fin.isValue, Matrix.cons_val_zero, Tm.e_subst] at h
               exact ha.ne_e h)
            | (injection hw with _ h_args
               have h := congrFun h_args 0
               simp only [Fin.isValue, Matrix.cons_val_zero,
                 Tm.add_subst, Term.subst] at h
               exact ha.not_isSum _ _ h)
      | congr f args i hr =>
          change Term.func Sym.add ![a, b] = Term.func f args at hw
          injection hw with hf hargs
          subst hf
          have hargs' : args = ![a, b] := (eq_of_heq hargs).symm
          subst hargs'
          fin_cases i
          · exact (IsNAddAtom.isNormalForm ha) _ (by simpa using hr)
          · exact (IsNAdd.isNormalForm hb) _ (by simpa using hr)

theorem IsNAddAtom.isNormalForm : ∀ {t : Tm Var}, IsNAddAtom t →
    IsNormalForm E_S3 t
  | _, .d        => Tm.d_isNF
  | _, .ofApp h  => IsNApp.isNormalForm h
end

/-! ### Proposition 13 (backward direction)

The paper combines Proposition 11 with case analysis on the
structure of a normal form to show that every closed normal form
lies in `N`. We induct on `IsClosed t`: the constants are immediate;
for `a + b` we sort the right summand `b` into the four `IsN` cases,
prepending `a` as an admissible atom; for `a ∘ₐ b` we use
Proposition 11 to force `a = d`, then build `IsNApp.mk` from the
recursion on `b` (which must not be `e`, since `dAppE` would fire).
The wrap-up `isN_iff_isNormalForm` is the iff of Proposition 13. -/

theorem isN_of_isNormalForm {t : Tm Var} (hcl : IsClosed t) :
    IsNormalForm E_S3 t → IsN t := by
  induction hcl with
  | d => intro _; exact IsN.d
  | e => intro _; exact IsN.e
  | @add a b _ _ iha ihb =>
      intro hnf
      have hnfa := isNormalForm_of_add_left hnf
      have hnfb := isNormalForm_of_add_right hnf
      have hia : IsN a := iha hnfa
      have hib : IsN b := ihb hnfb
      apply IsN.ofAdd
      have ha_summand : IsNAddAtom a := by
        cases hia with
        | d => exact IsNAddAtom.d
        | e => exact (hnf _ (Rewrite.eAdd b)).elim
        | ofApp happ => exact IsNAddAtom.ofApp happ
        | ofAdd hadd =>
            cases hadd with
            | @base a₁ a₂ _ _ =>
                exact (hnf _ (Rewrite.addAssoc a₁ a₂ b)).elim
            | @cons a₁ a₂ _ _ =>
                exact (hnf _ (Rewrite.addAssoc a₁ a₂ b)).elim
      cases hib with
      | d => exact IsNAdd.base ha_summand IsNAddAtom.d
      | e => exact (hnf _ (Rewrite.addE a)).elim
      | ofApp happ => exact IsNAdd.base ha_summand (IsNAddAtom.ofApp happ)
      | ofAdd hbAdd => exact IsNAdd.cons ha_summand hbAdd
  | @app a b hca _ _ ihb =>
      intro hnf
      have ha_d : a = Tm.d := head_eq_d_of_isNormalForm_app hca b hnf
      subst ha_d
      have hnfb := isNormalForm_of_app_right hnf
      have hib : IsN b := ihb hnfb
      have hne : b ≠ Tm.e := by
        intro hbe
        subst hbe
        exact hnf _ Rewrite.dAppE
      exact IsN.ofApp (IsNApp.mk hib hne)

theorem isN_iff_isNormalForm {t : Tm Var} (hcl : IsClosed t) :
    IsN t ↔ IsNormalForm E_S3 t :=
  ⟨IsN.isNormalForm, isN_of_isNormalForm hcl⟩

/-! ### Proposition 14

The paper: "If `t` is a sum of terms `u₁, u₂, …, uₖ` in any
parenthesization, and `t ≡ e`, then for all `i`, `uᵢ ≡ e`."

The paper's proof is by induction on the number of rewrite steps in
a chain `t →ⁿ e`. We follow the same plan: first replace `≡` by `⟶*`
(legal because `e` is a normal form), then expose the chain length
as `RewN n t e` and induct on `n`. The auxiliary `IsAddOf`
records "`t` is a sum of `us` in *some* parenthesization", matching
the paper's hypothesis. The theorem is reached in three steps: the
two-summand specialisation `add_equiv_e`, the structural form
`mem_equiv_e_of_isAddOf_of_equiv_e`, and the
`summandsOf`-corollary `mem_summandsOf_equiv_e`. -/

theorem equiv_e_iff_rewriteStar_e (t : Tm Var) :
    (t ≡ Tm.e) ↔ RewriteStar t Tm.e := by
  refine ⟨fun h => ?_, RewriteStar.toDerivable⟩
  have hnf : nf t = Tm.e := by
    have hnfeq : nf t = nf Tm.e := nf_eq_of_equiv h
    rw [nf_eq_self_of_isNF Tm.e_isNF] at hnfeq
    exact hnfeq
  have hstar := rewriteStar_nf t
  rwa [hnf] at hstar

def summandsOf : Tm Var → List (Tm Var)
  | Term.var v                  => [Term.var v]
  | Term.func Sym.add args      =>
      summandsOf (args (0 : Fin 2)) ++ summandsOf (args (1 : Fin 2))
  | Term.func Sym.d args        => [Term.func Sym.d args]
  | Term.func Sym.e args        => [Term.func Sym.e args]
  | Term.func Sym.app args      => [Term.func Sym.app args]

@[simp] lemma summandsOf_var (v : Var) :
    summandsOf (Term.var v : Tm Var) = [Term.var v] := rfl

@[simp] lemma summandsOf_d : summandsOf (Tm.d : Tm Var) = [Tm.d] := rfl

@[simp] lemma summandsOf_e : summandsOf (Tm.e : Tm Var) = [Tm.e] := rfl

@[simp] lemma summandsOf_app (a b : Tm Var) :
    summandsOf (a ∘ₐ b) = [a ∘ₐ b] := rfl

@[simp] lemma summandsOf_add (a b : Tm Var) :
    summandsOf (a + b) = summandsOf a ++ summandsOf b := by
  change summandsOf (Term.func Sym.add ![a, b]) = summandsOf a ++ summandsOf b
  change summandsOf ((![a, b] : Fin 2 → Tm Var) 0) ++
          summandsOf ((![a, b] : Fin 2 → Tm Var) 1)
       = summandsOf a ++ summandsOf b
  rfl

inductive IsAddOf : List (Tm Var) → Tm Var → Prop
  | one (t : Tm Var) : IsAddOf [t] t
  | comb {as bs : List (Tm Var)} {ta tb : Tm Var} :
      IsAddOf as ta → IsAddOf bs tb → IsAddOf (as ++ bs) (ta + tb)

theorem isAddOf_summandsOf : ∀ (t : Tm Var), IsAddOf (summandsOf t) t := by
  intro t
  induction t with
  | var v => exact IsAddOf.one _
  | func f args ih =>
      cases f with
      | d => exact IsAddOf.one _
      | e => exact IsAddOf.one _
      | app => exact IsAddOf.one _
      | add =>
          let i0 : Fin (S3.arity Sym.add) := ⟨0, by decide⟩
          let i1 : Fin (S3.arity Sym.add) := ⟨1, by decide⟩
          have hargs : (Term.func (S := S3) Sym.add args)
                        = args i0 + args i1 := by
            change Term.func (S := S3) Sym.add args
                 = Term.func (S := S3) Sym.add ![args i0, args i1]
            congr 1
            funext i; fin_cases i <;> rfl
          rw [hargs]
          change IsAddOf (summandsOf (args i0) ++ summandsOf (args i1))
                  (args i0 + args i1)
          exact IsAddOf.comb (ih i0) (ih i1)

/-! Length-indexed rewriting. The paper's induction is on "`n` such
    that the term rewrites to `e` in `n` steps"; `RewN n t u`
    exposes that index. The two helpers below convert between
    `RewN`, `Rewrite.toDerivable`, and `RewriteStar`. -/

private def RewN : ℕ → Tm Var → Tm Var → Prop
  | 0,     t, u => t = u
  | n + 1, t, u => ∃ v, Rewrite t v ∧ RewN n v u

private theorem rewN_of_rewriteStar : ∀ {t u : Tm Var},
    RewriteStar t u → ∃ n, RewN n t u := by
  intro t u h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head step _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, _, step, hn⟩

private theorem rewN_toEquiv : ∀ {n : ℕ} {t u : Tm Var}, RewN n t u → t ≡ u
  | 0, _, _, h => h ▸ Equiv.refl _
  | _ + 1, _, _, ⟨_, hr, hn⟩ =>
      Equiv.trans (Rewrite.toDerivable hr) (rewN_toEquiv hn)

private theorem rewN_to_rewriteStar : ∀ {n : ℕ} {t u : Tm Var},
    RewN n t u → RewriteStar t u
  | 0, _, _, h => h ▸ Relation.ReflTransGen.refl
  | _ + 1, _, _, ⟨_, hr, hn⟩ =>
      Relation.ReflTransGen.head hr (rewN_to_rewriteStar hn)

/-! Three small structural facts used to peel a sum back to `e`.
    If `a + b` is a normal form, then `a` itself is a normal form,
    and neither `a` nor `b` can be `e` (otherwise `addE`/`eAdd`
    would fire), and `a` cannot be a `+`-term (otherwise `addAssoc`
    would fire). The key structural lemma `isNF_left_add_e_of_rewN`
    then drives the proof of Proposition 14: if `u` is a normal form
    and `u + v →ⁿ e`, then `u = e` and `v →* e`. -/

private lemma isNF_left_of_add_isNF {a b : Tm Var}
    (h : IsNormalForm E_S3 (a + b)) :
    IsNormalForm E_S3 a := by
  intro u' hr
  have hr' : Rewrite
      ((![a, b] : Fin 2 → Tm Var) (0 : Fin 2)) u' := by simpa using hr
  have hcongr := Rewrite.congr (S := S3) (E := E_S3)
    Sym.add ![a, b] (0 : Fin 2) hr'
  have heq : (Term.func (S := S3) Sym.add
                (Function.update ![a, b] (0 : Fin 2) u')) = u' + b := by
    change _ = Term.func (S := S3) Sym.add ![u', b]
    congr 1; funext j
    fin_cases j <;> rfl
  rw [heq] at hcongr
  exact h _ hcongr

private lemma add_left_ne_e_of_isNF {a b : Tm Var}
    (h : IsNormalForm E_S3 (a + b)) : a ≠ Tm.e := by
  intro ha; subst ha
  exact h _ (Rewrite.eAdd b)

private lemma add_right_ne_e_of_isNF {a b : Tm Var}
    (h : IsNormalForm E_S3 (a + b)) : b ≠ Tm.e := by
  intro hb; subst hb
  exact h _ (Rewrite.addE a)

private lemma add_left_not_add_of_isNF {a b : Tm Var}
    (h : IsNormalForm E_S3 (a + b)) :
    ∀ x y, a ≠ x + y := by
  rintro x y rfl
  exact h _ (Rewrite.addAssoc x y b)

private theorem isNF_left_add_e_of_rewN :
    ∀ (n : ℕ) {u v : Tm Var},
      IsNormalForm E_S3 u →
      RewN n (u + v) Tm.e →
      u = Tm.e ∧ RewriteStar v Tm.e := by
  intro n
  induction n with
  | zero =>
      intro u v _ hrew
      change (u + v : Tm Var) = Tm.e at hrew
      injection hrew with hf
      cases hf
  | succ n IH =>
      intro u v hu hrew
      have hrew' : ∃ t', Rewrite (u + v) t' ∧
                          RewN n t' Tm.e := hrew
      obtain ⟨t', hstep, hrest⟩ := hrew'
      generalize hw : (u + v : Tm Var) = w at hstep
      cases hstep with
      | @step e he σ =>
          rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · -- **addE**: `u = σ 0`, `v = e`. From `RewN n (σ 0) e` and `u` NF,
            -- conclude `u = e` (and `v = e` via refl).
            injection hw with _ h_args
            have h0 := congrFun h_args 0
            have h1 := congrFun h_args 1
            simp only [Fin.isValue, Matrix.cons_val_zero, Tm.vx, Term.subst,
              Matrix.cons_val_one, Matrix.cons_val_fin_one, Tm.e_subst] at h0 h1
            subst h0; subst h1
            have hrest_clean : RewN n (σ 0) Tm.e := by
              simpa [Ax.addE, Tm.vx] using hrest
            have hstar : RewriteStar (σ 0) Tm.e :=
              Moss.Section3.rewN_to_rewriteStar hrest_clean
            exact ⟨RewriteStar.eq_of_isNormalForm hu hstar,
                   Relation.ReflTransGen.refl⟩
          · -- **eAdd**: `u = e`, `v = σ 0`. Conclude `u = e` (rfl) and
            -- `v →* e` from `RewN n (σ 0) e`.
            injection hw with _ h_args
            have h0 := congrFun h_args 0
            have h1 := congrFun h_args 1
            simp only [Fin.isValue, Matrix.cons_val_zero, Tm.vx, Tm.e_subst,
              Matrix.cons_val_one, Matrix.cons_val_fin_one, Term.subst] at h0 h1
            subst h0; subst h1
            have hrest_clean : RewN n (σ 0) Tm.e := by
              simpa [Ax.eAdd, Tm.vx] using hrest
            exact ⟨rfl, Moss.Section3.rewN_to_rewriteStar hrest_clean⟩
          · -- **addAssoc**: `u = σ 0 + σ 1`, `v = σ 2`. `u` NF means
            -- `σ 0 ≠ e`, but the IH on `(σ 0, σ 1 + σ 2)` (using `σ 0`
            -- NF as a sub-summand of NF `u`) would conclude `σ 0 = e`
            -- , contradiction.
            injection hw with _ h_args
            have h0 := congrFun h_args 0
            have h1 := congrFun h_args 1
            simp only [Fin.isValue, Matrix.cons_val_zero, Tm.vx, Tm.vy, Tm.vz,
              Term.subst, Matrix.cons_val_one, Matrix.cons_val_fin_one,
              Tm.add_subst] at h0 h1
            subst h0; subst h1
            have hrest' : RewN n (σ 0 + (σ 1 + σ 2)) Tm.e := by
              simpa [Ax.addAssoc, Tm.vx, Tm.vy, Tm.vz] using hrest
            have h_s0_nf : IsNormalForm E_S3 (σ 0) :=
              isNF_left_of_add_isNF hu
            obtain ⟨h_s0_eq, _⟩ := IH h_s0_nf hrest'
            exact absurd h_s0_eq (add_left_ne_e_of_isNF hu)
          · exfalso; injection hw with hf _; cases hf
          · exfalso; injection hw with hf _; cases hf
          · exfalso; injection hw with hf _; cases hf
          · exfalso; injection hw with hf _; cases hf
      | @congr f args i u' hr =>
          cases f with
          | d => exfalso; injection hw with hf _; cases hf
          | e => exfalso; injection hw with hf _; cases hf
          | app => exfalso; injection hw with hf _; cases hf
          | add =>
              injection hw with _ h_args
              have hargs_eq : args = ![u, v] := by
                funext j; fin_cases j
                · exact (congrFun h_args 0).symm
                · exact (congrFun h_args 1).symm
              subst hargs_eq
              fin_cases i
              · -- i = 0: rewrite inside `u`. But `u` is NF , contradiction.
                exfalso
                have hr' : Rewrite u u' := by
                  simpa using hr
                exact hu u' hr'
              · -- i = 1: rewrite inside `v`. New pair `(u, v')`. Apply IH.
                have hr' : Rewrite v u' := by
                  simpa using hr
                have hrest' : RewN n (u + u') Tm.e := by
                  have heq : (Term.func (S := S3) Sym.add
                                (Function.update ![u, v]
                                  ((fun i : Fin (S3.arity Sym.add) => i)
                                    ⟨1, by decide⟩) u')) = u + u' := by
                    change _ = Term.func (S := S3) Sym.add ![u, u']
                    congr 1; funext j; fin_cases j <;> rfl
                  rw [heq] at hrest; exact hrest
                obtain ⟨hu_eq, hu'_star⟩ := IH hu hrest'
                refine ⟨hu_eq, ?_⟩
                exact Relation.ReflTransGen.head hr' hu'_star

theorem add_equiv_e {a b : Tm Var} (h : (a + b) ≡ Tm.e) :
    (a ≡ Tm.e) ∧ (b ≡ Tm.e) := by
  -- 1. (a + b) →* e.
  have hab_to_e : RewriteStar (a + b) Tm.e :=
    (equiv_e_iff_rewriteStar_e _).mp h
  -- 2. (a + b) →* nf a + nf b via congr at both positions.
  have hab_to_nf : RewriteStar (a + b) (nf a + nf b) := by
    have hstar : ∀ i : Fin (S3.arity Sym.add),
        RewriteStar
          ((![a, b] : Fin 2 → Tm Var) i) ((![nf a, nf b] : Fin 2 → Tm Var) i) := by
      intro i; fin_cases i
      · simpa using rewriteStar_nf a
      · simpa using rewriteStar_nf b
    have := RewriteStar.func (E := E_S3)
              (f := Sym.add) (a₁ := ![a, b]) (a₂ := ![nf a, nf b]) hstar
    change RewriteStar
            (Term.func Sym.add ![a, b]) (Term.func Sym.add ![nf a, nf b]) at this
    exact this
  -- 3. By confluence, nf a + nf b and e join. Since e is NF, the join is e.
  obtain ⟨w, hw1, hw2⟩ := confluent_E_S3 hab_to_nf hab_to_e
  have hw_eq : w = Tm.e :=
    (RewriteStar.eq_of_isNormalForm Tm.e_isNF hw2).symm
  subst hw_eq
  -- hw1 : RewriteStar (nf a + nf b) e
  obtain ⟨m, hm⟩ := rewN_of_rewriteStar hw1
  -- 4. Apply isNF_left_add_e_of_rewN with u = nf a (NF) to get nf a = e ∧ nf b →* e.
  obtain ⟨h_nfa_e, h_nfb_star⟩ := isNF_left_add_e_of_rewN m (nf_isNormalForm a) hm
  -- 5. nf b →* e and nf b NF gives nf b = e.
  have h_nfb_e : nf b = Tm.e :=
    RewriteStar.eq_of_isNormalForm (nf_isNormalForm b) h_nfb_star
  -- 6. Convert back to ≡.
  refine ⟨?_, ?_⟩
  · rw [equiv_iff_nf_eq, nf_eq_self_of_isNF Tm.e_isNF]; exact h_nfa_e
  · rw [equiv_iff_nf_eq, nf_eq_self_of_isNF Tm.e_isNF]; exact h_nfb_e

theorem mem_equiv_e_of_isAddOf_of_equiv_e :
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
      have ⟨hta, htb⟩ := add_equiv_e h
      rcases List.mem_append.mp hu with h_in_as | h_in_bs
      · exact ihAs hta u h_in_as
      · exact ihBs htb u h_in_bs

theorem mem_equiv_e_of_rewN (n : ℕ) {t : Tm Var} (hrew : RewN n t Tm.e)
    {us : List (Tm Var)} (hAdd : IsAddOf us t) (u : Tm Var) (hu : u ∈ us) :
    u ≡ Tm.e :=
  mem_equiv_e_of_isAddOf_of_equiv_e hAdd (rewN_toEquiv (n := n) hrew) u hu

theorem mem_summandsOf_equiv_e {t : Tm Var}
    (h : t ≡ Tm.e) : ∀ s ∈ summandsOf t, (s ≡ Tm.e) :=
  mem_equiv_e_of_isAddOf_of_equiv_e (isAddOf_summandsOf t) h

/-! ### Proposition 15

The paper: "For all normal forms `t ≠ e` and all normal forms `u`:
(1) `e` does not occur in `t`; (2) `nf (t @ u) ∈ {e} ∪ N@`; (3) if
`nf (t @ u) = e`, then `u = e`."

We split the formalisation in two: part (1) relies on a syntactic
predicate `occursE`, established by mutual induction on `IsN`,
`IsNApp`, `IsNAdd`, `IsNAddAtom`; parts (2) and (3) are then proved
together by the same fourfold induction, with the `t = d` base case
factored out as the auxiliary `prop15_d_case`. -/

/-! Part (1) of Proposition 15. Define `occursE t` to mean "the
    constant `e` appears somewhere inside `t`", and prove that no
    `IsN`-element apart from `e` itself satisfies it. The induction
    matches the four mutual inductives. -/

def occursE : Tm Var → Prop
  | Term.var _              => False
  | Term.func Sym.e _       => True
  | Term.func Sym.d _       => False
  | Term.func Sym.add args  =>
      occursE (args (0 : Fin 2)) ∨ occursE (args (1 : Fin 2))
  | Term.func Sym.app args  =>
      occursE (args (0 : Fin 2)) ∨ occursE (args (1 : Fin 2))

@[simp] lemma occursE_d : ¬ occursE (Tm.d : Tm Var) := by
  intro h; exact h

@[simp] lemma occursE_e : occursE (Tm.e : Tm Var) := by
  trivial

@[simp] lemma occursE_add (a b : Tm Var) :
    occursE (a + b) ↔ occursE a ∨ occursE b := by
  change occursE (Term.func Sym.add ![a, b]) ↔ _
  change (occursE ((![a, b] : Fin 2 → Tm Var) 0)
        ∨ occursE ((![a, b] : Fin 2 → Tm Var) 1)) ↔ _
  exact Iff.rfl

@[simp] lemma occursE_app (a b : Tm Var) :
    occursE (a ∘ₐ b) ↔ occursE a ∨ occursE b := by
  change occursE (Term.func Sym.app ![a, b]) ↔ _
  change (occursE ((![a, b] : Fin 2 → Tm Var) 0)
        ∨ occursE ((![a, b] : Fin 2 → Tm Var) 1)) ↔ _
  exact Iff.rfl

/-! No element of `N` apart from `e` itself contains `e`. -/
mutual
theorem IsN.not_occursE : ∀ {t : Tm Var}, IsN t → t ≠ Tm.e → ¬ occursE t
  | _, .d,        _   => by simp
  | _, .e,        hne => (hne rfl).elim
  | _, .ofApp h,  _   => IsNApp.not_occursE h
  | _, .ofAdd h,  _   => IsNAdd.not_occursE h

theorem IsNApp.not_occursE : ∀ {t : Tm Var}, IsNApp t → ¬ occursE t
  | _, @IsNApp.mk s hs hne => by
      simp only [occursE_app, occursE_d, false_or]
      exact IsN.not_occursE hs hne

theorem IsNAdd.not_occursE : ∀ {t : Tm Var}, IsNAdd t → ¬ occursE t
  | _, @IsNAdd.base a b ha hb => by
      simp only [occursE_add, not_or]
      exact ⟨IsNAddAtom.not_occursE ha, IsNAddAtom.not_occursE hb⟩
  | _, @IsNAdd.cons a b ha hb => by
      simp only [occursE_add, not_or]
      exact ⟨IsNAddAtom.not_occursE ha, IsNAdd.not_occursE hb⟩

theorem IsNAddAtom.not_occursE : ∀ {t : Tm Var}, IsNAddAtom t → ¬ occursE t
  | _, .d        => by simp
  | _, .ofApp h  => IsNApp.not_occursE h
end

theorem not_occursE_of_isNormalForm
    {t : Tm Var} (hcl : IsClosed t)
    (hnf : IsNormalForm E_S3 t) (hne : t ≠ Tm.e) :
    ¬ occursE t :=
  IsN.not_occursE (isN_of_isNormalForm hcl hnf) hne

/-! Before we can lift `IsN` and `occursE` through rewriting, we
    need the obvious projections of `IsClosed` for compound terms:
    if `a + b` (resp. `a ∘ₐ b`) is closed, so are `a` and `b`. The
    direct `cases` on `IsClosed (a + b)` triggers a dependent-elim
    η-failure on `Matrix.cons`; we generalise the indexed term and
    discharge the residual goals with `injection`. -/

namespace IsClosed

lemma add_left {a b : Tm Var} (h : IsClosed (a + b)) : IsClosed a := by
  generalize hw : (a + b : Tm Var) = w at h
  cases h with
  | d =>
      change Term.func (S := S3) Sym.add ![a, b] = Term.func (S := S3) Sym.d Fin.elim0 at hw
      injection hw with hf _; cases hf
  | e =>
      change Term.func (S := S3) Sym.add ![a, b] = Term.func (S := S3) Sym.e Fin.elim0 at hw
      injection hw with hf _; cases hf
  | @add α β hα _ =>
      change Term.func (S := S3) Sym.add ![a, b] = Term.func (S := S3) Sym.add ![α, β] at hw
      injection hw with _ hargs
      have h0 : a = α := by
        have h := congrFun hargs 0
        simpa using h
      subst h0
      exact hα
  | @app α β _ _ =>
      change Term.func (S := S3) Sym.add ![a, b] = Term.func (S := S3) Sym.app ![α, β] at hw
      injection hw with hf _; cases hf

lemma add_right {a b : Tm Var} (h : IsClosed (a + b)) : IsClosed b := by
  generalize hw : (a + b : Tm Var) = w at h
  cases h with
  | d =>
      change Term.func (S := S3) Sym.add ![a, b] = Term.func (S := S3) Sym.d Fin.elim0 at hw
      injection hw with hf _; cases hf
  | e =>
      change Term.func (S := S3) Sym.add ![a, b] = Term.func (S := S3) Sym.e Fin.elim0 at hw
      injection hw with hf _; cases hf
  | @add α β _ hβ =>
      change Term.func (S := S3) Sym.add ![a, b] = Term.func (S := S3) Sym.add ![α, β] at hw
      injection hw with _ hargs
      have h1 : b = β := by
        have h := congrFun hargs 1
        simpa using h
      subst h1
      exact hβ
  | @app α β _ _ =>
      change Term.func (S := S3) Sym.add ![a, b] = Term.func (S := S3) Sym.app ![α, β] at hw
      injection hw with hf _; cases hf

lemma app_left {a b : Tm Var} (h : IsClosed (a ∘ₐ b)) : IsClosed a := by
  generalize hw : (a ∘ₐ b : Tm Var) = w at h
  cases h with
  | d =>
      change Term.func (S := S3) Sym.app ![a, b] = Term.func (S := S3) Sym.d Fin.elim0 at hw
      injection hw with hf _; cases hf
  | e =>
      change Term.func (S := S3) Sym.app ![a, b] = Term.func (S := S3) Sym.e Fin.elim0 at hw
      injection hw with hf _; cases hf
  | @add α β _ _ =>
      change Term.func (S := S3) Sym.app ![a, b] = Term.func (S := S3) Sym.add ![α, β] at hw
      injection hw with hf _; cases hf
  | @app α β hα _ =>
      change Term.func (S := S3) Sym.app ![a, b] = Term.func (S := S3) Sym.app ![α, β] at hw
      injection hw with _ hargs
      have h0 : a = α := by
        have h := congrFun hargs 0
        simpa using h
      subst h0
      exact hα

lemma app_right {a b : Tm Var} (h : IsClosed (a ∘ₐ b)) : IsClosed b := by
  generalize hw : (a ∘ₐ b : Tm Var) = w at h
  cases h with
  | d =>
      change Term.func (S := S3) Sym.app ![a, b] = Term.func (S := S3) Sym.d Fin.elim0 at hw
      injection hw with hf _; cases hf
  | e =>
      change Term.func (S := S3) Sym.app ![a, b] = Term.func (S := S3) Sym.e Fin.elim0 at hw
      injection hw with hf _; cases hf
  | @add α β _ _ =>
      change Term.func (S := S3) Sym.app ![a, b] = Term.func (S := S3) Sym.add ![α, β] at hw
      injection hw with hf _; cases hf
  | @app α β _ hβ =>
      change Term.func (S := S3) Sym.app ![a, b] = Term.func (S := S3) Sym.app ![α, β] at hw
      injection hw with _ hargs
      have h1 : b = β := by
        have h := congrFun hargs 1
        simpa using h
      subst h1
      exact hβ

end IsClosed

/-! Closedness is preserved under rewriting. For each of the seven
    Figure 2 axioms, the right-hand side is built from sub-terms of
    the left-hand side under the same substitution; the closure of
    the lhs-instance therefore propagates to the rhs-instance. The
    `congr` case lifts the inductive hypothesis through one
    argument position. We then chain to `RewriteStar`, and from
    there to `nf`. -/

theorem isClosed_of_rewrite :
    ∀ {a b : Tm Var}, Rewrite a b →
      IsClosed a → IsClosed b := by
  intro a b h
  induction h with
  | @step e he σ =>
      intro hcl
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Ax.addE, Ax.eAdd, Ax.addAssoc, Ax.addApp, Ax.dApp, Ax.eApp,
          Ax.dAppE, Tm.add_subst, Tm.app_subst, Tm.d_subst, Tm.e_subst] at hcl ⊢
      · exact hcl.add_left
      · exact hcl.add_right
      · exact .add hcl.add_left.add_left (.add hcl.add_left.add_right hcl.add_right)
      · exact .app hcl.app_left.add_right (.app hcl.app_left.add_left hcl.app_right)
      · exact .app hcl.app_left.app_right (.add hcl.app_right hcl.app_left.app_right)
      · exact hcl.app_right
      · exact .e
  | @congr f args i u' hr ih =>
      intro hcl
      cases f with
      | d => exact i.elim0
      | e => exact i.elim0
      | add =>
          let i0 : Fin (S3.arity Sym.add) := ⟨0, by decide⟩
          let i1 : Fin (S3.arity Sym.add) := ⟨1, by decide⟩
          have heq : args = ![args i0, args i1] := by funext j; fin_cases j <;> rfl
          rw [heq] at hcl
          have h0 := IsClosed.add_left hcl
          have h1 := IsClosed.add_right hcl
          fin_cases i
          · rw [show Function.update args i0 u' = ![u', args i1] from by
                  funext j; fin_cases j
                  · exact Function.update_self ..
                  · exact Function.update_of_ne (by decide : i1 ≠ i0) _ _]
            exact .add (ih h0) h1
          · rw [show Function.update args i1 u' = ![args i0, u'] from by
                  funext j; fin_cases j
                  · exact Function.update_of_ne (by decide : i0 ≠ i1) _ _
                  · exact Function.update_self ..]
            exact .add h0 (ih h1)
      | app =>
          let i0 : Fin (S3.arity Sym.app) := ⟨0, by decide⟩
          let i1 : Fin (S3.arity Sym.app) := ⟨1, by decide⟩
          have heq : args = ![args i0, args i1] := by funext j; fin_cases j <;> rfl
          rw [heq] at hcl
          have h0 := IsClosed.app_left hcl
          have h1 := IsClosed.app_right hcl
          fin_cases i
          · rw [show Function.update args i0 u' = ![u', args i1] from by
                  funext j; fin_cases j
                  · exact Function.update_self ..
                  · exact Function.update_of_ne (by decide : i1 ≠ i0) _ _]
            exact .app (ih h0) h1
          · rw [show Function.update args i1 u' = ![args i0, u'] from by
                  funext j; fin_cases j
                  · exact Function.update_of_ne (by decide : i0 ≠ i1) _ _
                  · exact Function.update_self ..]
            exact .app h0 (ih h1)

theorem isClosed_of_rewriteStar
    {a b : Tm Var} (h : RewriteStar a b)
    (hcl : IsClosed a) : IsClosed b := by
  induction h with
  | refl => exact hcl
  | tail _ hr ih => exact isClosed_of_rewrite hr ih

theorem isClosed_nf {t : Tm Var} (hcl : IsClosed t) : IsClosed (nf t) :=
  isClosed_of_rewriteStar (rewriteStar_nf t) hcl

theorem isN_nf {t : Tm Var} (hcl : IsClosed t) : IsN (nf t) :=
  isN_of_isNormalForm (isClosed_nf hcl) (nf_isNormalForm t)

/-! Conversely, every `IsN`-element is closed: an immediate
    induction over the four mutual inductives. -/

mutual
theorem IsN.isClosed : ∀ {t : Tm Var}, IsN t → IsClosed t
  | _, .d        => IsClosed.d
  | _, .e        => IsClosed.e
  | _, .ofApp h  => IsNApp.isClosed h
  | _, .ofAdd h  => IsNAdd.isClosed h

theorem IsNApp.isClosed : ∀ {t : Tm Var}, IsNApp t → IsClosed t
  | _, @IsNApp.mk s hs _ => IsClosed.app IsClosed.d (IsN.isClosed hs)

theorem IsNAdd.isClosed : ∀ {t : Tm Var}, IsNAdd t → IsClosed t
  | _, @IsNAdd.base a b ha hb =>
      IsClosed.add (IsNAddAtom.isClosed ha) (IsNAddAtom.isClosed hb)
  | _, @IsNAdd.cons a b ha hb =>
      IsClosed.add (IsNAddAtom.isClosed ha) (IsNAdd.isClosed hb)

theorem IsNAddAtom.isClosed : ∀ {t : Tm Var}, IsNAddAtom t → IsClosed t
  | _, .d        => IsClosed.d
  | _, .ofApp h  => IsNApp.isClosed h
end

/-! Parts (2) and (3) of Proposition 15 are proved together. The
    statement (over a generic closed `u`, not just an `IsN` `u`,
    because the IH for `t = d ∘ₐ s` is invoked at `u + s`) reads:

      `nf (t ∘ₐ u) ∈ {e} ∪ N@`   (encoded as a disjunction)
      `nf (t ∘ₐ u) = e → nf u = e`.

    The `t = d` base is factored as `prop15_d_case`. The wrapper
    `prop15_app` then specialises `u` to a normal form and turns
    the conclusion `nf u = e` into `u = e`, recovering the paper's
    statement. -/

private theorem prop15_d_case (u : Tm Var) (hu : IsClosed u) :
    (nf (Tm.d ∘ₐ u) = Tm.e ∨ IsNApp (nf (Tm.d ∘ₐ u)))
    ∧ (nf (Tm.d ∘ₐ u) = Tm.e → nf u = Tm.e) := by
  have hnu_isN : IsN (nf u) := isN_nf hu
  have h_d_u_equiv : (Tm.d ∘ₐ u) ≡ (Tm.d ∘ₐ nf u) :=
    Equiv.appRightCongr Tm.d
      (RewriteStar.toDerivable (rewriteStar_nf u))
  by_cases h : nf u = Tm.e
  · refine ⟨Or.inl ?_, fun _ => h⟩
    have h_d_e : (Tm.d ∘ₐ u) ≡ Tm.e := by
      have := h_d_u_equiv
      rw [h] at this
      exact Equiv.trans this Equiv.dAppE
    have := nf_eq_of_equiv h_d_e
    rw [nf_eq_self_of_isNF Tm.e_isNF] at this
    exact this
  · have h_isnf : IsNormalForm E_S3 (Tm.d ∘ₐ nf u) :=
      IsNApp.isNormalForm (IsNApp.mk hnu_isN h)
    have hnf_eq : nf (Tm.d ∘ₐ u) = Tm.d ∘ₐ nf u := by
      rw [nf_eq_of_equiv h_d_u_equiv, nf_eq_self_of_isNF h_isnf]
    refine ⟨Or.inr ?_, ?_⟩
    · rw [hnf_eq]; exact IsNApp.mk hnu_isN h
    · intro hnfeq
      exfalso
      rw [hnf_eq] at hnfeq
      change Term.func (S := S3) Sym.app ![Tm.d, nf u]
              = Term.func (S := S3) Sym.e Fin.elim0 at hnfeq
      injection hnfeq with hf _; cases hf

mutual

theorem IsN.prop15 :
    ∀ {t : Tm Var}, IsN t → t ≠ Tm.e → ∀ u : Tm Var, IsClosed u →
      (nf (t ∘ₐ u) = Tm.e ∨ IsNApp (nf (t ∘ₐ u)))
      ∧ (nf (t ∘ₐ u) = Tm.e → nf u = Tm.e)
  | _, .d, _, u, hu => prop15_d_case u hu
  | _, .e, hne, _, _ => (hne rfl).elim
  | _, .ofApp h, _, u, hu => IsNApp.prop15 h u hu
  | _, .ofAdd h, _, u, hu => IsNAdd.prop15 h u hu

theorem IsNApp.prop15 :
    ∀ {t : Tm Var}, IsNApp t → ∀ u : Tm Var, IsClosed u →
      (nf (t ∘ₐ u) = Tm.e ∨ IsNApp (nf (t ∘ₐ u)))
      ∧ (nf (t ∘ₐ u) = Tm.e → nf u = Tm.e)
  | _, @IsNApp.mk s hs hne_s, u, hu => by
      have heq : ((Tm.d ∘ₐ s) ∘ₐ u) ≡ (s ∘ₐ (u + s)) := Equiv.dApp s u
      have hnf_eq : nf ((Tm.d ∘ₐ s) ∘ₐ u) = nf (s ∘ₐ (u + s)) :=
        nf_eq_of_equiv heq
      have hcl_us : IsClosed (u + s) := IsClosed.add hu (IsN.isClosed hs)
      obtain ⟨h2, h3⟩ := IsN.prop15 hs hne_s (u + s) hcl_us
      refine ⟨?_, ?_⟩
      · rw [hnf_eq]; exact h2
      · intro hnfeq
        rw [hnf_eq] at hnfeq
        have h_us_e_nf : nf (u + s) = Tm.e := h3 hnfeq
        have h_us_e : (u + s) ≡ Tm.e := by
          rw [equiv_iff_nf_eq, nf_eq_self_of_isNF Tm.e_isNF]; exact h_us_e_nf
        have h_u_e : u ≡ Tm.e := (add_equiv_e h_us_e).1
        rw [equiv_iff_nf_eq, nf_eq_self_of_isNF Tm.e_isNF] at h_u_e
        exact h_u_e

theorem IsNAdd.prop15 :
    ∀ {t : Tm Var}, IsNAdd t → ∀ u : Tm Var, IsClosed u →
      (nf (t ∘ₐ u) = Tm.e ∨ IsNApp (nf (t ∘ₐ u)))
      ∧ (nf (t ∘ₐ u) = Tm.e → nf u = Tm.e)
  | _, @IsNAdd.base a b ha hb, u, hu => by
      have heq : ((a + b) ∘ₐ u) ≡ (b ∘ₐ (a ∘ₐ u)) := Equiv.addApp a b u
      have hnf_eq : nf ((a + b) ∘ₐ u) = nf (b ∘ₐ (a ∘ₐ u)) := nf_eq_of_equiv heq
      have hcl_a : IsClosed a := IsNAddAtom.isClosed ha
      have hcl_au : IsClosed (a ∘ₐ u) := IsClosed.app hcl_a hu
      obtain ⟨h2_b, h3_b⟩ := IsNAddAtom.prop15 hb (a ∘ₐ u) hcl_au
      refine ⟨?_, ?_⟩
      · rw [hnf_eq]; exact h2_b
      · intro hnfeq
        rw [hnf_eq] at hnfeq
        have h_au_e : nf (a ∘ₐ u) = Tm.e := h3_b hnfeq
        obtain ⟨_, h3_a⟩ := IsNAddAtom.prop15 ha u hu
        exact h3_a h_au_e
  | _, @IsNAdd.cons a b ha hb, u, hu => by
      have heq : ((a + b) ∘ₐ u) ≡ (b ∘ₐ (a ∘ₐ u)) := Equiv.addApp a b u
      have hnf_eq : nf ((a + b) ∘ₐ u) = nf (b ∘ₐ (a ∘ₐ u)) := nf_eq_of_equiv heq
      have hcl_a : IsClosed a := IsNAddAtom.isClosed ha
      have hcl_au : IsClosed (a ∘ₐ u) := IsClosed.app hcl_a hu
      obtain ⟨h2_b, h3_b⟩ := IsNAdd.prop15 hb (a ∘ₐ u) hcl_au
      refine ⟨?_, ?_⟩
      · rw [hnf_eq]; exact h2_b
      · intro hnfeq
        rw [hnf_eq] at hnfeq
        have h_au_e : nf (a ∘ₐ u) = Tm.e := h3_b hnfeq
        obtain ⟨_, h3_a⟩ := IsNAddAtom.prop15 ha u hu
        exact h3_a h_au_e

theorem IsNAddAtom.prop15 :
    ∀ {t : Tm Var}, IsNAddAtom t → ∀ u : Tm Var, IsClosed u →
      (nf (t ∘ₐ u) = Tm.e ∨ IsNApp (nf (t ∘ₐ u)))
      ∧ (nf (t ∘ₐ u) = Tm.e → nf u = Tm.e)
  | _, .d, u, hu => prop15_d_case u hu
  | _, .ofApp h, u, hu => IsNApp.prop15 h u hu

end

theorem prop15_app
    {t : Tm Var} (hcl_t : IsClosed t)
    (hnf_t : IsNormalForm E_S3 t)
    (hne : t ≠ Tm.e)
    {u : Tm Var} (hcl_u : IsClosed u)
    (hnf_u : IsNormalForm E_S3 u) :
    (nf (t ∘ₐ u) = Tm.e ∨ IsNApp (nf (t ∘ₐ u)))
      ∧ (nf (t ∘ₐ u) = Tm.e → u = Tm.e) := by
  have ht_isN := isN_of_isNormalForm hcl_t hnf_t
  obtain ⟨h2, h3⟩ := IsN.prop15 ht_isN hne u hcl_u
  refine ⟨h2, fun hnfeq => ?_⟩
  have h := h3 hnfeq
  rw [nf_eq_self_of_isNF hnf_u] at h
  exact h

/-! ## §3.4 Characterization of quines

We can now prove Section 3's main classification. The proof rests
on a single numerical invariant introduced in Definition 16: the
`d`-count of a term, `dCt t` , the number of `d` constants in it.

The plan is the paper's: Definition 16 (counter) → Proposition 17
(small `dCt` forces `e` or `d`) → Lemma 18 (rewriting does not
decrease `dCt`, in the absence of `e`) → Theorem 19 (uniqueness of
quines) → Proposition 20 (no cycles of length ≥ 2). -/

/-! ### Definition 16

The `d`-count is defined by structural recursion: `dCt e = 0`,
`dCt d = 1`, and `dCt` distributes over `+` and `∘ₐ`. -/

def dCt : Tm Var → ℕ
  | Term.var _              => 0
  | Term.func Sym.d _       => 1
  | Term.func Sym.e _       => 0
  | Term.func Sym.add args  =>
      dCt (args (0 : Fin 2)) + dCt (args (1 : Fin 2))
  | Term.func Sym.app args  =>
      dCt (args (0 : Fin 2)) + dCt (args (1 : Fin 2))

@[simp] lemma dCt_d : dCt (Tm.d : Tm Var) = 1 := rfl

@[simp] lemma dCt_e : dCt (Tm.e : Tm Var) = 0 := rfl

@[simp] lemma dCt_add (a b : Tm Var) :
    dCt (a + b) = dCt a + dCt b := by
  change dCt (Term.func Sym.add ![a, b]) = _
  change dCt ((![a, b] : Fin 2 → Tm Var) 0)
        + dCt ((![a, b] : Fin 2 → Tm Var) 1) = _
  rfl

@[simp] lemma dCt_app (a b : Tm Var) :
    dCt (a ∘ₐ b) = dCt a + dCt b := by
  change dCt (Term.func Sym.app ![a, b]) = _
  change dCt ((![a, b] : Fin 2 → Tm Var) 0)
        + dCt ((![a, b] : Fin 2 → Tm Var) 1) = _
  rfl

/-! ### Proposition 17

The paper: "The only normal form `t` with `dCt(t) = 0` is `e`, and
the only normal form `t` with `dCt(t) = 1` is `d`."

The proof traces the structure of `IsN`: every `IsNApp` term has
`dCt ≥ 1` (the leading `d`), every `IsNAdd` has `dCt ≥ 2` (each
summand contributes ≥ 1), and the constants are immediate. We
package the lower bounds as a four-way mutual recursion, then
specialise. -/

mutual
theorem IsN.dCt_pos_of_ne_e :
    ∀ {t : Tm Var}, IsN t → t ≠ Tm.e → 1 ≤ dCt t
  | _, .d,        _   => by simp
  | _, .e,        hne => (hne rfl).elim
  | _, .ofApp h,  _   => IsNApp.dCt_pos h
  | _, .ofAdd h,  _   => Nat.le_of_lt (IsNAdd.dCt_pos h)

theorem IsNApp.dCt_pos :
    ∀ {t : Tm Var}, IsNApp t → 1 ≤ dCt t
  | _, @IsNApp.mk s _ _ => by
      simp only [dCt_app, dCt_d]
      exact Nat.le_add_right _ _

theorem IsNAdd.dCt_pos :
    ∀ {t : Tm Var}, IsNAdd t → 2 ≤ dCt t
  | _, @IsNAdd.base a b ha hb => by
      simp only [dCt_add]
      have h1 : 1 ≤ dCt a := IsNAddAtom.dCt_pos ha
      have h2 : 1 ≤ dCt b := IsNAddAtom.dCt_pos hb
      omega
  | _, @IsNAdd.cons a b ha hb => by
      simp only [dCt_add]
      have h1 : 1 ≤ dCt a := IsNAddAtom.dCt_pos ha
      have h2 : 2 ≤ dCt b := IsNAdd.dCt_pos hb
      omega

theorem IsNAddAtom.dCt_pos :
    ∀ {t : Tm Var}, IsNAddAtom t → 1 ≤ dCt t
  | _, .d        => by simp
  | _, .ofApp h  => IsNApp.dCt_pos h
end

theorem eq_e_of_dCt_zero {t : Tm Var} (hcl : IsClosed t)
    (hnf : IsNormalForm E_S3 t)
    (h0 : dCt t = 0) : t = Tm.e := by
  by_contra hne
  have h := IsN.dCt_pos_of_ne_e (isN_of_isNormalForm hcl hnf) hne
  omega

theorem eq_d_of_dCt_one {t : Tm Var} (hcl : IsClosed t)
    (hnf : IsNormalForm E_S3 t)
    (h1 : dCt t = 1) : t = Tm.d := by
  have hisN := isN_of_isNormalForm hcl hnf
  cases hisN with
  | d => rfl
  | e => simp [dCt_e] at h1
  | ofApp happ =>
      cases happ with
      | @mk s hs hne =>
          -- t = d ∘ₐ s, dCt t = 1 + dCt s = 1, so dCt s = 0.
          have hds : dCt s = 0 := by
            simp only [dCt_app, dCt_d] at h1; omega
          -- by IsN.dCt_pos_of_ne_e on s, s = e , contradicts hne.
          have hs_e : s = Tm.e := by
            by_contra hse
            have := IsN.dCt_pos_of_ne_e hs hse
            omega
          exact (hne hs_e).elim
  | ofAdd hadd =>
      have h2 : 2 ≤ dCt _ := IsNAdd.dCt_pos hadd
      omega

/-! ### Lemma 18

The paper: "Let `t` be a term in which `e` does not occur (not
necessarily a normal form). Then `dCt(nf(t)) ≥ dCt(t)`."

The reason `e`-freeness matters is exactly the rewrite rule
`d @ e → e`: it has `dCt 1` on the left and `0` on the right. Once
that rule is excluded, the only rule with a `d`-count change is
`(d @ x) @ y → x @ (y + x)`, which loses one `d` on the left but
introduces an extra copy of `x`; closedness plus `e`-freeness
forces `dCt x ≥ 1` (auxiliary `dCt_pos_of_isClosed_no_e`), so the
count is non-decreasing. We then chain through `RewriteStar` to
`nf`. -/

private theorem dCt_pos_of_isClosed_no_e :
    ∀ {t : Tm Var}, IsClosed t → ¬ occursE t → 1 ≤ dCt t := by
  intro t hcl
  induction hcl with
  | d => intro _; simp
  | e => intro h; exact (h occursE_e).elim
  | @add a b _ _ iha _ =>
      intro h
      rw [occursE_add, not_or] at h
      have := iha h.1
      rw [dCt_add]; omega
  | @app a b _ _ iha _ =>
      intro h
      rw [occursE_app, not_or] at h
      have := iha h.1
      rw [dCt_app]; omega

private theorem dCt_le_of_rewrite :
    ∀ {a b : Tm Var}, Rewrite a b →
      IsClosed a → ¬ occursE a → dCt a ≤ dCt b := by
  intro a b h
  induction h with
  | @step e he σ =>
      intro hcl hocc
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Ax.addE, Ax.eAdd, Ax.addAssoc, Ax.addApp, Ax.dApp, Ax.eApp,
          Ax.dAppE, Tm.add_subst, Tm.app_subst, Tm.d_subst, Tm.e_subst,
          dCt_add, dCt_app, dCt_d, dCt_e, occursE_add, occursE_app, occursE_e,
          occursE_d, not_or] at hcl hocc ⊢
      · exact Nat.le_refl (dCt (Term.subst σ Tm.vx) + 0)   -- addE
      · exact (hocc.1 trivial).elim                        -- eAdd
      · omega                                              -- addAssoc
      · omega                                              -- addApp
      · -- dApp: 1 + dCt(σ 0) + dCt(σ 1) ≤ dCt(σ 0) + (dCt(σ 1) + dCt(σ 0))
        have h_σ0_pos := dCt_pos_of_isClosed_no_e hcl.app_left.app_right
                            hocc.1.2
        omega
      · exact (hocc.1 trivial).elim                        -- eApp
      · exact (hocc.2 trivial).elim                        -- dAppE
  | @congr f args i u' hr ih =>
      intro hcl hocc
      cases f with
      | d => exact i.elim0
      | e => exact i.elim0
      | add =>
          let i0 : Fin (S3.arity Sym.add) := ⟨0, by decide⟩
          let i1 : Fin (S3.arity Sym.add) := ⟨1, by decide⟩
          have heq : args = ![args i0, args i1] := by funext j; fin_cases j <;> rfl
          rw [heq] at hcl hocc
          have h0_cl := IsClosed.add_left hcl
          have h1_cl := IsClosed.add_right hcl
          change ¬ occursE (args i0 + args i1) at hocc
          rw [occursE_add, not_or] at hocc
          fin_cases i
          · rw [show Function.update args i0 u' = ![u', args i1] from by
                  funext j; fin_cases j
                  · exact Function.update_self ..
                  · exact Function.update_of_ne (by decide : i1 ≠ i0) _ _]
            have hih : dCt (args i0) ≤ dCt u' := ih h0_cl hocc.1
            change dCt (args i0 + args i1) ≤ dCt (u' + args i1)
            rw [dCt_add, dCt_add]; omega
          · rw [show Function.update args i1 u' = ![args i0, u'] from by
                  funext j; fin_cases j
                  · exact Function.update_of_ne (by decide : i0 ≠ i1) _ _
                  · exact Function.update_self ..]
            have hih : dCt (args i1) ≤ dCt u' := ih h1_cl hocc.2
            change dCt (args i0 + args i1) ≤ dCt (args i0 + u')
            rw [dCt_add, dCt_add]; omega
      | app =>
          let i0 : Fin (S3.arity Sym.app) := ⟨0, by decide⟩
          let i1 : Fin (S3.arity Sym.app) := ⟨1, by decide⟩
          have heq : args = ![args i0, args i1] := by funext j; fin_cases j <;> rfl
          rw [heq] at hcl hocc
          have h0_cl := IsClosed.app_left hcl
          have h1_cl := IsClosed.app_right hcl
          change ¬ occursE (args i0 ∘ₐ args i1) at hocc
          rw [occursE_app, not_or] at hocc
          fin_cases i
          · rw [show Function.update args i0 u' = ![u', args i1] from by
                  funext j; fin_cases j
                  · exact Function.update_self ..
                  · exact Function.update_of_ne (by decide : i1 ≠ i0) _ _]
            have hih : dCt (args i0) ≤ dCt u' := ih h0_cl hocc.1
            change dCt (args i0 ∘ₐ args i1) ≤ dCt (u' ∘ₐ args i1)
            rw [dCt_app, dCt_app]; omega
          · rw [show Function.update args i1 u' = ![args i0, u'] from by
                  funext j; fin_cases j
                  · exact Function.update_of_ne (by decide : i0 ≠ i1) _ _
                  · exact Function.update_self ..]
            have hih : dCt (args i1) ≤ dCt u' := ih h1_cl hocc.2
            change dCt (args i0 ∘ₐ args i1) ≤ dCt (args i0 ∘ₐ u')
            rw [dCt_app, dCt_app]; omega

private theorem not_occursE_of_rewrite :
    ∀ {a b : Tm Var}, Rewrite a b →
      ¬ occursE a → ¬ occursE b := by
  intro a b h
  induction h with
  | @step e he σ =>
      intro hocc hbocc
      apply hocc
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Ax.addE, Ax.eAdd, Ax.addAssoc, Ax.addApp, Ax.dApp, Ax.eApp,
          Ax.dAppE, Tm.add_subst, Tm.app_subst, Tm.d_subst, Tm.e_subst,
          occursE_add, occursE_app, occursE_e, occursE_d] at hbocc ⊢ <;>
        tauto
  | @congr f args i u' hr ih =>
      intro hocc hbocc
      apply hocc
      cases f with
      | d => exact i.elim0
      | e => exact i.elim0
      | add =>
          let i0 : Fin (S3.arity Sym.add) := ⟨0, by decide⟩
          let i1 : Fin (S3.arity Sym.add) := ⟨1, by decide⟩
          have heq : args = ![args i0, args i1] := by funext j; fin_cases j <;> rfl
          rw [heq]
          change occursE (args i0 + args i1)
          rw [occursE_add]
          fin_cases i
          · rw [show Function.update args i0 u' = ![u', args i1] from by
                  funext j; fin_cases j
                  · exact Function.update_self ..
                  · exact Function.update_of_ne (by decide : i1 ≠ i0) _ _] at hbocc
            change occursE (u' + args i1) at hbocc
            rw [occursE_add] at hbocc
            rcases hbocc with h | h
            · exact Or.inl (by_contra fun hno => ih hno h)
            · exact Or.inr h
          · rw [show Function.update args i1 u' = ![args i0, u'] from by
                  funext j; fin_cases j
                  · exact Function.update_of_ne (by decide : i0 ≠ i1) _ _
                  · exact Function.update_self ..] at hbocc
            change occursE (args i0 + u') at hbocc
            rw [occursE_add] at hbocc
            rcases hbocc with h | h
            · exact Or.inl h
            · exact Or.inr (by_contra fun hno => ih hno h)
      | app =>
          let i0 : Fin (S3.arity Sym.app) := ⟨0, by decide⟩
          let i1 : Fin (S3.arity Sym.app) := ⟨1, by decide⟩
          have heq : args = ![args i0, args i1] := by funext j; fin_cases j <;> rfl
          rw [heq]
          change occursE (args i0 ∘ₐ args i1)
          rw [occursE_app]
          fin_cases i
          · rw [show Function.update args i0 u' = ![u', args i1] from by
                  funext j; fin_cases j
                  · exact Function.update_self ..
                  · exact Function.update_of_ne (by decide : i1 ≠ i0) _ _] at hbocc
            change occursE (u' ∘ₐ args i1) at hbocc
            rw [occursE_app] at hbocc
            rcases hbocc with h | h
            · exact Or.inl (by_contra fun hno => ih hno h)
            · exact Or.inr h
          · rw [show Function.update args i1 u' = ![args i0, u'] from by
                  funext j; fin_cases j
                  · exact Function.update_of_ne (by decide : i0 ≠ i1) _ _
                  · exact Function.update_self ..] at hbocc
            change occursE (args i0 ∘ₐ u') at hbocc
            rw [occursE_app] at hbocc
            rcases hbocc with h | h
            · exact Or.inl h
            · exact Or.inr (by_contra fun hno => ih hno h)

private theorem rewrite_step_invariant
    {a b : Tm Var} (h : Rewrite a b)
    (hcl : IsClosed a) (hocc : ¬ occursE a) :
    IsClosed b ∧ ¬ occursE b ∧ dCt a ≤ dCt b :=
  ⟨isClosed_of_rewrite h hcl,
   not_occursE_of_rewrite h hocc,
   dCt_le_of_rewrite h hcl hocc⟩

private theorem rewriteStar_invariant
    {a b : Tm Var} (h : RewriteStar a b)
    (hcl : IsClosed a) (hocc : ¬ occursE a) :
    IsClosed b ∧ ¬ occursE b ∧ dCt a ≤ dCt b := by
  induction h with
  | refl => exact ⟨hcl, hocc, le_refl _⟩
  | @tail x y _ hr ih =>
      obtain ⟨hxcl, hxocc, hxle⟩ := ih
      obtain ⟨hycl, hyocc, hyle⟩ := rewrite_step_invariant hr hxcl hxocc
      exact ⟨hycl, hyocc, le_trans hxle hyle⟩

theorem dCt_le_nf {t : Tm Var}
    (hcl : IsClosed t) (hocc : ¬ occursE t) : dCt t ≤ dCt (nf t) :=
  (rewriteStar_invariant (rewriteStar_nf t) hcl hocc).2.2

/-! ### Theorem 19: uniqueness of non-empty quines

The paper: "If `t` is a quine, then either `t = e` or else
`t = d @ d`."

The argument combines almost everything we have built so far. Let
`t` be a closed quine. By Proposition 13 we case-split on the
shape of `t` as a member of `N`: the constants `d` is excluded by a
direct calculation (`d @ e ≡ e ≠ d`), and `+`-terms are excluded by
Proposition 15 (a `+`-normal-form's `t @ e` cannot normalise back
to itself). We are left with `t = d ∘ₐ u` (Proposition 11), so the
quine equation `(d ∘ₐ u) ∘ₐ e ≡ d ∘ₐ u` reduces to
`u ∘ₐ u ≡ d ∘ₐ u`. Lemma 18 on `u ∘ₐ u` (closed, no-`e` via
Proposition 15(1)) gives `2 · dCt u ≤ 1 + dCt u`, hence `dCt u ≤ 1`,
and Proposition 17 forces `u = d`, i.e. `t = d ∘ₐ d`. -/

private theorem IsNApp.exists_eq {t : Tm Var} (h : IsNApp t) :
    ∃ s, t = Tm.d ∘ₐ s := by
  cases h with
  | mk _ _ => exact ⟨_, rfl⟩

private theorem IsNApp.exists_full {t : Tm Var} (h : IsNApp t) :
    ∃ s, IsN s ∧ s ≠ Tm.e ∧ t = Tm.d ∘ₐ s := by
  cases h with
  | mk hsN hsne => exact ⟨_, hsN, hsne, rfl⟩

theorem quine_eq_e_or_dd
    {t : Tm Var} (hcl : IsClosed t) (hq : IsQuine t) :
    t = Tm.e ∨ t = (Tm.d ∘ₐ Tm.d) := by
  obtain ⟨hnf, hquine_equiv⟩ := hq
  by_cases hte : t = Tm.e
  · exact Or.inl hte
  right
  cases isN_of_isNormalForm hcl hnf with
  | d =>
      -- t = d ⇒ d ∘ₐ e ≡ d, but d ∘ₐ e ≡ e ⇒ e ≡ d, contradicting NF distinctness.
      exfalso
      have h_ed : (Tm.e : Tm Var) ≡ Tm.d :=
        Equiv.trans (Equiv.symm Equiv.dAppE) hquine_equiv
      have heq : Tm.e = (Tm.d : Tm Var) := by
        have := nf_eq_of_equiv h_ed
        rwa [nf_eq_self_of_isNF Tm.e_isNF, nf_eq_self_of_isNF Tm.d_isNF] at this
      injection heq with hf _; cases hf
  | e => exact (hte rfl).elim
  | ofApp happ =>
      -- t = d ∘ₐ u with u ∈ N, u ≠ e. Then (d ∘ₐ u) ∘ₐ e ≡ u ∘ₐ u via dApp+eAdd,
      -- combined with the quine equation gives nf (u ∘ₐ u) = d ∘ₐ u. Lemma 18
      -- on u ∘ₐ u then forces 2·dCt u ≤ 1 + dCt u, hence dCt u = 1 (since ≥ 1
      -- by Prop 17), and Prop 17 ⇒ u = d.
      obtain ⟨u, hu, hue, rfl⟩ := happ.exists_full
      have hu_cl := IsN.isClosed hu
      have hu_no_e := IsN.not_occursE hu hue
      have h_nf_eq : nf (u ∘ₐ u) = Tm.d ∘ₐ u := by
        have h : (u ∘ₐ u) ≡ (Tm.d ∘ₐ u) :=
          ((Equiv.dApp u Tm.e).trans (Equiv.appRightCongr u (Equiv.eAdd u))).symm.trans
            hquine_equiv
        rw [nf_eq_of_equiv h, nf_eq_self_of_isNF (IsNApp.isNormalForm ⟨hu, hue⟩)]
      have h18 : dCt (u ∘ₐ u) ≤ dCt (Tm.d ∘ₐ u) := h_nf_eq ▸
        dCt_le_nf (IsClosed.app hu_cl hu_cl)
          (by rw [occursE_app, not_or]; exact ⟨hu_no_e, hu_no_e⟩)
      rw [dCt_app, dCt_app, dCt_d] at h18
      have hu_pos : 1 ≤ dCt u := IsN.dCt_pos_of_ne_e hu hue
      rw [eq_d_of_dCt_one hu_cl (IsN.isNormalForm hu) (by omega)]
  | ofAdd hadd =>
      -- t ∈ N+; Proposition 15(2) on t and e gives nf(t ∘ₐ e) ∈ {e} ∪ N@.
      -- Quine ⇒ this equals t, but t ∈ N+ has head `+`, not e or `d ∘ₐ _`.
      exfalso
      have h_quine_nf : nf (t ∘ₐ Tm.e) = t := by
        rw [nf_eq_of_equiv hquine_equiv]
        exact nf_eq_self_of_isNF (IsNAdd.isNormalForm hadd)
      have h_prop15 := IsN.prop15 (IsN.ofAdd hadd) hte Tm.e IsClosed.e
      rw [h_quine_nf] at h_prop15
      rcases h_prop15.1 with h_t_eq_e | h_t_isNApp
      · exact IsNAdd.ne_e hadd h_t_eq_e
      · obtain ⟨s, ht_eq⟩ := IsNApp.exists_eq h_t_isNApp
        cases hadd <;>
          (change Term.func (S := S3) Sym.add _ = Term.func (S := S3) Sym.app _ at ht_eq
           injection ht_eq with hf _; cases hf)

/-! ### Proposition 20: no cycles of length ≥ 2

The paper: "In the language of this section, there are no cycles
of length ≥ 2."

A *cycle of length n* is a sequence of `n` pairwise distinct closed
normal forms `t₀, …, t_{n-1}` with `tᵢ ∘ₐ e ≡ t_{(i+1) mod n}`. We
phrase it by quantifying over `Fin (n+2) → Tm Var`, which both
forces length ≥ 2 and provides modular indexing.

Following the paper: Proposition 15 forces each `tᵢ ∈ N@`, so
`tᵢ = d ∘ₐ uᵢ`. Lemma 18 applied to `uᵢ ∘ₐ uᵢ` yields
`2 · dCt uᵢ ≤ 1 + dCt u_{i+1}`. Summing over `Fin (n+2)` (the
shift `i ↦ i+1` is a permutation) gives the total `S` of `dCt uᵢ`
satisfies `2S ≤ (n+2) + S`, hence `S ≤ n + 2`. Each summand is `≥
1` (Proposition 17), so `S = n + 2` and each `dCt uᵢ = 1`.
Proposition 17 again forces each `uᵢ = d`, hence each `tᵢ = d ∘ₐ d`
, contradicting distinctness of `t₀` and `t₁`. -/

theorem no_cycle_of_length_ge_two
    {n : ℕ}
    (t : Fin (n + 2) → Tm Var)
    (hcl : ∀ i, IsClosed (t i))
    (hnf : ∀ i, IsNormalForm E_S3 (t i))
    (hinj : Function.Injective t)
    (hcycle : ∀ i, (t i ∘ₐ Tm.e) ≡ t (i + 1)) : False := by
  have ht_isN : ∀ i, IsN (t i) := fun i => isN_of_isNormalForm (hcl i) (hnf i)
  -- Step 1: no `t i` equals `e`. If it did, the cycle gives `t (i+1) = t i`,
  -- but `i + 1 ≠ i` in `Fin (n+2)`.
  have ht_ne_e : ∀ i, t i ≠ Tm.e := by
    intro i hie
    have h_eq : t (i + 1) = t i := by
      have h2 : t (i + 1) ≡ Tm.e :=
        Equiv.trans (Equiv.symm (hcycle i)) (hie ▸ Equiv.eApp Tm.e)
      have := nf_eq_of_equiv h2
      rw [nf_eq_self_of_isNF (hnf (i + 1)), nf_eq_self_of_isNF Tm.e_isNF] at this
      rw [this, hie]
    have hv : (i + 1 : Fin (n + 2)).val = i.val := congrArg Fin.val (hinj h_eq)
    have h_lt := i.isLt
    rw [Fin.val_add, show ((1 : Fin (n + 2)) : ℕ) = 1 by simp] at hv
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ h_lt) with h1 | h1
    · rw [Nat.mod_eq_of_lt (by omega)] at hv; omega
    · rw [show i.val + 1 = n + 2 by omega, Nat.mod_self] at hv; omega
  -- Step 2: each `t i` is in `N@` via Proposition 15(2) at index `i - 1`.
  have ht_isNApp : ∀ i, IsNApp (t i) := by
    intro i
    have hcyc : (t (i - 1) ∘ₐ Tm.e) ≡ t i := by
      have := hcycle (i - 1); rwa [sub_add_cancel] at this
    have h_nf : nf (t (i - 1) ∘ₐ Tm.e) = t i := by
      rw [nf_eq_of_equiv hcyc, nf_eq_self_of_isNF (hnf i)]
    have hp := IsN.prop15 (ht_isN (i - 1)) (ht_ne_e (i - 1)) Tm.e IsClosed.e
    rw [h_nf] at hp
    exact hp.1.resolve_left (ht_ne_e i)
  -- Step 3: extract `u i` with `t i = d ∘ₐ u i`.
  choose u hu_isN hu_ne hu_eq using fun i => IsNApp.exists_full (ht_isNApp i)
  -- Step 4: `2 · dCt (u i) ≤ 1 + dCt (u (i+1))` via Lemma 18 on `u i ∘ₐ u i`.
  have key : ∀ i, 2 * dCt (u i) ≤ 1 + dCt (u (i + 1)) := by
    intro i
    have hu_cl := IsN.isClosed (hu_isN i)
    have hu_no_e := IsN.not_occursE (hu_isN i) (hu_ne i)
    have h_nf : nf (u i ∘ₐ u i) = Tm.d ∘ₐ u (i + 1) := by
      have hcyc : (u i ∘ₐ u i) ≡ (Tm.d ∘ₐ u (i + 1)) :=
        ((Equiv.dApp (u i) Tm.e).trans
          (Equiv.appRightCongr _ (Equiv.eAdd _))).symm.trans
          ((hu_eq i ▸ hu_eq (i + 1) ▸ hcycle i : _))
      rw [nf_eq_of_equiv hcyc,
          nf_eq_self_of_isNF (by rw [← hu_eq (i + 1)]; exact hnf (i + 1))]
    have h_l18 := dCt_le_nf (IsClosed.app hu_cl hu_cl)
      (by rw [occursE_app, not_or]; exact ⟨hu_no_e, hu_no_e⟩)
    rw [h_nf, dCt_app, dCt_app, dCt_d] at h_l18
    omega
  -- Step 5+6+7: sum the key. Cyclic shift is a permutation, so the sum
  -- inequality reads `2S ≤ (n+2) + S`, i.e. `S ≤ n+2`. Together with the
  -- pointwise bound `1 ≤ dCt (u i)` (Prop 17), `Finset.sum_eq_sum_iff_of_le`
  -- collapses both to equality and forces each `dCt (u i) = 1`.
  have pos : ∀ i, 1 ≤ dCt (u i) := fun i =>
    IsN.dCt_pos_of_ne_e (hu_isN i) (hu_ne i)
  have sum_shift : ∑ i : Fin (n + 2), dCt (u (i + 1))
                  = ∑ i : Fin (n + 2), dCt (u i) :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin (n + 2))) _ _ (fun _ => rfl)
  set S := ∑ i : Fin (n + 2), dCt (u i)
  have hS_le : S ≤ n + 2 := by
    have h2S : 2 * S ≤ (n + 2) + S := by
      calc 2 * S
          = ∑ i : Fin (n + 2), 2 * dCt (u i) := Finset.mul_sum ..
        _ ≤ ∑ i : Fin (n + 2), (1 + dCt (u (i + 1))) :=
            Finset.sum_le_sum fun i _ => key i
        _ = (n + 2) + S := by simp [Finset.sum_add_distrib, sum_shift]
    omega
  have hS_ge : (n + 2) ≤ S := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (n + 2))))
      (g := fun i => dCt (u i)) (fun i _ => pos i)
    simpa using h
  have h_each_eq : ∀ i, dCt (u i) = 1 := by
    have h_sum_eq : ∑ i : Fin (n + 2), 1 = ∑ i : Fin (n + 2), dCt (u i) := by
      simp; omega
    have := (Finset.sum_eq_sum_iff_of_le (fun i _ => pos i)).mp h_sum_eq
    exact fun i => (this i (Finset.mem_univ i)).symm
  -- Step 8+9: Prop 17 ⇒ each `u i = d`, so `t i = d ∘ₐ d`. Then `t 0 = t 1`,
  -- contradicting injectivity.
  have h_t_eq_dd : ∀ i, t i = Tm.d ∘ₐ Tm.d := fun i => by
    rw [hu_eq i, eq_d_of_dCt_one (IsN.isClosed (hu_isN i))
      (IsN.isNormalForm (hu_isN i)) (h_each_eq i)]
  have hv : ((0 : Fin (n + 2)) : ℕ) = ((1 : Fin (n + 2)) : ℕ) :=
    congrArg Fin.val (hinj (h_t_eq_dd 0 |>.trans (h_t_eq_dd 1).symm))
  simp at hv

end Moss.Section3
