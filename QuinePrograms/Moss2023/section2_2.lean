import Mathlib

/-!
# §2.2: Combinatory algebras

The paper's §2.2 introduces combinatory logic as background for the
"diagonalization" perspective on Kleene's Second Recursion Theorem.
A *combinatory algebra* (Definition 4) is a set `D` with a binary
application and two distinguished elements `s` and `k` satisfying

    k · x · y     = x
    s · x · y · z = x · z · (y · z).

From these the standard derived combinators follow: `i = s · k · k`
is the identity (`i · x = x`) and `b = s · (k · s) · k` is
composition (`b · x · y · z = x · (y · z)`); these are Example 6 of
the paper.

The big result of §2.2 is *combinatory completeness* (Theorem 5):
"For every term `t(x₁, …, xₙ)` … there is an element `t* ∈ D` such
that `t* · d₁ · ⋯ · dₙ = t(d₁, …, dₙ)`." We formalise the
single-variable base case via bracket abstraction `abstr` on a small
syntax `PureTerm D`. That is enough for §2.2's payoff: the
*fixed-point construction* used in the second proof of Kleene's
Second Recursion Theorem (Theorem 1). Specifically, given any
one-variable term `g`, the term
`fixOf g := abstr (substSelf g) · abstr (substSelf g)` satisfies
`abstr g · fixOf g = fixOf g`. -/

namespace Moss.CombinatoryLogic

/-! ## Definition 4: combinatory algebras

A combinatory algebra is the structure `(D, ·, s, k)` of the paper,
with the two `s, k` axioms. Application is `⬝` (the paper's `·`,
left-associative). Once `s` and `k` are fixed, the identity `i` and
the composition combinator `b` are derivable; their characteristic
equations (Example 6) follow by short calculations from the two
axioms. -/

class CombinatoryAlgebra (D : Type*) where
  ap : D → D → D
  s : D
  k : D
  k_eq (x y : D) : ap (ap k x) y = x
  s_eq (x y z : D) : ap (ap (ap s x) y) z = ap (ap x z) (ap y z)

namespace CombinatoryAlgebra

variable {D : Type*} [CombinatoryAlgebra D]

scoped infixl:70 " ⬝ " => CombinatoryAlgebra.ap

def i : D := s ⬝ (k : D) ⬝ k

lemma i_apply (x : D) : (i : D) ⬝ x = x := by
  change s ⬝ (k : D) ⬝ k ⬝ x = x
  rw [s_eq, k_eq]

def b : D := s ⬝ (k ⬝ (s : D)) ⬝ k

lemma b_apply (x y z : D) : (b : D) ⬝ x ⬝ y ⬝ z = x ⬝ (y ⬝ z) :=
  calc (b : D) ⬝ x ⬝ y ⬝ z
      = s ⬝ (k ⬝ (s : D)) ⬝ k ⬝ x ⬝ y ⬝ z := rfl
    _ = (k ⬝ s) ⬝ x ⬝ (k ⬝ x) ⬝ y ⬝ z     :=
        congrArg (· ⬝ y ⬝ z) (s_eq (k ⬝ s) k x)
    _ = s ⬝ (k ⬝ x) ⬝ y ⬝ z               :=
        congrArg (· ⬝ (k ⬝ x) ⬝ y ⬝ z) (k_eq s x)
    _ = (k ⬝ x) ⬝ z ⬝ (y ⬝ z)             := s_eq (k ⬝ x) y z
    _ = x ⬝ (y ⬝ z)                       :=
        congrArg (· ⬝ (y ⬝ z)) (k_eq x z)


/-! ## Theorem 5 (single-variable case): combinatory completeness

The paper's Theorem 5 says that for every term `t(x₁, …, xₙ)` there
is `t* ∈ D` with `t* · d₁ · ⋯ · dₙ = t(d₁, …, dₙ)`. The full
statement requires bracket abstraction over arbitrarily many
variables. We restrict to the one-variable case, which is what the
fixed-point construction needs.

A `PureTerm D` is built from one variable, constants drawn from
`D`, and binary application. `eval t x` evaluates such a term at
the value `x`; bracket abstraction `abstr t` produces the element
of `D` that `eval`-s back to `t` when applied to the variable. The
content of Theorem 5 in this form is `abstr_apply`:

    abstr t · x = eval t x. -/

inductive PureTerm (D : Type*) where
  | var            : PureTerm D
  | const (c : D)  : PureTerm D
  | ap (t u : PureTerm D) : PureTerm D

namespace PureTerm

variable {D : Type*} [CombinatoryAlgebra D]

def eval : PureTerm D → D → D
  | var,      x => x
  | const c,  _ => c
  | ap t u,   x => eval t x ⬝ eval u x

def abstr : PureTerm D → D
  | var      => i
  | const c  => k ⬝ c
  | ap t u   => s ⬝ abstr t ⬝ abstr u

theorem abstr_apply (t : PureTerm D) (x : D) :
    abstr t ⬝ x = eval t x := by
  induction t with
  | var        => simp [abstr, eval, i_apply]
  | const c    => simp [abstr, eval, k_eq]
  | ap t u iht ihu =>
    simp only [abstr, eval]
    rw [s_eq, iht, ihu]

/-! ## Fixed-point construction (CL version of Kleene's SRT)

The paper (p. 6): "Consider a function `f(x)` such as `f(x) = x · e`.
We show that there is a term `x*` so that `f(x*) ≡ x*`. For this,
consider the term `f(x · x)`. By combinatory completeness, let `t*`
be such that for all `x`, `t* · x ≡ f(x · x)`. Let `x* = t* · t*`.
Then `x* = t* · t* ≡ f(t* · t*) = f(x*)`."

We follow the same self-application trick. `substSelf t` replaces
the variable inside `t` by the self-application `var · var`, so
`eval (substSelf t) y = eval t (y · y)`, this is the CL counterpart
of the diagonalization step `[[x]](x)`. The fixed point is then
`fixOf g = abstr (substSelf g) · abstr (substSelf g)`, and
`fixOf_isFixed` shows `abstr g · fixOf g = fixOf g`. This is the
combinatory-logic analogue of the second proof of Theorem 1
(Kleene's Second Recursion Theorem). -/

def substSelf : PureTerm D → PureTerm D
  | var      => ap var var
  | const c  => const c
  | ap t u   => ap (substSelf t) (substSelf u)

theorem eval_substSelf (t : PureTerm D) (y : D) :
    eval (substSelf t) y = eval t (y ⬝ y) := by
  induction t with
  | var          => simp [substSelf, eval]
  | const c      => simp [substSelf, eval]
  | ap t u iht ihu =>
      simp only [substSelf, eval, iht, ihu]

def fixOf (g : PureTerm D) : D :=
  abstr (substSelf g) ⬝ abstr (substSelf g)

theorem fixOf_isFixed (g : PureTerm D) :
    abstr g ⬝ fixOf g = fixOf g := by
  -- Let h = substSelf g.  Then abstr h · abstr h = eval h (abstr h)
  -- = eval g (abstr h · abstr h) = eval g (fixOf g).
  -- Also abstr g · fixOf g = eval g (fixOf g).  So they're equal.
  have h1 : fixOf g = eval g (fixOf g) := by
    change abstr (substSelf g) ⬝ abstr (substSelf g) =
           eval g (abstr (substSelf g) ⬝ abstr (substSelf g))
    calc abstr (substSelf g) ⬝ abstr (substSelf g)
        = eval (substSelf g) (abstr (substSelf g)) := abstr_apply _ _
      _ = eval g ((abstr (substSelf g)) ⬝ (abstr (substSelf g))) :=
          eval_substSelf g _
  have h2 : abstr g ⬝ fixOf g = eval g (fixOf g) := abstr_apply g (fixOf g)
  rw [h2, ← h1]

end PureTerm

end CombinatoryAlgebra


end Moss.CombinatoryLogic
