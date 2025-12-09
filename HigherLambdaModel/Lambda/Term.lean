/-
# Untyped Lambda Terms

This module defines untyped λ-terms using de Bruijn indices.
De Bruijn representation provides:
- Built-in α-equivalence (terms equal up to variable renaming are identical)
- Clean substitution without capture-avoiding concerns

## Key Definitions

- `Term` : The type of untyped λ-terms
- `shift` : Shifts free variable indices
- `subst` : Capture-avoiding substitution
- `freeVars` : Set of free variable indices

## Mathematical Background

In the paper "The Theory of an Arbitrary Higher λ-Model" (arXiv:2111.07092),
λ-terms form the 0-cells of a higher structure. The 1-cells will be
β- and η-reductions, and higher cells will be the "higher βη-conversions"
that arise in homotopic λ-models.

## References

- de Queiroz & Martínez-Rivillas, "The Theory of an Arbitrary Higher λ-Model"
- de Bruijn, "Lambda calculus notation with nameless dummies" (1972)
-/

namespace HigherLambdaModel.Lambda

universe u

/-! ## Term Definition -/

/-- Untyped λ-terms using de Bruijn indices.
- `var n` represents the variable bound by the n-th enclosing λ (0-indexed)
- `app M N` represents application M N
- `lam M` represents λ-abstraction; the variable is implicit (index 0 in M)
-/
inductive Term : Type where
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving Repr, DecidableEq, Inhabited

namespace Term

/-! ## Notation -/

/-- Notation: M @ N for application -/
scoped infixl:70 " @ " => Term.app

/-- Notation: ƛ M for lambda abstraction -/
scoped prefix:65 "ƛ " => Term.lam

/-! ## Shifting (de Bruijn index manipulation) -/

/-- Shift free variables in a term.
    `shift d c M` adds d to all free variables with index ≥ c.
    This is needed when moving terms under binders. -/
def shift (d : Int) (c : Nat) : Term → Term
  | var n => if n < c then var n else var (Int.toNat (n + d))
  | app M N => app (shift d c M) (shift d c N)
  | lam M => lam (shift d (c + 1) M)

/-- Increment all free variables by 1 (for going under a binder) -/
abbrev shift1 : Term → Term := shift 1 0

/-! ## Substitution -/

/-- Substitute term N for variable index j in term M.
    `subst j N M` replaces var j with N in M, adjusting indices appropriately. -/
def subst (j : Nat) (N : Term) : Term → Term
  | var n =>
      if n = j then N
      else if n > j then var (n - 1)
      else var n
  | app M₁ M₂ => app (subst j N M₁) (subst j N M₂)
  | lam M => lam (subst (j + 1) (shift1 N) M)

/-- Substitute for variable 0 (the most common case) -/
abbrev subst0 (N : Term) (M : Term) : Term := subst 0 N M

/-- Notation: M[N] for substituting N for variable 0 in M -/
scoped notation:max M "[" N "]" => subst0 N M

/-! ## Free Variables -/

/-- Check if a variable index appears free in a term -/
def hasFreeVar (n : Nat) : Term → Bool
  | var m => m = n
  | app M N => hasFreeVar n M || hasFreeVar n N
  | lam M => hasFreeVar (n + 1) M

/-- Check if all free variables are below a threshold (term is closed at depth d) -/
def closedAtDepth (d : Nat) : Term → Bool
  | var n => n < d
  | app M N => closedAtDepth d M && closedAtDepth d N
  | lam M => closedAtDepth (d + 1) M

/-- A term is closed if it has no free variables -/
def isClosed (t : Term) : Bool := closedAtDepth 0 t

/-! ## Size and Structural Properties -/

/-- Size of a term (number of constructors) -/
def size : Term → Nat
  | var _ => 1
  | app M N => 1 + size M + size N
  | lam M => 1 + size M

/-- Depth of a term (maximum nesting) -/
def depth : Term → Nat
  | var _ => 0
  | app M N => 1 + max (depth M) (depth N)
  | lam M => 1 + depth M

/-! ## Helper for iteration -/

/-- Iterate a function n times -/
def iterate (n : Nat) (f : Term → Term) (x : Term) : Term :=
  match n with
  | 0 => x
  | n + 1 => f (iterate n f x)

/-! ## Examples -/

/-- The identity function: λx.x -/
def I : Term := lam (var 0)

/-- The K combinator: λx.λy.x -/
def K : Term := lam (lam (var 1))

/-- The S combinator: λx.λy.λz.xz(yz) -/
def S : Term := lam (lam (lam (app (app (var 2) (var 0)) (app (var 1) (var 0)))))

/-- The ω combinator: λx.xx -/
def omega : Term := lam (app (var 0) (var 0))

/-- The Ω diverging term: ωω -/
def Omega : Term := app omega omega

/-- Church numeral for 0: λf.λx.x -/
def zero : Term := lam (lam (var 0))

/-- Church numeral for 1: λf.λx.fx -/
def one : Term := lam (lam (app (var 1) (var 0)))

/-- Church numeral for n -/
def church (n : Nat) : Term :=
  lam (lam (iterate n (fun body => app (var 1) body) (var 0)))

/-! ## More Combinators -/

/-- The Y combinator (fixed-point combinator): λf.(λx.f(xx))(λx.f(xx))
    For any F, we have Y F =β F (Y F), making Y F a fixed point of F. -/
def Y : Term :=
  lam (app (lam (app (var 1) (app (var 0) (var 0))))
           (lam (app (var 1) (app (var 0) (var 0)))))

/-- Turing's fixed-point combinator Θ: (λx.λy.y(xxy))(λx.λy.y(xxy))
    An alternative to Y that works in call-by-value. -/
def Theta : Term :=
  let A := lam (lam (app (var 0) (app (app (var 1) (var 1)) (var 0))))
  app A A

/-- The B combinator (composition): λf.λg.λx.f(gx) -/
def B : Term := lam (lam (lam (app (var 2) (app (var 1) (var 0)))))

/-- The C combinator (flip): λf.λx.λy.fyx -/
def C : Term := lam (lam (lam (app (app (var 2) (var 0)) (var 1))))

/-- The W combinator (duplicate): λf.λx.fxx -/
def W : Term := lam (lam (app (app (var 1) (var 0)) (var 0)))

/-! ## Church Booleans -/

/-- Church encoding of true: λx.λy.x (same as K) -/
def tru : Term := K

/-- Church encoding of false: λx.λy.y -/
def fls : Term := lam (lam (var 0))

/-- Church if-then-else: λb.λt.λf.btf
    Usage: ite b t f reduces to t if b is tru, f if b is fls -/
def ite : Term := lam (lam (lam (app (app (var 2) (var 1)) (var 0))))

/-- Church and: λb.λc.bc(λx.λy.y) = λb.λc.bc fls -/
def cand : Term := lam (lam (app (app (var 1) (var 0)) fls))

/-- Church or: λb.λc.b(λx.λy.x)c = λb.λc.b tru c -/
def cor : Term := lam (lam (app (app (var 1) tru) (var 0)))

/-- Church not: λb.b(λx.λy.y)(λx.λy.x) = λb.b fls tru -/
def cnot : Term := lam (app (app (var 0) fls) tru)

/-! ## Church Pairs -/

/-- Church pair constructor: λx.λy.λf.fxy -/
def pair : Term := lam (lam (lam (app (app (var 0) (var 2)) (var 1))))

/-- Church first projection: λp.p(λx.λy.x) = λp.p tru -/
def fst : Term := lam (app (var 0) tru)

/-- Church second projection: λp.p(λx.λy.y) = λp.p fls -/
def snd : Term := lam (app (var 0) fls)

/-! ## Church Numeral Operations -/

/-- Successor function: λn.λf.λx.f(nfx) -/
def succ : Term := lam (lam (lam (app (var 1) (app (app (var 2) (var 1)) (var 0)))))

/-- Addition: λm.λn.λf.λx.mf(nfx) -/
def add : Term := lam (lam (lam (lam (app (app (var 3) (var 1)) (app (app (var 2) (var 1)) (var 0))))))

/-- Multiplication: λm.λn.λf.m(nf) -/
def mul : Term := lam (lam (lam (app (var 2) (app (var 1) (var 0)))))

/-- Exponentiation: λm.λn.nm -/
def exp : Term := lam (lam (app (var 0) (var 1)))

/-- Test for zero: λn.n(λx.fls)tru -/
def iszero : Term := lam (app (app (var 0) (lam fls)) tru)

/-! ## Basic Lemmas -/

@[simp]
theorem shift_zero (c : Nat) (M : Term) : shift 0 c M = M := by
  induction M generalizing c with
  | var n =>
    simp only [shift]
    split <;> simp
  | app M N ihM ihN =>
    simp only [shift]
    rw [ihM, ihN]
  | lam M ih =>
    simp only [shift]
    rw [ih]

@[simp]
theorem subst_var_same (j : Nat) (N : Term) : subst j N (var j) = N := by
  simp [subst]

theorem subst_var_lt (j n : Nat) (N : Term) (h : n < j) :
    subst j N (var n) = var n := by
  simp only [subst]
  have hne : ¬(n = j) := Nat.ne_of_lt h
  have hng : ¬(n > j) := Nat.not_lt.mpr (Nat.le_of_lt h)
  simp [hne, hng]

theorem subst_var_gt (j n : Nat) (N : Term) (h : n > j) :
    subst j N (var n) = var (n - 1) := by
  simp only [subst]
  have hne : ¬(n = j) := Nat.ne_of_gt h
  simp [hne, h]

/-! ## η-contractum check -/

/-- Check if a term has the form λx.Mx where x is not free in M.
    This is the pattern that η-reduces to M. -/
def isEtaRedex : Term → Bool
  | lam (app M (var 0)) => !hasFreeVar 0 M
  | _ => false

/-- Extract the η-contractum if the term is an η-redex -/
def etaContractum : Term → Option Term
  | lam (app M (var 0)) =>
      if !hasFreeVar 0 M then some (shift (-1) 0 M) else none
  | _ => none

end Term

end HigherLambdaModel.Lambda
