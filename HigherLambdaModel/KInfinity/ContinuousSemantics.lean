import HigherLambdaModel.KInfinity.Properties

namespace HigherLambdaModel.KInfinity

open HigherLambdaModel.Domain
open HigherLambdaModel.Lambda
open HigherLambdaModel.Lambda.HomotopyOrder
open Term

/-- A two-sided continuous reflexivity witness: besides the original retract
`reify ∘ reflect = id`, the reflection of a reified continuous map is also
judgmentally exact. This is the continuous-function-space analogue of combining
the β/η sides needed for a term model. -/
structure TwoSidedReflexiveCHPO (K : CompleteHomotopyPartialOrder) where
  toReflexiveCHPO : ReflexiveCHPO K
  sectionLaw :
    ContinuousMap.comp toReflexiveCHPO.reflect toReflexiveCHPO.reify =
      ContinuousMap.id (Exponential.chpo K K)

instance {K : CompleteHomotopyPartialOrder} :
    CoeOut (TwoSidedReflexiveCHPO K) (ReflexiveCHPO K) where
  coe := TwoSidedReflexiveCHPO.toReflexiveCHPO

@[simp] theorem ReflexiveCHPO.retract_apply
    {K : CompleteHomotopyPartialOrder}
    (R : ReflexiveCHPO K) (x : K.Obj) :
    R.reify.toFun (R.reflect.toFun x) = x := by
  have h :=
    congrArg
      (fun g : ContinuousMap K K => g.toFun x)
      R.retract
  simpa [ContinuousMap.comp, ContinuousMap.id] using h

@[simp] theorem TwoSidedReflexiveCHPO.section_apply
    {K : CompleteHomotopyPartialOrder}
    (R : TwoSidedReflexiveCHPO K)
    (f : (Exponential.chpo K K).Obj) :
    R.toReflexiveCHPO.reflect.toFun (R.toReflexiveCHPO.reify.toFun f) = f := by
  have h :=
    congrArg
      (fun g : ContinuousMap (Exponential.chpo K K) (Exponential.chpo K K) =>
        g.toFun f)
      R.sectionLaw
  simpa [ContinuousMap.comp, ContinuousMap.id] using h

@[simp] theorem TwoSidedReflexiveCHPO.section_apply_eval
    {K : CompleteHomotopyPartialOrder}
    (R : TwoSidedReflexiveCHPO K)
    (f : (Exponential.chpo K K).Obj) (x : K.Obj) :
    ((R.toReflexiveCHPO.reflect.toFun (R.toReflexiveCHPO.reify.toFun f)).toFun x) =
      f.toFun x := by
  simpa using congrArg (fun g : (Exponential.chpo K K).Obj => g.toFun x)
    (R.section_apply f)

/-- Finite de Bruijn contexts interpreted as iterated products, with the newest
variable stored in the rightmost slot. -/
def SemanticContext (K : CompleteHomotopyPartialOrder) : Nat → CompleteHomotopyPartialOrder
  | 0 => terminalCHPO
  | n + 1 => Product.chpo (SemanticContext K n) K

/-- Extend a semantic context with a new head variable. -/
def SemanticContext.extend
    {K : CompleteHomotopyPartialOrder} {n : Nat}
    (ρ : (SemanticContext K n).Obj) (x : K.Obj) :
    (SemanticContext K (n + 1)).Obj :=
  (ρ, x)

/-- The unique empty semantic context. -/
def SemanticContext.empty (K : CompleteHomotopyPartialOrder) :
    (SemanticContext K 0).Obj :=
  PUnit.unit

/-- Remove the variable at de Bruijn index `i` from an iterated-product
semantic context, keeping the newer variables in place. This is the semantic
counterpart of weakening / shifting. -/
def SemanticContext.removeAt
    {K : CompleteHomotopyPartialOrder} :
    {n : Nat} → Fin (n + 1) → (SemanticContext K (n + 1)).Obj →
      (SemanticContext K n).Obj
  | _, ⟨0, _⟩, (ρ, _) => ρ
  | _ + 1, ⟨i + 1, hi⟩, (ρ, y) =>
      (SemanticContext.removeAt ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ρ, y)

@[simp] theorem SemanticContext.removeAt_zero
    {K : CompleteHomotopyPartialOrder} {n : Nat}
    (ρ : (SemanticContext K n).Obj) (x : K.Obj) :
    SemanticContext.removeAt (K := K) (n := n) ⟨0, Nat.succ_pos n⟩ (ρ, x) = ρ := by
  cases n <;> rfl

@[simp] theorem SemanticContext.removeAt_succ
    {K : CompleteHomotopyPartialOrder} {n i : Nat}
    (hi : i < n + 1)
    (ρ : (SemanticContext K (n + 1)).Obj) (x : K.Obj) :
    SemanticContext.removeAt (K := K) (n := n + 1) ⟨i + 1, Nat.succ_lt_succ hi⟩ (ρ, x) =
      (SemanticContext.removeAt (K := K) (n := n) ⟨i, hi⟩ ρ, x) := by
  rfl

/-- Insert a semantic value at de Bruijn index `i`, shifting older entries one
step outward in the iterated-product context. This is the semantic context
operation that will underlie the continuous substitution lemma. -/
def SemanticContext.insertAt
    {K : CompleteHomotopyPartialOrder} :
    {n : Nat} → Fin (n + 1) → (SemanticContext K n).Obj → K.Obj →
      (SemanticContext K (n + 1)).Obj
  | _, ⟨0, _⟩, ρ, x => (ρ, x)
  | _ + 1, ⟨i + 1, hi⟩, (ρ, y), x =>
      (SemanticContext.insertAt ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ρ x, y)

@[simp] theorem SemanticContext.insertAt_zero
    {K : CompleteHomotopyPartialOrder} {n : Nat}
    (ρ : (SemanticContext K n).Obj) (x : K.Obj) :
    SemanticContext.insertAt (K := K) (n := n) ⟨0, Nat.succ_pos n⟩ ρ x = (ρ, x) := by
  cases n <;> rfl

@[simp] theorem SemanticContext.insertAt_succ
    {K : CompleteHomotopyPartialOrder} {n i : Nat}
    (hi : i < n + 1)
    (ρ : (SemanticContext K (n + 1)).Obj) (x : K.Obj) :
    SemanticContext.insertAt (K := K) (n := n + 1) ⟨i + 1, Nat.succ_lt_succ hi⟩ ρ x =
      (SemanticContext.insertAt (K := K) (n := n) ⟨i, hi⟩ ρ.1 x, ρ.2) := by
  cases ρ
  rfl

/-- Lookup of a de Bruijn variable in the semantic context, realized as a
continuous projection map. -/
noncomputable def lookupContinuous
    (K : CompleteHomotopyPartialOrder) :
    {n : Nat} → Fin n → ContinuousMap (SemanticContext K n) K
  | 0, i => nomatch i
  | n + 1, ⟨0, _⟩ => sndContinuous (SemanticContext K n) K
  | n + 1, ⟨i + 1, hi⟩ =>
      ContinuousMap.comp
        (lookupContinuous K ⟨i, Nat.lt_of_succ_lt_succ hi⟩)
        (fstContinuous (SemanticContext K n) K)

@[simp] theorem lookupContinuous_head_apply
    {K : CompleteHomotopyPartialOrder} {n : Nat}
    (ρ : (SemanticContext K n).Obj) (x : K.Obj) :
    lookupContinuous K (n := n + 1) ⟨0, Nat.succ_pos n⟩ (ρ, x) = x := by
  rfl

@[simp] theorem lookupContinuous_tail_apply
    {K : CompleteHomotopyPartialOrder} {n i : Nat}
    (hi : i < n) (ρ : (SemanticContext K n).Obj) (x : K.Obj) :
    lookupContinuous K (n := n + 1) ⟨i + 1, Nat.succ_lt_succ hi⟩ (ρ, x) =
      lookupContinuous K (n := n) ⟨i, hi⟩ ρ := by
  rfl

@[simp] theorem lookupContinuous_insertAt_same
    {K : CompleteHomotopyPartialOrder} :
    {n : Nat} → (i : Fin (n + 1)) → (ρ : (SemanticContext K n).Obj) → (x : K.Obj) →
      lookupContinuous K (n := n + 1) i (SemanticContext.insertAt (K := K) i ρ x) = x
  | n, ⟨0, _⟩, ρ, x => by
      cases n <;> rfl
  | _ + 1, ⟨i + 1, hi⟩, (ρ, y), x => by
      simpa [SemanticContext.insertAt] using
        lookupContinuous_insertAt_same (K := K) (n := _) ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ρ x

private def insertAtBelowIndex
    {n : Nat} (i j : Fin (n + 1)) (hij : i.1 < j.1) : Fin n :=
  ⟨i.1, Nat.lt_of_lt_of_le hij (Nat.le_of_lt_succ j.2)⟩

private def insertAtAboveIndex
    {n : Nat} (i j : Fin (n + 1)) (hji : j.1 < i.1) : Fin n :=
  ⟨i.1 - 1, by omega⟩

private def removeAtBelowIndex
    {n : Nat} (i : Fin n) : Fin (n + 1) :=
  ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩

private def removeAtAboveIndex
    {n : Nat} (i : Fin n) : Fin (n + 1) :=
  ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

@[simp] theorem lookupContinuous_removeAt_below
    {K : CompleteHomotopyPartialOrder} :
    ∀ {n : Nat}
      (i : Fin n) (j : Fin (n + 1)) (hij : i.1 < j.1)
      (σ : (SemanticContext K (n + 1)).Obj),
      lookupContinuous K (n := n) i (SemanticContext.removeAt (K := K) j σ) =
        lookupContinuous K (n := n + 1) (removeAtBelowIndex i) σ
  | _, _, ⟨0, _⟩, hij, _ => by
      exact False.elim (Nat.not_lt_zero _ hij)
  | _ + 1, ⟨0, _⟩, ⟨j + 1, hj⟩, hij, (ρ, y) => by
      rfl
  | _ + 1, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hij, (ρ, y) => by
      simpa [SemanticContext.removeAt, removeAtBelowIndex] using
        lookupContinuous_removeAt_below (K := K)
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩
          ⟨j, Nat.lt_of_succ_lt_succ hj⟩
          (Nat.lt_of_succ_lt_succ hij) ρ

@[simp] theorem lookupContinuous_removeAt_above
    {K : CompleteHomotopyPartialOrder} :
    ∀ {n : Nat}
      (i : Fin n) (j : Fin (n + 1)) (hji : j.1 ≤ i.1)
      (σ : (SemanticContext K (n + 1)).Obj),
      lookupContinuous K (n := n) i (SemanticContext.removeAt (K := K) j σ) =
        lookupContinuous K (n := n + 1) (removeAtAboveIndex i) σ
  | n, i, ⟨0, _⟩, hji, (ρ, y) => by
      rw [SemanticContext.removeAt_zero]
      simpa [removeAtAboveIndex] using
        (lookupContinuous_tail_apply (K := K) (n := n)
          (hi := i.2) (ρ := ρ) (x := y)).symm
  | _, ⟨0, _⟩, ⟨j + 1, hj⟩, hji, _ => by
      exact False.elim (Nat.not_succ_le_zero _ hji)
  | _ + 1, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hji, (ρ, y) => by
      simpa [SemanticContext.removeAt, removeAtAboveIndex] using
        lookupContinuous_removeAt_above (K := K)
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩
          ⟨j, Nat.lt_of_succ_lt_succ hj⟩
          (Nat.le_of_succ_le_succ hji) ρ

@[simp] theorem lookupContinuous_insertAt_below
    {K : CompleteHomotopyPartialOrder} :
    ∀ {n : Nat}
      (i j : Fin (n + 1)) (hij : i.1 < j.1)
      (ρ : (SemanticContext K n).Obj) (x : K.Obj),
      lookupContinuous K (n := n + 1) i (SemanticContext.insertAt (K := K) j ρ x) =
        lookupContinuous K (n := n) (insertAtBelowIndex i j hij) ρ
  | _, _, ⟨0, _⟩, hij, _, _ => by
      exact False.elim (Nat.not_lt_zero _ hij)
  | n + 1, ⟨0, _⟩, ⟨j + 1, hj⟩, hij, (ρ, y), x => by
      rfl
  | n + 1, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hij, (ρ, y), x => by
      simpa [SemanticContext.insertAt, insertAtBelowIndex] using
        lookupContinuous_insertAt_below (K := K) (n := n)
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩
          ⟨j, Nat.lt_of_succ_lt_succ hj⟩
          (Nat.lt_of_succ_lt_succ hij) ρ x

@[simp] theorem lookupContinuous_insertAt_above
    {K : CompleteHomotopyPartialOrder} :
    ∀ {n : Nat}
      (i j : Fin (n + 1)) (hji : j.1 < i.1)
      (ρ : (SemanticContext K n).Obj) (x : K.Obj),
      lookupContinuous K (n := n + 1) i (SemanticContext.insertAt (K := K) j ρ x) =
        lookupContinuous K (n := n) (insertAtAboveIndex i j hji) ρ
  | _, ⟨0, _⟩, _, hij, _, _ => by
      exact False.elim (Nat.not_lt_zero _ hij)
  | n + 1, ⟨i + 1, hi⟩, ⟨0, _⟩, hij, (ρ, y), x => by
      have hi' : i < n + 1 := Nat.lt_of_succ_lt_succ hi
      simpa [insertAtAboveIndex] using
        (lookupContinuous_tail_apply (K := K) (n := n + 1)
          (hi := hi') (ρ := (ρ, y)) (x := x))
  | n + 1, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hij, (ρ, y), x => by
      cases i with
      | zero =>
          exact False.elim
            (Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.zero_le j)) hij)
      | succ i =>
          simpa [SemanticContext.insertAt, insertAtAboveIndex] using
            lookupContinuous_insertAt_above (K := K) (n := n)
              ⟨i + 1, Nat.lt_of_succ_lt_succ hi⟩
              ⟨j, Nat.lt_of_succ_lt_succ hj⟩
              (Nat.lt_of_succ_lt_succ hij) ρ x

/-- Continuous interpretation of well-scoped λ-terms in a reflexive c.h.p.o.
This is the first bridge from the Section 4 continuous-function-space model to
the de Bruijn syntax: the result is a continuous map out of the finite semantic
context, not a raw function. -/
noncomputable def interpretContinuous
    {K : CompleteHomotopyPartialOrder}
    (R : ReflexiveCHPO K) :
    (n : Nat) → (M : Term) → Term.closedAtDepth n M = true →
      ContinuousMap (SemanticContext K n) K
  | n, var i, h =>
      lookupContinuous K ⟨i, by
        have hi : i < n := by
          simpa [Term.closedAtDepth] using h
        exact hi⟩
  | n, app M N, h =>
      let hMN : Term.closedAtDepth n M = true ∧ Term.closedAtDepth n N = true := by
        simpa [Term.closedAtDepth] using h
      ContinuousMap.comp
        (HigherLambdaModel.Domain.applicationContinuous K K)
        (ContinuousMap.pair
          (ContinuousMap.comp R.reflect (interpretContinuous R n M hMN.1))
          (interpretContinuous R n N hMN.2))
  | n, lam M, h =>
      let hM : Term.closedAtDepth (n + 1) M = true := by
        simpa [Term.closedAtDepth] using h
      ContinuousMap.comp
        R.reify
        (HigherLambdaModel.Domain.curry (interpretContinuous R (n + 1) M hM))
termination_by n M _h => M.size
decreasing_by
  all_goals
    simp [Term.size]
    try omega

private theorem nat_add_one_toNat (n : Nat) : (↑n + (1 : Int)).toNat = n + 1 := by
  have h : (↑n : Int) + 1 = ↑(n + 1) := by omega
  rw [h]
  exact Int.toNat_natCast (n + 1)

/-- Shifting down by one and then restoring the cutoff shift recovers the
original term, provided the cutoff variable was not free to begin with. -/
private theorem shift_cancel_unshift_aux (M : Term) :
    ∀ (c : Nat), Term.hasFreeVar c M = false →
      Term.shift 1 c (Term.shift (-1) c M) = M := by
  induction M with
  | var m =>
      intro c hFree
      simp [Term.hasFreeVar] at hFree
      by_cases hmc : m < c
      · simp [Term.shift, hmc]
      · have hcm : c ≤ m := Nat.le_of_not_lt hmc
        have hne : m ≠ c := by
          intro hEq
          simp [hEq] at hFree
        have hgt : c < m := Nat.lt_of_le_of_ne hcm (Ne.symm hne)
        have hmpos : 1 ≤ m := by omega
        have hSub : (↑m + (-1 : Int)).toNat = m - 1 := by
          have hInt : (↑m : Int) + (-1 : Int) = ↑(m - 1) := by omega
          rw [hInt]
          exact Int.toNat_natCast (m - 1)
        have hNotLt : ¬ m - 1 < c := by omega
        have hPred : m - 1 + 1 = m := by
          simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hmpos
        simpa [Term.shift, hmc, hNotLt, hSub, hPred, nat_add_one_toNat]
  | app M N ihM ihN =>
      intro c hFree
      simp [Term.hasFreeVar] at hFree
      simp [Term.shift, ihM c hFree.1, ihN c hFree.2]
  | lam M ih =>
      intro c hFree
      simp [Term.hasFreeVar] at hFree
      simp [Term.shift, ih (c + 1) hFree]

/-- Shifting by one above a cutoff preserves well-scopedness when the target
depth is enlarged by one. -/
private theorem closedAtDepth_shift_succ (M : Term) :
    ∀ {n c : Nat}, c ≤ n →
      Term.closedAtDepth n M = true →
      Term.closedAtDepth (n + 1) (Term.shift 1 c M) = true := by
  induction M with
  | var m =>
      intro n c hcn hClosed
      have hm : m < n := by
        simpa [Term.closedAtDepth] using hClosed
      by_cases hmc : m < c
      · simpa [Term.closedAtDepth, Term.shift, hmc] using
          (show m < n + 1 from Nat.lt_trans hm (Nat.lt_succ_self n))
      · have hcm : c ≤ m := Nat.le_of_not_lt hmc
        simpa [Term.closedAtDepth, Term.shift, hmc] using
          (show m + 1 < n + 1 from Nat.succ_lt_succ hm)
  | app M N ihM ihN =>
      intro n c hcn hClosed
      have hMN : Term.closedAtDepth n M = true ∧ Term.closedAtDepth n N = true := by
        simpa [Term.closedAtDepth] using hClosed
      simpa [Term.closedAtDepth, Term.shift,
        ihM hcn hMN.1, ihN hcn hMN.2]
  | lam M ih =>
      intro n c hcn hClosed
      have hM : Term.closedAtDepth (n + 1) M = true := by
        simpa [Term.closedAtDepth] using hClosed
      have hcSucc : c + 1 ≤ n + 1 := Nat.succ_le_succ hcn
      simpa [Term.closedAtDepth, Term.shift] using ih hcSucc hM

/-- In particular, `shift1` preserves well-scopedness after extending the
ambient context by one slot. -/
private theorem closedAtDepth_shift1
    (M : Term) {n : Nat}
    (hClosed : Term.closedAtDepth n M = true) :
    Term.closedAtDepth (n + 1) (Term.shift1 M) = true := by
  simpa [Term.shift1] using closedAtDepth_shift_succ M (n := n) (c := 0) (Nat.zero_le n) hClosed

/-- Finite-context semantic shift lemma: shifting free indices above a cutoff is
interpreted by removing the corresponding semantic slot from the iterated
product context. -/
private theorem interpretContinuous_shift_aux
    {K : CompleteHomotopyPartialOrder}
    (R : ReflexiveCHPO K) (M : Term) :
    ∀ {n : Nat} (j : Fin (n + 1))
      (hM : Term.closedAtDepth n M = true)
      (hShift : Term.closedAtDepth (n + 1) (Term.shift 1 j.1 M) = true)
      (σ : (SemanticContext K (n + 1)).Obj),
      (interpretContinuous R (n + 1) (Term.shift 1 j.1 M) hShift).toFun σ =
        (interpretContinuous R n M hM).toFun (SemanticContext.removeAt j σ) := by
  induction M with
  | var m =>
      intro n j hM hShift σ
      have hm : m < n := by
        simpa [Term.closedAtDepth] using hM
      by_cases hij : m < j.1
      · simpa [interpretContinuous, Term.shift, hij, removeAtBelowIndex] using
          (lookupContinuous_removeAt_below (K := K)
            (i := ⟨m, hm⟩) (j := j) hij σ).symm
      · have hji : j.1 ≤ m := Nat.le_of_not_lt hij
        simpa [interpretContinuous, Term.shift, hij,
            nat_add_one_toNat, removeAtAboveIndex] using
          (lookupContinuous_removeAt_above (K := K)
            (i := ⟨m, hm⟩) (j := j) hji σ).symm
  | app M N ihM ihN =>
      intro n j hApp hShift σ
      have hMN : Term.closedAtDepth n M = true ∧ Term.closedAtDepth n N = true := by
        simpa [Term.closedAtDepth] using hApp
      have hShiftMN :
          Term.closedAtDepth (n + 1) (Term.shift 1 j.1 M) = true ∧
            Term.closedAtDepth (n + 1) (Term.shift 1 j.1 N) = true := by
        simpa [Term.closedAtDepth, Term.shift] using hShift
      simp [interpretContinuous, Term.shift, hMN, hShiftMN,
        HigherLambdaModel.Domain.applicationContinuous,
        ContinuousMap.comp, ContinuousMap.pair,
        ihM j hMN.1 hShiftMN.1 σ, ihN j hMN.2 hShiftMN.2 σ]
  | lam P ih =>
      intro n j hLam hShift σ
      have hP : Term.closedAtDepth (n + 1) P = true := by
        simpa [Term.closedAtDepth] using hLam
      have hShiftP : Term.closedAtDepth (n + 2) (Term.shift 1 (j.1 + 1) P) = true := by
        simpa [Term.closedAtDepth, Term.shift] using hShift
      simp [interpretContinuous, Term.shift]
      apply congrArg R.reify.toFun
      apply ContinuousMap.ext
      intro x
      simpa [interpretContinuous, HigherLambdaModel.Domain.curry,
          SemanticContext.removeAt_succ] using
        ih ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ hP hShiftP (σ, x)

/-- Specialization of the semantic shift lemma for `shift1`: extending the
context by a newest variable does not affect the interpretation of a term whose
free variables have all been shifted outward by one slot. -/
private theorem interpretContinuous_shift1
    {K : CompleteHomotopyPartialOrder}
    (R : ReflexiveCHPO K) (M : Term) {n : Nat}
    (hM : Term.closedAtDepth n M = true)
    (hShift : Term.closedAtDepth (n + 1) (Term.shift1 M) = true)
    (ρ : (SemanticContext K n).Obj) (x : K.Obj) :
    (interpretContinuous R (n + 1) (Term.shift1 M) hShift).toFun (ρ, x) =
      (interpretContinuous R n M hM).toFun ρ := by
  have h :=
    interpretContinuous_shift_aux R M ⟨0, Nat.succ_pos n⟩ hM hShift (ρ, x)
  rw [SemanticContext.removeAt_zero] at h
  simpa [Term.shift1] using h

/-- Finite-context semantic substitution lemma: substituting a well-scoped term
for the variable at de Bruijn index `j` is interpreted by inserting the
semantic value of that term at slot `j` in the semantic context. -/
private theorem interpretContinuous_subst_aux
    {K : CompleteHomotopyPartialOrder}
    (R : ReflexiveCHPO K) (M : Term) :
    ∀ {n : Nat} (j : Fin (n + 1)) (N : Term)
      (hM : Term.closedAtDepth (n + 1) M = true)
      (hN : Term.closedAtDepth n N = true)
      (hSub : Term.closedAtDepth n (Term.subst j.1 N M) = true)
      (ρ : (SemanticContext K n).Obj),
      (interpretContinuous R n (Term.subst j.1 N M) hSub).toFun ρ =
        (interpretContinuous R (n + 1) M hM).toFun
          (SemanticContext.insertAt j ρ ((interpretContinuous R n N hN).toFun ρ)) := by
  induction M with
  | var m =>
      intro n j N hM hN hSub ρ
      have hmBig : m < n + 1 := by
        simpa [Term.closedAtDepth] using hM
      by_cases hmEq : m = j.1
      · subst hmEq
        have hSubN : Term.closedAtDepth n N = true := by
          simpa [Term.subst] using hSub
        have hSubEq : hSubN = hN := by
          apply Subsingleton.elim
        simpa [interpretContinuous, Term.subst, hSubEq] using
          lookupContinuous_insertAt_same (K := K) (i := j) (ρ := ρ)
            (x := (interpretContinuous R n N hN).toFun ρ)
      · by_cases hmLt : m < j.1
        · have hmLe : ¬ m > j.1 := by omega
          simpa [interpretContinuous, Term.subst, hmEq, hmLt, hmLe, insertAtBelowIndex]
        · have hjm : j.1 < m := by omega
          simpa [interpretContinuous, Term.subst, hmEq, hmLt, hjm, insertAtAboveIndex] using
            (lookupContinuous_insertAt_above (K := K)
              (i := ⟨m, hmBig⟩) (j := j) hjm ρ
              ((interpretContinuous R n N hN).toFun ρ)).symm
  | app M P ihM ihP =>
      intro n j N hApp hN hSub ρ
      have hMP : Term.closedAtDepth (n + 1) M = true ∧ Term.closedAtDepth (n + 1) P = true := by
        simpa [Term.closedAtDepth] using hApp
      have hSubMP :
          Term.closedAtDepth n (Term.subst j.1 N M) = true ∧
            Term.closedAtDepth n (Term.subst j.1 N P) = true := by
        simpa [Term.closedAtDepth, Term.subst] using hSub
      simp [interpretContinuous, Term.subst,
        HigherLambdaModel.Domain.applicationContinuous,
        ContinuousMap.comp, ContinuousMap.pair,
        ihM j N hMP.1 hN hSubMP.1 ρ,
        ihP j N hMP.2 hN hSubMP.2 ρ]
  | lam P ih =>
      intro n j N hLam hN hSub ρ
      have hP : Term.closedAtDepth (n + 2) P = true := by
        simpa [Term.closedAtDepth] using hLam
      have hShiftN : Term.closedAtDepth (n + 1) (Term.shift1 N) = true :=
        closedAtDepth_shift1 N hN
      have hSubP :
          Term.closedAtDepth (n + 1) (Term.subst (j.1 + 1) (Term.shift1 N) P) = true := by
        simpa [Term.closedAtDepth, Term.subst] using hSub
      simp [interpretContinuous, Term.subst]
      apply congrArg R.reify.toFun
      apply ContinuousMap.ext
      intro x
      have hShiftVal :
          (interpretContinuous R (n + 1) (Term.shift1 N) hShiftN).toFun (ρ, x) =
            (interpretContinuous R n N hN).toFun ρ :=
        interpretContinuous_shift1 R N hN hShiftN ρ x
      simpa [HigherLambdaModel.Domain.curry, SemanticContext.insertAt_succ, hShiftVal] using
        ih ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ (Term.shift1 N) hP hShiftN hSubP (ρ, x)

/-- Finite-context semantic substitution for the continuous interpreter:
interpreting `Term.subst j N M` agrees with interpreting `M` in the semantic
context where the value of `N` has been inserted at slot `j`. -/
theorem interpretContinuous_subst
    {K : CompleteHomotopyPartialOrder}
    (R : ReflexiveCHPO K) (M : Term)
    {n : Nat} (j : Fin (n + 1)) (N : Term)
    (hM : Term.closedAtDepth (n + 1) M = true)
    (hN : Term.closedAtDepth n N = true)
    (hSub : Term.closedAtDepth n (Term.subst j.1 N M) = true)
    (ρ : (SemanticContext K n).Obj) :
    (interpretContinuous R n (Term.subst j.1 N M) hSub).toFun ρ =
      (interpretContinuous R (n + 1) M hM).toFun
        (SemanticContext.insertAt j ρ ((interpretContinuous R n N hN).toFun ρ)) :=
  interpretContinuous_subst_aux R M j N hM hN hSub ρ

/-- Specialization of continuous semantic substitution to the root variable
`0`, so insertion becomes extension by a newest variable. -/
@[simp] theorem interpretContinuous_subst0
    {K : CompleteHomotopyPartialOrder}
    (R : ReflexiveCHPO K) (M N : Term) {n : Nat}
    (hM : Term.closedAtDepth (n + 1) M = true)
    (hN : Term.closedAtDepth n N = true)
    (hSub : Term.closedAtDepth n (M[N]) = true)
    (ρ : (SemanticContext K n).Obj) :
    (interpretContinuous R n (M[N]) hSub).toFun ρ =
      (interpretContinuous R (n + 1) M hM).toFun
        (ρ, (interpretContinuous R n N hN).toFun ρ) := by
  calc
    (interpretContinuous R n (M[N]) hSub).toFun ρ =
        (interpretContinuous R (n + 1) M hM).toFun
          (SemanticContext.insertAt ⟨0, Nat.succ_pos n⟩ ρ
            ((interpretContinuous R n N hN).toFun ρ)) := by
          simpa [Term.subst0] using
            interpretContinuous_subst R M ⟨0, Nat.succ_pos n⟩ N hM hN hSub ρ
    _ =
        (interpretContinuous R (n + 1) M hM).toFun
          (ρ, (interpretContinuous R n N hN).toFun ρ) := by
          rw [SemanticContext.insertAt_zero]

/-- In a two-sided continuous reflexive model, reflecting the interpretation of
a λ-term recovers the body map evaluated at the extended semantic context. This
is the first concrete bridge lemma relating the new continuous interpreter to
the Section 4 `reflect`/`reify` equivalence. -/
@[simp] theorem interpretContinuous_lam_reflect_apply
    {K : CompleteHomotopyPartialOrder}
    (R : TwoSidedReflexiveCHPO K)
    (n : Nat) (M : Term)
    (h : Term.closedAtDepth n (lam M) = true)
    (ρ : (SemanticContext K n).Obj) (x : K.Obj) :
    ((R.toReflexiveCHPO.reflect.toFun
        ((interpretContinuous R.toReflexiveCHPO n (lam M) h).toFun ρ)).toFun x) =
      (interpretContinuous R.toReflexiveCHPO (n + 1) M
        (by simpa [Term.closedAtDepth] using h)).toFun (ρ, x) := by
  let hM : Term.closedAtDepth (n + 1) M = true := by
    simpa [Term.closedAtDepth] using h
  have hM_eq :
      (by simpa [Term.closedAtDepth] using h :
        Term.closedAtDepth (n + 1) M = true) = hM := by
    apply Subsingleton.elim
  rw [hM_eq]
  simp [interpretContinuous, ContinuousMap.comp, HigherLambdaModel.Domain.curry]

/-- Root β-soundness for the continuous interpreter. The two-sided section law
on the continuous exponential identifies application of a reified abstraction
with semantic substitution in the extended context. -/
theorem beta_sound_continuous
    {K : CompleteHomotopyPartialOrder}
    (R : TwoSidedReflexiveCHPO K)
    (n : Nat) (M N : Term)
    (hM : Term.closedAtDepth (n + 1) M = true)
    (hN : Term.closedAtDepth n N = true)
    (hSub : Term.closedAtDepth n (M[N]) = true)
    (ρ : (SemanticContext K n).Obj) :
    (interpretContinuous R.toReflexiveCHPO n ((Term.lam M) @ N)
      (by
        have hLam : Term.closedAtDepth n (Term.lam M) = true := by
          simpa [Term.closedAtDepth] using hM
        simpa [Term.closedAtDepth] using And.intro hLam hN)).toFun ρ =
      (interpretContinuous R.toReflexiveCHPO n (M[N]) hSub).toFun ρ := by
  let hLam : Term.closedAtDepth n (Term.lam M) = true := by
    simpa [Term.closedAtDepth] using hM
  have hLam_eq :
      (by simpa [Term.closedAtDepth] using hM :
        Term.closedAtDepth n (Term.lam M) = true) = hLam := by
    apply Subsingleton.elim
  let hApp : Term.closedAtDepth n ((Term.lam M) @ N) = true := by
    simpa [Term.closedAtDepth] using And.intro hLam hN
  have hApp_eq :
      (by
        have hLam' : Term.closedAtDepth n (Term.lam M) = true := by
          simpa [Term.closedAtDepth] using hM
        simpa [Term.closedAtDepth] using And.intro hLam' hN :
        Term.closedAtDepth n ((Term.lam M) @ N) = true) = hApp := by
    apply Subsingleton.elim
  rw [hApp_eq]
  let arg := (interpretContinuous R.toReflexiveCHPO n N hN).toFun ρ
  calc
    (interpretContinuous R.toReflexiveCHPO n ((Term.lam M) @ N) hApp).toFun ρ
        =
      ((R.toReflexiveCHPO.reflect.toFun
          ((interpretContinuous R.toReflexiveCHPO n (Term.lam M) hLam).toFun ρ)).toFun arg) := by
            simp [arg, interpretContinuous, hLam_eq, ContinuousMap.comp, ContinuousMap.pair,
              HigherLambdaModel.Domain.applicationContinuous,
              HigherLambdaModel.Domain.evalContinuous,
              HigherLambdaModel.Domain.SeparateContinuousWitness.joint]
    _ =
      (interpretContinuous R.toReflexiveCHPO (n + 1) M hM).toFun (ρ, arg) := by
        simpa [arg, hLam_eq] using
          interpretContinuous_lam_reflect_apply R n M hLam ρ arg
    _ =
      (interpretContinuous R.toReflexiveCHPO n (M[N]) hSub).toFun ρ := by
        simpa [arg, Term.subst0] using
          (interpretContinuous_subst0 R.toReflexiveCHPO M N hM hN hSub ρ).symm

/-- η-soundness for the continuous interpreter in the standard shifted de Bruijn
form `λ.((shift1 M) · 0)`. The new bound variable is semantically inert because
`shift1` moves every free variable of `M` outward by one slot. -/
theorem eta_sound_continuous
    {K : CompleteHomotopyPartialOrder}
    (R : TwoSidedReflexiveCHPO K)
    (n : Nat) (M : Term)
    (hM : Term.closedAtDepth n M = true)
    (ρ : (SemanticContext K n).Obj) :
    (interpretContinuous R.toReflexiveCHPO n
      (Term.lam ((Term.shift1 M) @ (Term.var 0)))
      (by
        have hShift : Term.closedAtDepth (n + 1) (Term.shift1 M) = true :=
          closedAtDepth_shift1 M hM
        have hVar : Term.closedAtDepth (n + 1) (Term.var 0) = true := by
          simp [Term.closedAtDepth]
        simpa [Term.closedAtDepth] using And.intro hShift hVar)).toFun ρ =
      (interpretContinuous R.toReflexiveCHPO n M hM).toFun ρ := by
  let hShift : Term.closedAtDepth (n + 1) (Term.shift1 M) = true :=
    closedAtDepth_shift1 M hM
  have hVar : Term.closedAtDepth (n + 1) (Term.var 0) = true := by
    simp [Term.closedAtDepth]
  let hBody : Term.closedAtDepth (n + 1) ((Term.shift1 M) @ (Term.var 0)) = true := by
    simpa [Term.closedAtDepth] using And.intro hShift hVar
  let hEta : Term.closedAtDepth n (Term.lam ((Term.shift1 M) @ (Term.var 0))) = true := by
    simpa [Term.closedAtDepth] using hBody
  have hEta_eq :
      (by
        have hShift' : Term.closedAtDepth (n + 1) (Term.shift1 M) = true :=
          closedAtDepth_shift1 M hM
        have hVar' : Term.closedAtDepth (n + 1) (Term.var 0) = true := by
          simp [Term.closedAtDepth]
        simpa [Term.closedAtDepth] using And.intro hShift' hVar' :
        Term.closedAtDepth n (Term.lam ((Term.shift1 M) @ (Term.var 0))) = true) = hEta := by
    apply Subsingleton.elim
  rw [hEta_eq]
  have hReflect :
      R.toReflexiveCHPO.reflect.toFun
        ((interpretContinuous R.toReflexiveCHPO n
            (Term.lam ((Term.shift1 M) @ (Term.var 0))) hEta).toFun ρ) =
      R.toReflexiveCHPO.reflect.toFun
        ((interpretContinuous R.toReflexiveCHPO n M hM).toFun ρ) := by
    apply ContinuousMap.ext
    intro x
    have hShiftVal :
        (interpretContinuous R.toReflexiveCHPO (n + 1) (Term.shift1 M) hShift).toFun (ρ, x) =
          (interpretContinuous R.toReflexiveCHPO n M hM).toFun ρ :=
      interpretContinuous_shift1 R.toReflexiveCHPO M hM hShift ρ x
    calc
      ((R.toReflexiveCHPO.reflect.toFun
          ((interpretContinuous R.toReflexiveCHPO n
              (Term.lam ((Term.shift1 M) @ (Term.var 0))) hEta).toFun ρ)).toFun x) =
        (interpretContinuous R.toReflexiveCHPO (n + 1)
          ((Term.shift1 M) @ (Term.var 0)) hBody).toFun (ρ, x) := by
            simpa using
              interpretContinuous_lam_reflect_apply
                R n ((Term.shift1 M) @ (Term.var 0)) hEta ρ x
      _ =
        ((R.toReflexiveCHPO.reflect.toFun
            ((interpretContinuous R.toReflexiveCHPO n M hM).toFun ρ)).toFun
          ((lookupContinuous K (n := n + 1) ⟨0, Nat.succ_pos n⟩).toFun (ρ, x))) := by
            simp [interpretContinuous, ContinuousMap.comp, ContinuousMap.pair,
              HigherLambdaModel.Domain.applicationContinuous,
              HigherLambdaModel.Domain.SeparateContinuousWitness.joint,
              hShiftVal]
      _ =
        ((R.toReflexiveCHPO.reflect.toFun
            ((interpretContinuous R.toReflexiveCHPO n M hM).toFun ρ)).toFun x) := by
            rfl
  calc
    (interpretContinuous R.toReflexiveCHPO n
        (Term.lam ((Term.shift1 M) @ (Term.var 0))) hEta).toFun ρ =
      R.toReflexiveCHPO.reify.toFun
        (R.toReflexiveCHPO.reflect.toFun
          ((interpretContinuous R.toReflexiveCHPO n
              (Term.lam ((Term.shift1 M) @ (Term.var 0))) hEta).toFun ρ)) := by
            symm
            exact R.toReflexiveCHPO.retract_apply _
    _ =
      R.toReflexiveCHPO.reify.toFun
        (R.toReflexiveCHPO.reflect.toFun
          ((interpretContinuous R.toReflexiveCHPO n M hM).toFun ρ)) := by
            rw [hReflect]
    _ =
      (interpretContinuous R.toReflexiveCHPO n M hM).toFun ρ := by
            exact R.toReflexiveCHPO.retract_apply _

/-- Arbitrary β-steps preserve the continuous interpretation. The root case uses
`beta_sound_continuous`, while the congruence cases follow from the
compositionality of `interpretContinuous`. -/
theorem betaStep_sound_continuous
    {K : CompleteHomotopyPartialOrder}
    (R : TwoSidedReflexiveCHPO K)
    {n : Nat} {M N : Term} (h : BetaStep M N)
    (hM : Term.closedAtDepth n M = true)
    (hN : Term.closedAtDepth n N = true)
    (ρ : (SemanticContext K n).Obj) :
    (interpretContinuous R.toReflexiveCHPO n M hM).toFun ρ =
      (interpretContinuous R.toReflexiveCHPO n N hN).toFun ρ := by
  induction h generalizing n ρ with
  | beta M N =>
      simp [Term.closedAtDepth] at hM
      exact beta_sound_continuous R n M N hM.1 hM.2 hN ρ
  | appL h ih =>
      simp [Term.closedAtDepth] at hM hN
      simpa [interpretContinuous, ContinuousMap.comp, ContinuousMap.pair,
          HigherLambdaModel.Domain.applicationContinuous,
          HigherLambdaModel.Domain.SeparateContinuousWitness.joint,
          ih hM.1 hN.1 ρ]
  | appR h ih =>
      simp [Term.closedAtDepth] at hM hN
      simpa [interpretContinuous, ContinuousMap.comp, ContinuousMap.pair,
          HigherLambdaModel.Domain.applicationContinuous,
          HigherLambdaModel.Domain.SeparateContinuousWitness.joint,
          ih hM.2 hN.2 ρ]
  | lam h ih =>
      simp [Term.closedAtDepth] at hM hN
      simp [interpretContinuous]
      apply congrArg R.toReflexiveCHPO.reify.toFun
      apply ContinuousMap.ext
      intro x
      simpa [HigherLambdaModel.Domain.curry] using ih hM hN (ρ, x)

/-- Arbitrary η-steps preserve the continuous interpretation. The root case is
reduced to `eta_sound_continuous` by rewriting the η-redex body as the shifted
form of its contracted target; the congruence cases follow from the
compositionality of `interpretContinuous`. -/
theorem etaStep_sound_continuous
    {K : CompleteHomotopyPartialOrder}
    (R : TwoSidedReflexiveCHPO K)
    {n : Nat} {M N : Term} (h : EtaStep M N)
    (hM : Term.closedAtDepth n M = true)
    (hN : Term.closedAtDepth n N = true)
    (ρ : (SemanticContext K n).Obj) :
    (interpretContinuous R.toReflexiveCHPO n M hM).toFun ρ =
      (interpretContinuous R.toReflexiveCHPO n N hN).toFun ρ := by
  induction h generalizing n ρ with
  | eta M hNotFree =>
      have hFree : Term.hasFreeVar 0 M = false := by
        cases hfv : Term.hasFreeVar 0 M <;> simp [hfv] at hNotFree ⊢
      have hShiftCancel :
          Term.shift1 (Term.shift (-1) 0 M) = M :=
        shift_cancel_unshift_aux M 0 hFree
      simpa [hShiftCancel] using
        eta_sound_continuous R n (Term.shift (-1) 0 M) hN ρ
  | appL h ih =>
      simp [Term.closedAtDepth] at hM hN
      simpa [interpretContinuous, ContinuousMap.comp, ContinuousMap.pair,
          HigherLambdaModel.Domain.applicationContinuous,
          HigherLambdaModel.Domain.SeparateContinuousWitness.joint,
          ih hM.1 hN.1 ρ]
  | appR h ih =>
      simp [Term.closedAtDepth] at hM hN
      simpa [interpretContinuous, ContinuousMap.comp, ContinuousMap.pair,
          HigherLambdaModel.Domain.applicationContinuous,
          HigherLambdaModel.Domain.SeparateContinuousWitness.joint,
          ih hM.2 hN.2 ρ]
  | lam h ih =>
      simp [Term.closedAtDepth] at hM hN
      simp [interpretContinuous]
      apply congrArg R.toReflexiveCHPO.reify.toFun
      apply ContinuousMap.ext
      intro x
      simpa [HigherLambdaModel.Domain.curry] using ih hM hN (ρ, x)

/-- Combined βη-steps preserve the continuous interpretation. -/
theorem betaEtaStep_sound_continuous
    {K : CompleteHomotopyPartialOrder}
    (R : TwoSidedReflexiveCHPO K)
    {n : Nat} {M N : Term} (h : BetaEtaStep M N)
    (hM : Term.closedAtDepth n M = true)
    (hN : Term.closedAtDepth n N = true)
    (ρ : (SemanticContext K n).Obj) :
    (interpretContinuous R.toReflexiveCHPO n M hM).toFun ρ =
      (interpretContinuous R.toReflexiveCHPO n N hN).toFun ρ := by
  cases h with
  | beta hb => exact betaStep_sound_continuous R hb hM hN ρ
  | eta he => exact etaStep_sound_continuous R he hM hN ρ

/-- `K∞` now carries the two-sided continuous reflexivity package needed by the
new continuous semantics layer. -/
noncomputable def kInfinityTwoSidedReflexiveCHPO :
    TwoSidedReflexiveCHPO KInfinityCHPO where
  toReflexiveCHPO := kInfinityReflexiveCHPO
  sectionLaw := proposition_4_3_shadow.globalSection

end HigherLambdaModel.KInfinity
