import HigherLambdaModel.Lambda.ExtensionalKanHigher

open HigherLambdaModel.Lambda.ExtensionalKan
open HigherLambdaModel.Lambda
open HigherTerms

noncomputable section

example (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
      let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)) :
    let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
    let δ := reductionSeq_in_Theory1 K r
    let Aβ := Theory2.associator K α β δ
    let right := Theory2.whiskerRight K
      (Theory2.whiskerLeft K α
        (reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q)) δ
    let T := Theory2.trans K
      (Theory2.associator K α
        (reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)) δ)
      (Theory2.whiskerLeft K α
        (reductionSeq_comp_in_Theory2 K (ReductionSeq.concat (ReductionSeq.refl M) q) r))
    Theory3 K
      (Theory2.trans K Aβ
        (Theory2.trans K
          (Theory2.whiskerLeft K α
            (reductionSeq_associator_in_Theory2 K (ReductionSeq.refl M) q r))
          (Theory2.whiskerLeft K α
            (reductionSeq_associator_target_in_Theory2 K (ReductionSeq.refl M) q r))))
      (Theory2.trans K right T) := by
  let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
  let Aβ := Theory2.associator K α β (reductionSeq_in_Theory1 K r)
  let head := Theory2.whiskerRight K
    (Theory2.whiskerLeft K α
      (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)))
    (reductionSeq_in_Theory1 K r)
  let right := Theory2.whiskerRight K
    (Theory2.whiskerLeft K α
      (reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q))
    (reductionSeq_in_Theory1 K r)
  let T := Theory2.trans K
    (Theory2.associator K α
      (reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q))
      (reductionSeq_in_Theory1 K r))
    (Theory2.whiskerLeft K α
      (reductionSeq_comp_in_Theory2 K (ReductionSeq.concat (ReductionSeq.refl M) q) r))
  have hTarget :
      Theory3 K
        (Theory2.trans K Aβ
          (Theory2.trans K
            (Theory2.whiskerLeft K α
              (reductionSeq_associator_in_Theory2 K (ReductionSeq.refl M) q r))
            (Theory2.whiskerLeft K α
              (reductionSeq_associator_target_in_Theory2 K (ReductionSeq.refl M) q r))))
        (Theory2.trans K head T) := by
    have hShell :
        Theory3 K
          (Theory2.whiskerLeft K α
            (Theory2.trans K
              (reductionSeq_associator_in_Theory2 K (ReductionSeq.refl M) q r)
              (reductionSeq_associator_target_in_Theory2 K (ReductionSeq.refl M) q r)))
          (Theory2.trans K (Theory2.symm K Aβ)
            (Theory2.trans K head T)) := by
      simpa [Aβ, head, T, reductionSeq_associator_in_Theory2,
        reductionSeq_associator_target_in_Theory2] using
        (reductionSeq_comp_associator_refl_targetHeadShell_in_Theory3_of_nestedWhiskerComparison
          K α q r hNested)
    have hAssoc :
        Theory3 K
          (Theory2.trans K Aβ
            (Theory2.trans K
              (Theory2.symm K Aβ)
              (Theory2.trans K head T)))
          (Theory2.trans K head T) := by
      exact Theory3.trans K
        (Theory3.symm K
          (Theory3.transAssoc K Aβ (Theory2.symm K Aβ)
            (Theory2.trans K head T)))
        (Theory3.trans K
          (Theory3.transCongrLeft K
            (Theory3.transRightCancel K Aβ)
            (Theory2.trans K head T))
          (Theory3.transReflLeft K (Theory2.trans K head T)))
    exact Theory3.trans K
      (Theory3.transCongrLeft K
        (Theory3.symm K (Theory3.whiskerLeftTrans K α
          (reductionSeq_associator_in_Theory2 K (ReductionSeq.refl M) q r)
          (reductionSeq_associator_target_in_Theory2 K (ReductionSeq.refl M) q r)))
        (Theory2.trans K (Theory2.symm K Aβ) (Theory2.trans K head T)))
      (Theory3.trans K
        (Theory3.transCongrLeft K Aβ hShell)
        hAssoc)
  exact Theory3.trans K hTarget
    (Theory3.transCongrLeft K
      (Theory3.symm K
        (reductionSeq_comp_associator_refl_rightHeadComparison_in_Theory3 K α q r))
      T)

example (K : ExtensionalKanComplex) {L M N P : Term}
    (s : BetaEtaStep L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    let α := betaEtaStep_in_Theory1 K L M s
    let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
    let δ := reductionSeq_in_Theory1 K r
    let β0 := reductionSeq_in_Theory1 K (ReductionSeq.refl M)
    let γ := reductionSeq_in_Theory1 K q
    fun ρ =>
      K.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidRightFrontPath2
        (α ρ) (η ρ) (δ ρ) =
      K.toReflexiveKanComplex.toKanComplex.pentagonInnerRightFrontPath2
        (α ρ) (β0 ρ) (γ ρ) (δ ρ) := by
  intro ρ
  simp [KanComplex.whiskerLeftWhiskerRightMidRightFrontPath2,
    KanComplex.pentagonInnerRightFrontPath2]

example (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
      let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)) :
    Theory3 K
      (Theory2.trans K
        (Theory2.whiskerLeft K α
          (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.refl M) q r))
        (Theory2.whiskerLeft K α
          (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r))))
      (let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
       let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
       let δ := reductionSeq_in_Theory1 K r
       let right := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
       let c₀ := reductionSeq_comp_in_Theory2 K
         (ReductionSeq.concat (ReductionSeq.refl M) q) r
       let T := Theory2.trans K
         (Theory2.associator K α γ δ)
         (Theory2.whiskerLeft K α c₀)
       Theory2.trans K (Theory2.symm K T)
         (Theory2.trans K (Theory2.symm K right)
           (Theory2.trans K right T))) := by
  simpa [reductionSeq_associator_shell_in_Theory2, reductionSeq_associator_target_in_Theory2,
    reductionSeq_associator_source_in_Theory2, reductionSeq_leftUnitor_shell_in_Theory2] using
    (reductionSeq_comp_associator_refl_splitLoop_in_Theory3_of_nestedWhiskerComparison
      K α q r hNested)
