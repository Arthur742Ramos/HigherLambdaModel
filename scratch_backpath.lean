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
    Theory3 K
      (fun ρ =>
        K.toReflexiveKanComplex.toKanComplex.trianglePath2
          (K.toReflexiveKanComplex.toKanComplex.pentagonInnerBackTriangle
            (α ρ)
            ((Theory1.refl K M) ρ)
            (reductionSeq_in_Theory1 K q ρ)
            (reductionSeq_in_Theory1 K r ρ))
          (K.toReflexiveKanComplex.toKanComplex.pentagonRightBackTriangle
            (α ρ)
            ((Theory1.refl K M) ρ)
            (reductionSeq_in_Theory1 K q ρ)
            (reductionSeq_in_Theory1 K r ρ)))
      (Theory2.refl K
        (Theory1.comp K
          (Theory1.comp K
            (Theory1.comp K α (Theory1.refl K M))
            (reductionSeq_in_Theory1 K q))
          (reductionSeq_in_Theory1 K r))) := by
  simpa [reductionSeq_associator_shell_in_Theory2,
    reductionSeq_associator_source_in_Theory2, reductionSeq_associator_target_in_Theory2,
    reductionSeq_associator_in_Theory2, reductionSeq_leftUnitor_shell_in_Theory2,
    reductionSeq_comp_in_Theory2, reductionSeq_in_Theory1, ReductionSeq.concat,
    Theory2.whiskerLeft, Theory2.whiskerRight,
    KanComplex.pentagonInnerBackTriangle, KanComplex.pentagonRightBackTriangle] using
    (reductionSeq_comp_associator_refl_splitLoopContract_in_Theory3_of_nestedWhiskerComparison
      K α q r hNested)
