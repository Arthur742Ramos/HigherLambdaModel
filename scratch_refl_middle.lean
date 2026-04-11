import HigherLambdaModel.Lambda.ExtensionalKanHigher

open HigherLambdaModel.Lambda.ExtensionalKan
open HigherLambdaModel.Lambda
open HigherTerms

noncomputable section

example (K : ExtensionalKanComplex) {L M N P : Term}
    (s : BetaEtaStep L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let α := betaEtaStep_in_Theory1 K L M s
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
    let α := betaEtaStep_in_Theory1 K L M s
    let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
    let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
    let δ := reductionSeq_in_Theory1 K r
    let Aβ := Theory2.associator K α β δ
    let A1 := Theory2.associator K α (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
    let right := Theory2.whiskerRight K
      (Theory2.whiskerLeft K α (reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q)) δ
    let c₀ := reductionSeq_comp_in_Theory2 K
      (ReductionSeq.concat (ReductionSeq.refl M) q) r
    let T := Theory2.trans K
      (Theory2.associator K α γ δ)
      (Theory2.whiskerLeft K α c₀)
    Theory3 K
      (Theory2.trans K
        (Theory2.trans K (Theory2.symm K Aβ)
          (Theory2.whiskerRight K (Theory2.symm K A1) δ))
        (Theory2.trans K
          (reductionSeq_associator_in_Theory2 K (ReductionSeq.step s (ReductionSeq.refl M)) q r)
          (reductionSeq_associator_target_in_Theory2 K (ReductionSeq.step s (ReductionSeq.refl M)) q r)))
      (Theory2.trans K (Theory2.symm K Aβ)
        (Theory2.trans K right T)) := by
  simp [reductionSeq_associator_in_Theory2, reductionSeq_associator_target_in_Theory2,
    reductionSeq_comp_in_Theory2, reductionSeq_in_Theory1, ReductionSeq.concat,
    Theory2.whiskerRight, Theory2.whiskerLeft]

example (K : ExtensionalKanComplex) {L M N P : Term}
    (s : BetaEtaStep L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let α := betaEtaStep_in_Theory1 K L M s
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
    let α := betaEtaStep_in_Theory1 K L M s
    Theory3 K
      (Theory2.trans K
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.symm K
              (Theory2.associator K α
                (Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q))
                (reductionSeq_in_Theory1 K r)))
            (Theory2.whiskerRight K
              (Theory2.symm K
                (Theory2.associator K α
                  (Theory1.refl K M)
                  (reductionSeq_in_Theory1 K q)))
              (reductionSeq_in_Theory1 K r)))
          (reductionSeq_associator_in_Theory2 K (ReductionSeq.step s (ReductionSeq.refl M)) q r))
        (reductionSeq_associator_target_in_Theory2 K (ReductionSeq.step s (ReductionSeq.refl M)) q r))
      (Theory2.trans K
        (Theory2.whiskerLeft K α
          (reductionSeq_associator_in_Theory2 K (ReductionSeq.refl M) q r))
        (Theory2.whiskerLeft K α
          (reductionSeq_associator_target_in_Theory2 K (ReductionSeq.refl M) q r))) := by
  let α := betaEtaStep_in_Theory1 K L M s
  simpa [α] using
    (reductionSeq_comp_associator_refl_rightShell_to_theoryWhiskerTail_in_Theory3_of_nestedWhiskerComparison
      K α q r hNested)

example (K : ExtensionalKanComplex) {L M N P : Term}
    (s : BetaEtaStep L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    let α := betaEtaStep_in_Theory1 K L M s
    let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
    let δ := reductionSeq_in_Theory1 K r
    let Aβ := Theory2.associator K α β δ
    let A1 := Theory2.associator K α (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
    let c₀ := reductionSeq_comp_in_Theory2 K
      (ReductionSeq.concat (ReductionSeq.refl M) q) r
    let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
    let target := Theory2.whiskerLeft K α
      (Theory2.trans K
        (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
        (Theory2.trans K
          (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
          (Theory2.trans K e
            (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))
    Theory3 K
      (Theory2.trans K
        (Theory2.whiskerRight K (Theory2.symm K A1) δ)
        (Theory2.trans K
          (reductionSeq_associator_in_Theory2 K (ReductionSeq.step s (ReductionSeq.refl M)) q r)
          (reductionSeq_associator_target_in_Theory2 K (ReductionSeq.step s (ReductionSeq.refl M)) q r)))
      (Theory2.trans K Aβ target) := by
  simp [reductionSeq_associator_in_Theory2, reductionSeq_associator_target_in_Theory2,
    reductionSeq_comp_in_Theory2, reductionSeq_in_Theory1, ReductionSeq.concat,
    Theory2.whiskerLeft, Theory2.whiskerRight]

example (K : KanComplex) {a b d e : K.Obj}
    (p : K.PathSpace a b) (r : K.PathSpace b d) (s : K.PathSpace d e) :
    K.Path3
      (K.pentagonInnerRightFrontPath2 p (K.reflPath b) r s)
      (K.trianglePath2
        (K.compTriangle (K.reflPath b) (K.compPath r s))
        (K.sourceDegenerateTriangle (K.compPath r s))) := by
  simp [KanComplex.pentagonInnerRightFrontPath2]

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
  simpa [reductionSeq_associator_shell_in_Theory2, reductionSeq_associator_source_in_Theory2,
    reductionSeq_associator_target_in_Theory2, reductionSeq_associator_in_Theory2,
    reductionSeq_leftUnitor_shell_in_Theory2, reductionSeq_comp_in_Theory2,
    reductionSeq_in_Theory1, ReductionSeq.concat, Theory2.whiskerLeft, Theory2.whiskerRight] using
    (reductionSeq_comp_associator_refl_splitLoopContract_in_Theory3_of_nestedWhiskerComparison
      K α q r hNested)

example (K : KanComplex) {a b d e : K.Obj}
    (p : K.PathSpace a b) (r : K.PathSpace b d) (s : K.PathSpace d e) :
    K.Path3
      (K.pentagonInnerRightFrontPath2 p (K.reflPath b) r s)
      (K.whiskerLeftWhiskerRightMidRightFrontPath2 p
        (K.leftUnitorPath2 r) s) := by
  simp [KanComplex.pentagonInnerRightFrontPath2]

example (K : KanComplex) {a b d e : K.Obj}
    (p : K.PathSpace a b) (r : K.PathSpace b d) (s : K.PathSpace d e) :
    K.Path3
      (K.pentagonInnerRightFrontPath2 p (K.reflPath b) r s)
      (K.trianglePath2
        (K.compTriangle (K.reflPath b) (K.compPath r s))
        (K.assocTriangle (K.reflPath b) r s)) := by
  simp [KanComplex.pentagonInnerRightFrontPath2]
