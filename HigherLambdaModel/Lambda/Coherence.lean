/-
# Coherence Laws for the Weak ω-Groupoid Structure on λ-Terms

This module records coherence witnesses for the explicit higher-cell structure on
λ-terms. Unlike the earlier proof-irrelevant presentation, the current version
expresses coherence by actual 3-cells rather than strict equalities of 2-cells.
-/

import HigherLambdaModel.Lambda.HigherTerms

namespace HigherLambdaModel.Lambda.Coherence

open Term
open HigherLambdaModel.Lambda.HigherTerms

/-! ## Whiskering Operations -/

/-- Left whiskering transports a 2-cell along composition on the left. -/
def whiskerLeft {M N P : Term}
    (r : ReductionSeq M N) {p q : ReductionSeq N P}
    (α : Homotopy2 p q) :
    Homotopy2 (ReductionSeq.concat r p) (ReductionSeq.concat r q) :=
  HigherTerms.whiskerLeft r α

/-- Right whiskering transports a 2-cell along composition on the right. -/
def whiskerRight {M N P : Term}
    {p q : ReductionSeq M N} (α : Homotopy2 p q)
    (s : ReductionSeq N P) :
    Homotopy2 (ReductionSeq.concat p s) (ReductionSeq.concat q s) :=
  HigherTerms.whiskerRight α s

/-- Horizontal composition of 2-cells. -/
def hcomp {M N P : Term}
    {p p' : ReductionSeq M N} {q q' : ReductionSeq N P}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    Homotopy2 (ReductionSeq.concat p q) (ReductionSeq.concat p' q') :=
  HigherTerms.hcomp α β

/-! ## Whiskering Properties -/

/-- Left whiskering preserves identity 2-cells up to a 3-cell. -/
def whiskerLeft_refl {M N P : Term}
    (r : ReductionSeq M N) (p : ReductionSeq N P) :
    HigherTerms.Homotopy3 (whiskerLeft r (Homotopy2.refl p))
      (Homotopy2.refl (ReductionSeq.concat r p)) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.whiskerLeftRefl r p)

/-- Right whiskering preserves identity 2-cells up to a 3-cell. -/
def whiskerRight_refl {M N P : Term}
    (p : ReductionSeq M N) (s : ReductionSeq N P) :
    HigherTerms.Homotopy3 (whiskerRight (Homotopy2.refl p) s)
      (Homotopy2.refl (ReductionSeq.concat p s)) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.whiskerRightRefl p s)

/-- Left whiskering preserves vertical composition up to a 3-cell. -/
def whiskerLeft_trans {M N P : Term}
    (r : ReductionSeq M N) {p q s : ReductionSeq N P}
    (α : Homotopy2 p q) (β : Homotopy2 q s) :
    HigherTerms.Homotopy3 (whiskerLeft r (Homotopy2.trans α β))
      (Homotopy2.trans (whiskerLeft r α) (whiskerLeft r β)) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.whiskerLeftTrans r α β)

/-- Right whiskering preserves vertical composition up to a 3-cell. -/
def whiskerRight_trans {M N P : Term}
    {p q s : ReductionSeq M N} (α : Homotopy2 p q) (β : Homotopy2 q s)
    (r : ReductionSeq N P) :
    HigherTerms.Homotopy3 (whiskerRight (Homotopy2.trans α β) r)
      (Homotopy2.trans (whiskerRight α r) (whiskerRight β r)) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.whiskerRightTrans α β r)

/-- Left whiskering preserves symmetry up to a 3-cell. -/
def whiskerLeft_symm {M N P : Term}
    (r : ReductionSeq M N) {p q : ReductionSeq N P}
    (α : Homotopy2 p q) :
    HigherTerms.Homotopy3 (whiskerLeft r (Homotopy2.symm α))
      (Homotopy2.symm (whiskerLeft r α)) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.whiskerLeftSymm r α)

/-- Right whiskering preserves symmetry up to a 3-cell. -/
def whiskerRight_symm {M N P : Term}
    {p q : ReductionSeq M N} (α : Homotopy2 p q)
    (s : ReductionSeq N P) :
    HigherTerms.Homotopy3 (whiskerRight (Homotopy2.symm α) s)
      (Homotopy2.symm (whiskerRight α s)) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.whiskerRightSymm α s)

/-! ## Interchange Law -/

/-- Interchange is witnessed by a 3-cell. -/
def interchange {M N P : Term}
    {p p' : ReductionSeq M N} {q q' : ReductionSeq N P}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    HigherTerms.Homotopy3 (hcomp α β)
      (Homotopy2.trans (whiskerRight α q) (whiskerLeft p' β)) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.interchange α β)

/-- Alternative interchange witness using the other parenthesization. -/
def interchange' {M N P : Term}
    {p p' : ReductionSeq M N} {q q' : ReductionSeq N P}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    HigherTerms.Homotopy3 (hcomp α β)
      (Homotopy2.trans (whiskerLeft p β) (whiskerRight α q')) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.interchange' α β)

/-! ## Associativity Coherence (Pentagon) -/

/-- The associator 2-cell witnessing that concatenation is associative. -/
def associator {M N P Q : Term}
    (p : ReductionSeq M N) (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Homotopy2 (ReductionSeq.concat (ReductionSeq.concat p q) r)
      (ReductionSeq.concat p (ReductionSeq.concat q r)) :=
  HigherTerms.associator p q r

/-- Pentagon coherence is witnessed by a 3-cell. -/
def pentagon {M N P Q R : Term}
    (p : ReductionSeq M N) (q : ReductionSeq N P)
    (r : ReductionSeq P Q) (s : ReductionSeq Q R) :
    HigherTerms.Homotopy3
      (Homotopy2.trans (associator (ReductionSeq.concat p q) r s)
        (associator p q (ReductionSeq.concat r s)))
      (Homotopy2.trans
        (Homotopy2.trans (whiskerRight (associator p q r) s)
          (associator p (ReductionSeq.concat q r) s))
        (whiskerLeft p (associator q r s))) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.pentagon p q r s)

/-! ## Unit Coherence (Triangle) -/

/-- The left unitor. -/
def leftUnitor {M N : Term} (p : ReductionSeq M N) :
    Homotopy2 (ReductionSeq.concat (ReductionSeq.refl M) p) p :=
  HigherTerms.leftUnitor p

/-- The right unitor. -/
def rightUnitor {M N : Term} (p : ReductionSeq M N) :
    Homotopy2 (ReductionSeq.concat p (ReductionSeq.refl N)) p :=
  HigherTerms.rightUnitor p

/-- Triangle coherence is witnessed by a 3-cell. -/
def triangle {M N P : Term}
    (p : ReductionSeq M N) (q : ReductionSeq N P) :
    HigherTerms.Homotopy3
      (Homotopy2.trans (associator p (ReductionSeq.refl N) q)
        (whiskerLeft p (leftUnitor q)))
      (whiskerRight (rightUnitor p) q) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.triangle p q)

/-! ## Reflexive Coherence -/

/-- Every 2-cell admits its reflexive 3-cell. -/
def coherence_refl {M N : Term} {p q : ReductionSeq M N}
    (α : Homotopy2 p q) :
    HigherTerms.Homotopy3 α α :=
  HigherTerms.Homotopy3.refl α

/-! ## Coherence for Inverses -/

/-- Inverse of refl is homotopic to refl. -/
def inv_refl_homotopy {M : Term} :
    Homotopy2 (ReductionSeq.refl M).inv (ReductionSeq.refl M) :=
  Homotopy2.ofEq rfl

/-- Inverse distributes over composition up to homotopy. -/
def inv_concat {M N P : Term}
    (p : ReductionSeq M N) (q : ReductionSeq N P) :
    Homotopy2 (ReductionSeq.concat p q).inv
              (ReductionSeq.concat q.inv p.inv) :=
  Homotopy2.ofEq (ReductionSeq.inv_concat p q)

/-- Double inverse returns to the original path up to homotopy. -/
def inv_inv {M N : Term} (p : ReductionSeq M N) :
    Homotopy2 p.inv.inv p :=
  Homotopy2.ofEq (ReductionSeq.inv_inv p)

/-- Inverse commutes with left whiskering up to a 3-cell. -/
def inv_whiskerLeft {M N P : Term}
    (r : ReductionSeq M N) {p q : ReductionSeq N P}
    (α : Homotopy2 p q) :
    HigherTerms.Homotopy3 (Homotopy2.symm (whiskerLeft r α))
      (whiskerLeft r (Homotopy2.symm α)) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.invWhiskerLeft r α)

/-- Inverse commutes with right whiskering up to a 3-cell. -/
def inv_whiskerRight {M N P : Term}
    {p q : ReductionSeq M N} (α : Homotopy2 p q)
    (s : ReductionSeq N P) :
    HigherTerms.Homotopy3 (Homotopy2.symm (whiskerRight α s))
      (whiskerRight (Homotopy2.symm α) s) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.invWhiskerRight α s)

/-! ## Higher Reflexivity -/

/-- Every 2-cell admits its reflexive 3-cell. -/
def homotopy3_refl {M N : Term} {p q : ReductionSeq M N}
    (α : Homotopy2 p q) : HigherTerms.Homotopy3 α α :=
  HigherTerms.Homotopy3.refl α

/-! ## The Weak ω-Groupoid Structure -/

/-- The weak ω-groupoid structure on λ-terms, with coherence witnesses. -/
structure LambdaOmegaGroupoid where
  comp_assoc : {M N P Q : Term} → (p : ReductionSeq M N) → (q : ReductionSeq N P) →
    (r : ReductionSeq P Q) →
    ReductionSeq.concat (ReductionSeq.concat p q) r = ReductionSeq.concat p (ReductionSeq.concat q r)
  comp_id_left : {M N : Term} → (p : ReductionSeq M N) →
    ReductionSeq.concat (ReductionSeq.refl M) p = p
  comp_id_right : {M N : Term} → (p : ReductionSeq M N) →
    ReductionSeq.concat p (ReductionSeq.refl N) = p
  hom3_refl : {M N : Term} → {p q : ReductionSeq M N} →
    (α : Homotopy2 p q) → HigherTerms.Homotopy3 α α
  pentagon_coh : {M N P Q R : Term} → (p : ReductionSeq M N) → (q : ReductionSeq N P) →
    (r : ReductionSeq P Q) → (s : ReductionSeq Q R) →
    HigherTerms.Homotopy3
      (Homotopy2.trans (associator (ReductionSeq.concat p q) r s)
        (associator p q (ReductionSeq.concat r s)))
      (Homotopy2.trans
        (Homotopy2.trans (whiskerRight (associator p q r) s)
          (associator p (ReductionSeq.concat q r) s))
        (whiskerLeft p (associator q r s)))
  triangle_coh : {M N P : Term} → (p : ReductionSeq M N) → (q : ReductionSeq N P) →
    HigherTerms.Homotopy3
      (Homotopy2.trans (associator p (ReductionSeq.refl N) q)
        (whiskerLeft p (leftUnitor q)))
      (whiskerRight (rightUnitor p) q)
  interchange_coh : {M N P : Term} → {p p' : ReductionSeq M N} → {q q' : ReductionSeq N P} →
    (α : Homotopy2 p p') → (β : Homotopy2 q q') →
    HigherTerms.Homotopy3 (hcomp α β)
      (Homotopy2.trans (whiskerRight α q) (whiskerLeft p' β))

/-- The canonical weak ω-groupoid structure on λ-terms. -/
def lambdaOmegaGroupoid : LambdaOmegaGroupoid := {
  comp_assoc := ReductionSeq.concat_assoc
  comp_id_left := ReductionSeq.concat_refl_left
  comp_id_right := ReductionSeq.concat_refl_right
  hom3_refl := fun {_} {_} {_} {_} α => coherence_refl α
  pentagon_coh := pentagon
  triangle_coh := triangle
  interchange_coh := interchange
}

end HigherLambdaModel.Lambda.Coherence
