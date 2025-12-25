import VerifiedAgora.tagger
noncomputable section

namespace CategoryTheory.ProjectiveResolution

open CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Projective

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C] (Z : C)
@[target]
lemma ofComplex_d_1_0 :
    (ofComplex Z).d 1 0 = d (Projective.π Z) := by
  sorry