import VerifiedAgora.tagger
noncomputable section

namespace CategoryTheory.ProjectiveResolution

open CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Projective

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C] (Z : C)
@[target]
lemma ofComplex_exactAt_succ (n : ℕ) :
    (ofComplex Z).ExactAt (n + 1) := by
  sorry