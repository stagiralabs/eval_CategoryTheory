import VerifiedAgora.tagger
namespace CategoryTheory.Functor

open CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Localization

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [HasShift D ℤ] [L.CommShift ℤ]
@[target]
lemma rotate_essImageDistTriang [Preadditive D] [L.Additive]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] (T : Triangle D) :
  T ∈ L.essImageDistTriang ↔ T.rotate ∈ L.essImageDistTriang := by
  sorry