import VerifiedAgora.tagger
namespace CategoryTheory.Functor

open CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Localization

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [HasShift D ℤ] [L.CommShift ℤ] [HasZeroObject D]
  [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [L.mapArrow.EssSurj] [L.IsTriangulated]
@[target]
lemma distTriang_iff (T : Triangle D) :
    (T ∈ distTriang D) ↔ T ∈ L.essImageDistTriang := by
  sorry