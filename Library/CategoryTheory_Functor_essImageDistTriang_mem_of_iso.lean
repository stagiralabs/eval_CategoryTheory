import VerifiedAgora.tagger
namespace CategoryTheory.Functor

open CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Localization

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [HasShift D ℤ] [L.CommShift ℤ]
@[target]
lemma essImageDistTriang_mem_of_iso {T₁ T₂ : Triangle D} (e : T₂ ≅ T₁)
    (h : T₁ ∈ L.essImageDistTriang) : T₂ ∈ L.essImageDistTriang := by
  sorry