module

public import MBDVendor.QSE.CategoryTheory.IyamaNakayamaBoundary

/-!
# Split-component lifting between tau-sequences

This file begins the categorical chain-map lifting used in Iyama,
*Tau-categories I*, 3.5.2.  For two right tau-sequences, a split-epimorphic
right-endpoint component forces both earlier components to be split epic.
The mixed left-mesh-to-right-mesh specialization is built on this lemma.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama

open CategoricalRadical

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A chain map between right tau-sequences which is split epic at the right
endpoint is split epic in the other two degrees as well. -/
theorem RightTauSequence.splitEpi_components_of_splitEpi_τ₃
    {S T : ShortComplex C}
    (hS : RightTauSequence S) (hT : RightTauSequence T)
    (φ : S ⟶ T) [IsSplitEpi φ.τ₃] :
    IsSplitEpi φ.τ₁ ∧ IsSplitEpi φ.τ₂ := by
  have hTg : IsRadicalMorphism (T.g ≫ section_ φ.τ₃) :=
    isRadicalMorphism_postcomp (section_ φ.τ₃) hT.g_radical
  obtain ⟨ψ₂, hψ₂⟩ :=
    hS.factors_into_right (T.g ≫ section_ φ.τ₃) hTg
  have hfix₂ : (ψ₂ ≫ φ.τ₂) ≫ T.g = T.g := by
    calc
      (ψ₂ ≫ φ.τ₂) ≫ T.g = ψ₂ ≫ (φ.τ₂ ≫ T.g) :=
        Category.assoc _ _ _
      _ = ψ₂ ≫ (S.g ≫ φ.τ₃) := by rw [φ.comm₂₃]
      _ = (ψ₂ ≫ S.g) ≫ φ.τ₃ := (Category.assoc _ _ _).symm
      _ = (T.g ≫ section_ φ.τ₃) ≫ φ.τ₃ := by rw [hψ₂]
      _ = T.g := by simp
  letI : IsIso (ψ₂ ≫ φ.τ₂) :=
    hT.isRightMinimal_g (ψ₂ ≫ φ.τ₂) hfix₂
  let δ₂ : T.X₂ ⟶ S.X₂ := inv (ψ₂ ≫ φ.τ₂) ≫ ψ₂
  have hδ₂φ₂ : δ₂ ≫ φ.τ₂ = 𝟙 T.X₂ := by
    dsimp only [δ₂]
    rw [Category.assoc, IsIso.inv_hom_id]
  have hinvFix₂ : inv (ψ₂ ≫ φ.τ₂) ≫ T.g = T.g := by
    rw [← cancel_epi (ψ₂ ≫ φ.τ₂)]
    simpa only [IsIso.hom_inv_id_assoc] using hfix₂.symm
  have hδ₂g : δ₂ ≫ S.g = T.g ≫ section_ φ.τ₃ := by
    dsimp only [δ₂]
    rw [Category.assoc, hψ₂, ← Category.assoc, hinvFix₂]
  have hTfδ₂ : (T.f ≫ δ₂) ≫ S.g = 0 := by
    rw [Category.assoc, hδ₂g, ← Category.assoc, T.zero, zero_comp]
  obtain ⟨ψ₁, hψ₁⟩ :=
    (ShortComplex.isWeakKernel_iff S).mp hS.minimalWeakKernel.1
      (T.f ≫ δ₂) hTfδ₂
  have hfix₁ : (ψ₁ ≫ φ.τ₁) ≫ T.f = T.f := by
    calc
      (ψ₁ ≫ φ.τ₁) ≫ T.f = ψ₁ ≫ (φ.τ₁ ≫ T.f) :=
        Category.assoc _ _ _
      _ = ψ₁ ≫ (S.f ≫ φ.τ₂) := by rw [φ.comm₁₂]
      _ = (ψ₁ ≫ S.f) ≫ φ.τ₂ := (Category.assoc _ _ _).symm
      _ = (T.f ≫ δ₂) ≫ φ.τ₂ := by rw [hψ₁]
      _ = T.f ≫ (δ₂ ≫ φ.τ₂) := Category.assoc _ _ _
      _ = T.f := by rw [hδ₂φ₂, Category.comp_id]
  letI : IsIso (ψ₁ ≫ φ.τ₁) :=
    hT.minimalWeakKernel.2 (ψ₁ ≫ φ.τ₁) hfix₁
  constructor
  · apply IsSplitEpi.mk'
    exact
      { section_ := inv (ψ₁ ≫ φ.τ₁) ≫ ψ₁
        id := by
          calc
            (inv (ψ₁ ≫ φ.τ₁) ≫ ψ₁) ≫ φ.τ₁ =
                inv (ψ₁ ≫ φ.τ₁) ≫ (ψ₁ ≫ φ.τ₁) :=
              Category.assoc _ _ _
            _ = 𝟙 T.X₁ := IsIso.inv_hom_id _ }
  · apply IsSplitEpi.mk'
    exact
      { section_ := δ₂
        id := hδ₂φ₂ }

/-- A chain map between left tau-sequences which is split monic at the left
endpoint is split monic in the other two degrees as well. -/
theorem LeftTauSequence.splitMono_components_of_splitMono_τ₁
    {S T : ShortComplex C}
    (hS : LeftTauSequence S) (hT : LeftTauSequence T)
    (phi : S ⟶ T) [IsSplitMono phi.τ₁] :
    IsSplitMono phi.τ₂ ∧ IsSplitMono phi.τ₃ := by
  have hSf : IsRadicalMorphism (retraction phi.τ₁ ≫ S.f) :=
    isRadicalMorphism_precomp (retraction phi.τ₁) hS.f_radical
  obtain ⟨psi₂, hpsi₂⟩ :=
    hT.factors_from_left (retraction phi.τ₁ ≫ S.f) hSf
  have hfix₂ : S.f ≫ (phi.τ₂ ≫ psi₂) = S.f := by
    calc
      S.f ≫ (phi.τ₂ ≫ psi₂) =
          (S.f ≫ phi.τ₂) ≫ psi₂ :=
        (Category.assoc _ _ _).symm
      _ = (phi.τ₁ ≫ T.f) ≫ psi₂ := by rw [phi.comm₁₂]
      _ = phi.τ₁ ≫ (T.f ≫ psi₂) := Category.assoc _ _ _
      _ = phi.τ₁ ≫ (retraction phi.τ₁ ≫ S.f) := by rw [hpsi₂]
      _ = S.f := by rw [← Category.assoc, IsSplitMono.id, Category.id_comp]
  letI : IsIso (phi.τ₂ ≫ psi₂) :=
    hS.isLeftMinimal_f (phi.τ₂ ≫ psi₂) hfix₂
  let delta₂ : T.X₂ ⟶ S.X₂ := psi₂ ≫ inv (phi.τ₂ ≫ psi₂)
  have hphi₂delta₂ : phi.τ₂ ≫ delta₂ = 𝟙 S.X₂ := by
    dsimp only [delta₂]
    rw [← Category.assoc, IsIso.hom_inv_id]
  have hfinv₂ : S.f ≫ inv (phi.τ₂ ≫ psi₂) = S.f := by
    rw [← cancel_mono (phi.τ₂ ≫ psi₂)]
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact hfix₂.symm
  have hTdelta₂ : T.f ≫ delta₂ = retraction phi.τ₁ ≫ S.f := by
    dsimp only [delta₂]
    rw [← Category.assoc, hpsi₂, Category.assoc, hfinv₂]
  have hdelta₂g : T.f ≫ (delta₂ ≫ S.g) = 0 := by
    rw [← Category.assoc, hTdelta₂, Category.assoc, S.zero, comp_zero]
  obtain ⟨psi₃, hpsi₃⟩ :=
    (ShortComplex.isWeakCokernel_iff T).mp hT.minimalWeakCokernel.1
      (delta₂ ≫ S.g) hdelta₂g
  have hfix₃ : S.g ≫ (phi.τ₃ ≫ psi₃) = S.g := by
    calc
      S.g ≫ (phi.τ₃ ≫ psi₃) =
          (S.g ≫ phi.τ₃) ≫ psi₃ :=
        (Category.assoc _ _ _).symm
      _ = (phi.τ₂ ≫ T.g) ≫ psi₃ := by rw [phi.comm₂₃]
      _ = phi.τ₂ ≫ (T.g ≫ psi₃) := Category.assoc _ _ _
      _ = phi.τ₂ ≫ (delta₂ ≫ S.g) := by rw [hpsi₃]
      _ = S.g := by rw [← Category.assoc, hphi₂delta₂, Category.id_comp]
  letI : IsIso (phi.τ₃ ≫ psi₃) :=
    hS.minimalWeakCokernel.2 (phi.τ₃ ≫ psi₃) hfix₃
  constructor
  · apply IsSplitMono.mk'
    exact
      { retraction := delta₂
        id := hphi₂delta₂ }
  · apply IsSplitMono.mk'
    exact
      { retraction := psi₃ ≫ inv (phi.τ₃ ≫ psi₃)
        id := by
          rw [← Category.assoc, IsIso.hom_inv_id] }

end MBDVendor.QSE.Iyama
