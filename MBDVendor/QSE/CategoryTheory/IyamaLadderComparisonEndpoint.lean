import MBDVendor.QSE.CategoryTheory.IyamaNakayamaBoundary

/-!
# The nonzero endpoint in Iyama's finite ladder comparison

This file proves the normalized endpoint step in Iyama, *Tau-categories I*,
6.3.1(2)(i), directly from the finite tau-category axioms.  A split-dominant
essential factor at a nonzero left-ladder domain is arrow-isomorphic to the
initial `muMinus` map.  The proof uses indecomposability, left-mesh uniqueness,
weak-cokernel exactness, and radical perturbation; it requires neither a
functor-category construction nor a concrete module classification.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama.LeftLadder.Comparison

open CategoricalRadical

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

omit [HasFiniteBiproducts C] in
/-- A split subobject of an indecomposable object is the whole object as soon
as its source is nonzero. -/
theorem isIso_of_isSplitMono_to_indecomposable
    {X Y : C} (hY : Indecomposable Y)
    (j : X ⟶ Y) [IsSplitMono j] (hX : ¬ IsZero X) :
    IsIso j := by
  let d := splitMonoComplement j
  let e : Y ≅ X ⊞ d.complement :=
    d.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso
      (BinaryBiproduct.isLimit _ _)
  have hcomp : IsZero d.complement :=
    (hY.2 X d.complement e).resolve_left hX
  apply IsIso.mk
  refine ⟨retraction j, IsSplitMono.id j, ?_⟩
  rw [← d.total]
  have hp : d.projection = 0 := hcomp.eq_of_tgt _ _
  have hi : d.inclusion = 0 := hcomp.eq_of_src _ _
  rw [hp, hi, zero_comp, add_zero]

omit [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- The middle component of the uniqueness isomorphism between two left
tau-sequences can be chosen above any prescribed left-endpoint isomorphism. -/
theorem exists_middle_iso_lifting_left_endpoint_iso
    {S T : ShortComplex C}
    (hS : LeftTauSequence S) (hT : LeftTauSequence T)
    (e₁ : S.X₁ ≅ T.X₁) :
    ∃ e₂ : S.X₂ ≅ T.X₂,
      e₁.hom ≫ T.f = S.f ≫ e₂.hom := by
  have hTf : IsRadicalMorphism (e₁.hom ≫ T.f) :=
    isRadicalMorphism_precomp e₁.hom hT.f_radical
  obtain ⟨a, ha⟩ := hS.factors_from_left (e₁.hom ≫ T.f) hTf
  have hSf : IsRadicalMorphism (e₁.inv ≫ S.f) :=
    isRadicalMorphism_precomp e₁.inv hS.f_radical
  obtain ⟨b, hb⟩ := hT.factors_from_left (e₁.inv ≫ S.f) hSf
  have hab : S.f ≫ (a ≫ b) = S.f := by
    calc
      S.f ≫ (a ≫ b) = (S.f ≫ a) ≫ b :=
        (Category.assoc _ _ _).symm
      _ = (e₁.hom ≫ T.f) ≫ b := by rw [ha]
      _ = e₁.hom ≫ (T.f ≫ b) := Category.assoc _ _ _
      _ = e₁.hom ≫ (e₁.inv ≫ S.f) := by rw [hb]
      _ = S.f := by simp
  have hba : T.f ≫ (b ≫ a) = T.f := by
    calc
      T.f ≫ (b ≫ a) = (T.f ≫ b) ≫ a :=
        (Category.assoc _ _ _).symm
      _ = (e₁.inv ≫ S.f) ≫ a := by rw [hb]
      _ = e₁.inv ≫ (S.f ≫ a) := Category.assoc _ _ _
      _ = e₁.inv ≫ (e₁.hom ≫ T.f) := by rw [ha]
      _ = T.f := by simp
  letI : IsIso (a ≫ b) := hS.isLeftMinimal_f (a ≫ b) hab
  letI : IsIso (b ≫ a) := hT.isLeftMinimal_f (b ≫ a) hba
  letI : IsIso a := isIso_of_isIso_comp_both a b
  exact ⟨asIso a, by simpa using ha.symm⟩

omit [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- Subtracting a radical morphism from an isomorphism remains invertible. -/
private theorem isIso_sub_of_isIso_of_isRadicalMorphism
    {X Y : C} (e r : X ⟶ Y) [IsIso e]
    (hr : IsRadicalMorphism r) : IsIso (e - r) := by
  have hq : IsRadicalMorphism (inv e ≫ r) :=
    isRadicalMorphism_precomp (inv e) hr
  haveI : IsIso (𝟙 Y - inv e ≫ r) := by
    simpa using hq (𝟙 Y)
  have heq : e - r = e ≫ (𝟙 Y - inv e ≫ r) := by
    simp [Preadditive.comp_sub]
  rw [heq]
  infer_instance

omit [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- A split epimorphism whose composite with a second map is invertible is
itself invertible. -/
theorem isIso_of_isSplitEpi_of_isIso_comp
    {X Y Z : C} (p : X ⟶ Y) [IsSplitEpi p] (t : Y ⟶ Z)
    [IsIso (p ≫ t)] : IsIso p := by
  let r : Y ⟶ X := t ≫ inv (p ≫ t)
  have hpr : p ≫ r = 𝟙 X := by
    dsimp only [r]
    rw [← Category.assoc, IsIso.hom_inv_id]
  have hrs : r = section_ p := by
    calc
      r = 𝟙 Y ≫ r := by simp
      _ = (section_ p ≫ p) ≫ r := by rw [IsSplitEpi.id p]
      _ = section_ p ≫ (p ≫ r) := Category.assoc _ _ _
      _ = section_ p := by rw [hpr, Category.comp_id]
  exact ⟨⟨r, hpr, hrs ▸ IsSplitEpi.id p⟩⟩

/-- Direct normalized form of the load-bearing endpoint step in Iyama
6.3.1(2)(i).

If a split-epi essential factor of the left mesh at a nonzero object is
left-dominated by `muMinus A`, then it is already arrow-isomorphic to
`muMinus A`.  The proof avoids a functor-category detour: the split source
map is invertible by indecomposability, and weak-cokernel exactness makes the
target composite an isomorphism modulo the categorical radical. -/
theorem nonempty_essentialArrow_iso_muMinus_of_leftDominance
    (T : FiniteTauCategoryData C Ind) (A : Ind)
    {Y Z : C}
    (p : (T.leftMesh Y).X₂ ⟶ Z) [IsSplitEpi p]
    (s : Y ⟶ (T.leftMesh (T.obj A)).X₁) [IsSplitMono s]
    (t : Z ⟶ (T.leftMesh (T.obj A)).X₂)
    (hY : ¬ IsZero Y)
    (hdom :
      s ≫ T.muMinus A =
        ((T.leftTermIso Y).inv ≫ (T.leftMesh Y).f ≫ p) ≫ t) :
    Nonempty
      (Arrow.mk
          ((T.leftTermIso Y).inv ≫ (T.leftMesh Y).f ≫ p) ≅
        Arrow.mk (T.muMinus A)) := by
  let s' : Y ⟶ T.obj A := s ≫ (T.leftTermIso (T.obj A)).hom
  letI : IsSplitMono s' := inferInstance
  have hs'I : IsIso s' :=
    isIso_of_isSplitMono_to_indecomposable (T.obj_indec A) s' hY
  letI : IsIso s' := hs'I
  have hsI : IsIso s := by
    apply IsIso.mk
    let r : (T.leftMesh (T.obj A)).X₁ ⟶ Y :=
      (T.leftTermIso (T.obj A)).hom ≫ inv s'
    refine ⟨r, ?_, ?_⟩
    · change s ≫ ((T.leftTermIso (T.obj A)).hom ≫ inv s') = 𝟙 _
      rw [← Category.assoc]
      exact IsIso.hom_inv_id s'
    · change ((T.leftTermIso (T.obj A)).hom ≫ inv s') ≫ s = 𝟙 _
      rw [← cancel_mono (T.leftTermIso (T.obj A)).hom]
      simp [s', Category.assoc]
  letI : IsIso s := hsI
  let e₁ : (T.leftMesh Y).X₁ ≅
      (T.leftMesh (T.obj A)).X₁ :=
    (T.leftTermIso Y).trans (asIso s)
  obtain ⟨e₂, he₂⟩ :=
    exists_middle_iso_lifting_left_endpoint_iso
      (T.leftTau Y) (T.leftTau (T.obj A)) e₁
  have hdom' :
      e₁.hom ≫ T.muMinus A =
        (T.leftMesh Y).f ≫ p ≫ t := by
    change
      ((T.leftTermIso Y).hom ≫ s) ≫ T.muMinus A =
        (T.leftMesh Y).f ≫ p ≫ t
    rw [Category.assoc, hdom]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hzero :
      (T.leftMesh Y).f ≫ (e₂.hom - p ≫ t) = 0 := by
    rw [Preadditive.comp_sub, ← he₂, hdom', sub_self]
  obtain ⟨q, hq⟩ :=
    (ShortComplex.isWeakCokernel_iff (T.leftMesh Y)).mp
      (T.leftTau Y).minimalWeakCokernel.1
      (e₂.hom - p ≫ t) hzero
  have hrad : IsRadicalMorphism ((T.leftMesh Y).g ≫ q) :=
    isRadicalMorphism_postcomp q (T.leftTau Y).g_radical
  have hpt : p ≫ t = e₂.hom - (T.leftMesh Y).g ≫ q := by
    rw [hq]
    abel
  have hptI : IsIso (p ≫ t) := by
    rw [hpt]
    exact isIso_sub_of_isIso_of_isRadicalMorphism
      e₂.hom ((T.leftMesh Y).g ≫ q) hrad
  letI : IsIso (p ≫ t) := hptI
  letI : IsIso p := isIso_of_isSplitEpi_of_isIso_comp p t
  have ht : t = inv p ≫ (p ≫ t) := by simp
  letI : IsIso t := by
    rw [ht]
    infer_instance
  exact ⟨Arrow.isoMk'
    ((T.leftTermIso Y).inv ≫ (T.leftMesh Y).f ≫ p)
    (T.muMinus A) (asIso s) (asIso t) hdom⟩

end MBDVendor.QSE.Iyama.LeftLadder.Comparison
