import MBDVendor.QSE.RepresentationTheory.AlmostSplitCofinite

/-!
# Irreducible morphisms in an abelian category

The canonical epi--mono image factorization shows that an irreducible
morphism in an abelian category is either monic or epic.  This is the
categorical step used in Ringel's support argument for an almost-split
sequence.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An irreducible morphism in an abelian category is monic or epic. -/
theorem IsIrreducibleMorphism.mono_or_epi
    {X Y : C} {f : X ⟶ Y} (hf : IsIrreducibleMorphism f) :
    Mono f ∨ Epi f := by
  rcases hf.factorization
      (Abelian.factorThruImage f) (Abelian.image.ι f)
      (Abelian.image.fac f) with hq | hi
  · left
    letI : IsSplitMono (Abelian.factorThruImage f) := hq
    letI : IsIso (Abelian.factorThruImage f) :=
      isIso_of_epi_of_isSplitMono _
    rw [← Abelian.image.fac f]
    infer_instance
  · right
    letI : IsSplitEpi (Abelian.image.ι f) := hi
    letI : IsIso (Abelian.image.ι f) :=
      isIso_of_mono_of_isSplitEpi _
    rw [← Abelian.image.fac f]
    infer_instance

/-- A componentwise form of the kernel argument in Ringel's support lemma.

Suppose every morphism killed by `g` factors through `f`.  If the component
`f ≫ p` is monic, then every monic morphism `j` into the middle object which
is orthogonal to `p` remains monic after composition with `g`. -/
theorem mono_comp_of_weakKernel_component
    {X Y Z U V : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hweak : ∀ (W : C) (q : W ⟶ Y), q ≫ g = 0 →
      ∃ l : W ⟶ X, l ≫ f = q)
    {p : Y ⟶ U} (hfp : Mono (f ≫ p))
    {j : V ⟶ Y} (hj : Mono j) (hjp : j ≫ p = 0) :
    Mono (j ≫ g) := by
  letI : Mono (f ≫ p) := hfp
  letI : Mono j := hj
  apply (Preadditive.mono_iff_cancel_zero (j ≫ g)).2
  intro W q hq
  obtain ⟨l, hl⟩ := hweak W (q ≫ j) (by
    simpa only [Category.assoc] using hq)
  have hl0 : l ≫ (f ≫ p) = 0 := by
    rw [← Category.assoc, hl, Category.assoc, hjp, comp_zero]
  have hlzero : l = 0 := zero_of_comp_mono _ hl0
  have hqjzero : q ≫ j = 0 := by
    rw [← hl, hlzero, zero_comp]
  exact zero_of_comp_mono _ hqjzero

namespace IndecomposableSkeleton

universe uR uι w

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
variable {ι : Type uι} (σ : IndecomposableSkeleton.{uR, uι, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The component from one chosen middle summand to the endpoint of a
minimal right almost-split map. -/
def MinimalRightAlmostSplitDecomposition.component
    {z : ι} (A : σ.MinimalRightAlmostSplitDecomposition z)
    (t : A.index) : σ.obj (A.label t) ⟶ σ.obj z :=
  let F : A.index → FGModuleCat.{w} R := fun j ↦ σ.obj (A.label j)
  biproduct.ι F t ≫ A.decomposition.inv ≫ A.map

/-- Each displayed component of a minimal right almost-split map is
irreducible. -/
theorem MinimalRightAlmostSplitDecomposition.component_irreducible
    {z : ι} (A : σ.MinimalRightAlmostSplitDecomposition z)
    (t : A.index) : IsIrreducibleMorphism (A.component σ t) := by
  let F : A.index → FGModuleCat.{w} R := fun j ↦ σ.obj (A.label j)
  let inc : F t ⟶ A.middle :=
    biproduct.ι F t ≫ A.decomposition.inv
  let proj : A.middle ⟶ F t :=
    A.decomposition.hom ≫ biproduct.π F t
  let g : F t ⟶ σ.obj z := inc ≫ A.map
  change IsIrreducibleMorphism g
  have hincproj : inc ≫ proj = 𝟙 (F t) := by
    simp [inc, proj, Category.assoc]
  have hnotepi : ¬ IsSplitEpi g := by
    intro hg
    apply A.rightAlmostSplit.not_isSplitEpi
    obtain ⟨se⟩ := hg.exists_splitEpi
    exact IsSplitEpi.mk'
      { section_ := se.section_ ≫ inc
        id := by
          simpa only [g, Category.assoc] using se.id }
  have hnotmono : ¬ IsSplitMono g := by
    intro hg
    letI : IsSplitMono g := hg
    exact hnotepi
      (isSplitEpi_of_isSplitMono_between_obj σ g)
  refine ⟨hnotmono, hnotepi, ?_⟩
  intro M a b hab
  by_cases hb : IsSplitEpi b
  · exact Or.inr hb
  · obtain ⟨c, hc⟩ := A.rightAlmostSplit.factors b hb
    let e : A.middle ⟶ A.middle :=
      𝟙 A.middle + proj ≫ (a ≫ c - inc)
    have hefix : e ≫ A.map = A.map := by
      dsimp only [e]
      rw [Preadditive.add_comp, Category.id_comp,
        Category.assoc, Preadditive.sub_comp]
      have hac : (a ≫ c) ≫ A.map = g := by
        rw [Category.assoc, hc, hab]
      rw [hac]
      change A.map + proj ≫ (g - g) = A.map
      simp
    have hince : inc ≫ e = a ≫ c := by
      dsimp only [e]
      rw [Preadditive.comp_add, Category.comp_id,
        ← Category.assoc, hincproj, Category.id_comp]
      abel
    letI : IsIso e := A.rightMinimal e hefix
    exact Or.inl (IsSplitMono.mk'
      { retraction := c ≫ inv e ≫ proj
        id := by
          calc
            a ≫ (c ≫ inv e ≫ proj) =
                (a ≫ c) ≫ inv e ≫ proj := by
                  simp only [Category.assoc]
            _ = (inc ≫ e) ≫ inv e ≫ proj := by rw [hince]
            _ = 𝟙 (F t) := by
                  simp only [Category.assoc,
                    IsIso.hom_inv_id_assoc, hincproj] })

/-- Every displayed right almost-split component is monic or epic. -/
theorem MinimalRightAlmostSplitDecomposition.component_mono_or_epi
    {z : ι} (A : σ.MinimalRightAlmostSplitDecomposition z)
    (t : A.index) : Mono (A.component σ t) ∨ Epi (A.component σ t) :=
  (A.component_irreducible σ t).mono_or_epi

/-- The component from the start of a minimal left almost-split map to one
chosen middle summand. -/
def MinimalLeftAlmostSplitDecomposition.component
    {z : ι} (A : σ.MinimalLeftAlmostSplitDecomposition z)
    (t : A.index) : σ.obj z ⟶ σ.obj (A.label t) :=
  let F : A.index → FGModuleCat.{w} R := fun j ↦ σ.obj (A.label j)
  A.map ≫ A.decomposition.hom ≫ biproduct.π F t

/-- Each displayed component of a minimal left almost-split map is
irreducible. -/
theorem MinimalLeftAlmostSplitDecomposition.component_irreducible
    {z : ι} (A : σ.MinimalLeftAlmostSplitDecomposition z)
    (t : A.index) : IsIrreducibleMorphism (A.component σ t) := by
  let F : A.index → FGModuleCat.{w} R := fun j ↦ σ.obj (A.label j)
  let inc : F t ⟶ A.middle :=
    biproduct.ι F t ≫ A.decomposition.inv
  let proj : A.middle ⟶ F t :=
    A.decomposition.hom ≫ biproduct.π F t
  let g : σ.obj z ⟶ F t := A.map ≫ proj
  change IsIrreducibleMorphism g
  have hincproj : inc ≫ proj = 𝟙 (F t) := by
    simp [inc, proj, Category.assoc]
  have hnotmono : ¬ IsSplitMono g := by
    intro hg
    apply A.leftAlmostSplit.not_isSplitMono
    obtain ⟨sm⟩ := hg.exists_splitMono
    exact IsSplitMono.mk'
      { retraction := proj ≫ sm.retraction
        id := by
          simpa only [g, Category.assoc] using sm.id }
  have hnotepi : ¬ IsSplitEpi g := by
    intro hg
    letI : IsSplitEpi g := hg
    exact hnotmono
      (isSplitMono_of_isSplitEpi_between_obj σ g)
  refine ⟨hnotmono, hnotepi, ?_⟩
  intro M a b hab
  by_cases ha : IsSplitMono a
  · exact Or.inl ha
  · obtain ⟨c, hc⟩ := A.leftAlmostSplit.factors a ha
    let e : A.middle ⟶ A.middle :=
      𝟙 A.middle + (c ≫ b - proj) ≫ inc
    have hefix : A.map ≫ e = A.map := by
      dsimp only [e]
      rw [Preadditive.comp_add, Category.comp_id,
        ← Category.assoc, Preadditive.comp_sub]
      have hcb : A.map ≫ (c ≫ b) = g := by
        rw [← Category.assoc, hc, hab]
      rw [hcb]
      change A.map + (g - g) ≫ inc = A.map
      simp
    have heproj : e ≫ proj = c ≫ b := by
      dsimp only [e]
      rw [Preadditive.add_comp, Category.id_comp,
        Category.assoc, hincproj, Category.comp_id]
      abel
    letI : IsIso e := A.leftMinimal e hefix
    exact Or.inr (IsSplitEpi.mk'
      { section_ := inc ≫ inv e ≫ c
        id := by
          calc
            (inc ≫ inv e ≫ c) ≫ b =
                inc ≫ inv e ≫ (c ≫ b) := by
                  simp only [Category.assoc]
            _ = inc ≫ inv e ≫ (e ≫ proj) := by rw [← heproj]
            _ = 𝟙 (F t) := by
                  simp only [IsIso.inv_hom_id_assoc, hincproj] })

/-- Every displayed left almost-split component is monic or epic. -/
theorem MinimalLeftAlmostSplitDecomposition.component_mono_or_epi
    {z : ι} (A : σ.MinimalLeftAlmostSplitDecomposition z)
    (t : A.index) : Mono (A.component σ t) ∨ Epi (A.component σ t) :=
  (A.component_irreducible σ t).mono_or_epi

end IndecomposableSkeleton

end MBDVendor.QSE
