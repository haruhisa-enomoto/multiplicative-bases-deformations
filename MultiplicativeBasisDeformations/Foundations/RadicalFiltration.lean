import MultiplicativeBasisDeformations.Foundations.ARBridge

/-!
# The radical filtration of `ind(mod A)`

The powers `J^n` of the categorical radical of `ind(mod A)`
(`graded-category.tex`) form a decreasing multiplicative filtration:
`J^{n+1} ⊆ J^n` and `J^m ∘ J^n ⊆ J^{m+n}`. For a representation-finite algebra
the radical is nilpotent: the manuscript argues that `J` consists of the
matrix entries of the Jacobson radical of the endomorphism algebra of a finite
additive generator (`graded-category.tex`). The formal nilpotence uses
the vendored nilpotence of the categorical radical of `mod A`, which is proved
by that argument (`MBDVendor.Magnitude.Algebra.RightModuleRadical`,
`nilpotentRadicalDataOfArtinianGenerator`).
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MultiplicativeBasisDeformations.IndSkeleton

universe u v

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
variable (S : IndSkeleton k A)

/-- `J^0` is everything. -/
@[simp] theorem radPow_zero (X Y : S.Ind) : S.radPow 0 X Y = ⊤ := rfl

theorem mem_radPow_succ_of {X Z Y : S.Ind} {f : X ⟶ Z} {g : Z ⟶ Y} (hf : S.IsRadical f)
    {n : ℕ} (hg : g ∈ S.radPow n Z Y) : f ≫ g ∈ S.radPow (n + 1) X Y :=
  Submodule.subset_span ⟨Z, f, g, hf, hg, rfl⟩

/-- Precomposition with any morphism preserves radical morphisms. -/
theorem isRadical_precomp {W X Y : S.Ind} (a : W ⟶ X) {f : X ⟶ Y} (hf : S.IsRadical f) :
    S.IsRadical (a ≫ f) := by
  intro g
  have h1 : IsIso (𝟙 X - (f ≫ g) ≫ a) := by simpa [Category.assoc] using hf (g ≫ a)
  have h2 : IsIso (𝟙 W - a ≫ (f ≫ g)) := by
    obtain ⟨c, hc1, hc2⟩ := h1
    refine ⟨𝟙 W + a ≫ c ≫ f ≫ g, ?_, ?_⟩
    · have e1 : (𝟙 X - (f ≫ g) ≫ a) ≫ c = 𝟙 X := hc1
      calc (𝟙 W - a ≫ f ≫ g) ≫ (𝟙 W + a ≫ c ≫ f ≫ g)
          = 𝟙 W - a ≫ f ≫ g + a ≫ ((𝟙 X - (f ≫ g) ≫ a) ≫ c) ≫ f ≫ g := by
            simp only [Preadditive.sub_comp, Preadditive.comp_add, Preadditive.comp_sub,
              Category.id_comp, Category.comp_id, Category.assoc]
            try abel
        _ = 𝟙 W := by rw [e1]; simp
    · have e2 : c ≫ (𝟙 X - (f ≫ g) ≫ a) = 𝟙 X := hc2
      calc (𝟙 W + a ≫ c ≫ f ≫ g) ≫ (𝟙 W - a ≫ f ≫ g)
          = 𝟙 W - a ≫ f ≫ g + a ≫ (c ≫ (𝟙 X - (f ≫ g) ≫ a)) ≫ f ≫ g := by
            simp only [Preadditive.sub_comp, Preadditive.comp_add, Preadditive.comp_sub,
              Preadditive.add_comp, Category.id_comp, Category.comp_id, Category.assoc]
            try abel
        _ = 𝟙 W := by rw [e2]; simp
  simpa [Category.assoc] using h2

/-- Postcomposition with any morphism preserves radical morphisms. -/
theorem isRadical_postcomp {X Y Z : S.Ind} {f : X ⟶ Y} (hf : S.IsRadical f) (b : Y ⟶ Z) :
    S.IsRadical (f ≫ b) := by
  intro g
  simpa [Category.assoc] using hf (b ≫ g)

/-- `J^n` is closed under postcomposition with any morphism. -/
theorem comp_mem_radPow_left {X Y Z : S.Ind} {n : ℕ} {f : X ⟶ Y}
    (hf : f ∈ S.radPow n X Y) (g : Y ⟶ Z) : f ≫ g ∈ S.radPow n X Z := by
  induction n generalizing X with
  | zero => exact Submodule.mem_top
  | succ n ih =>
      change f ∈ Submodule.span k _ at hf
      induction hf using Submodule.span_induction with
      | mem h hh =>
          obtain ⟨W, f₁, g₁, hf₁, hg₁, rfl⟩ := hh
          rw [Category.assoc]
          exact S.mem_radPow_succ_of hf₁ (ih hg₁)
      | zero => simp
      | add a b _ _ ha hb => rw [Preadditive.add_comp]; exact add_mem ha hb
      | smul c a _ ha => rw [Linear.smul_comp]; exact Submodule.smul_mem _ c ha

/-- `J^n` is closed under precomposition with any morphism. -/
theorem comp_mem_radPow_right {X Y Z : S.Ind} {n : ℕ} (f : X ⟶ Y) {g : Y ⟶ Z}
    (hg : g ∈ S.radPow n Y Z) : f ≫ g ∈ S.radPow n X Z := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ n =>
      change g ∈ Submodule.span k _ at hg
      induction hg using Submodule.span_induction with
      | mem h hh =>
          obtain ⟨W, f₁, g₁, hf₁, hg₁, rfl⟩ := hh
          rw [← Category.assoc]
          exact S.mem_radPow_succ_of (S.isRadical_precomp f hf₁) hg₁
      | zero => simp
      | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact add_mem ha hb
      | smul c a _ ha => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c ha

/-- The filtration is multiplicative: `J^m ∘ J^n ⊆ J^{m+n}`. -/
theorem comp_mem_radPow {X Y Z : S.Ind} {m n : ℕ} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : f ∈ S.radPow m X Y) (hg : g ∈ S.radPow n Y Z) :
    f ≫ g ∈ S.radPow (m + n) X Z := by
  induction m generalizing X with
  | zero => simpa using S.comp_mem_radPow_right f hg
  | succ m ih =>
      change f ∈ Submodule.span k _ at hf
      rw [Nat.succ_add]
      induction hf using Submodule.span_induction with
      | mem h hh =>
          obtain ⟨W, f₁, g₁, hf₁, hg₁, rfl⟩ := hh
          rw [Category.assoc]
          exact S.mem_radPow_succ_of hf₁ (ih hg₁)
      | zero => simp
      | add a b _ _ ha hb => rw [Preadditive.add_comp]; exact add_mem ha hb
      | smul c a _ ha => rw [Linear.smul_comp]; exact Submodule.smul_mem _ c ha

/-- The filtration is decreasing: `J^{n+1} ⊆ J^n`. -/
theorem radPow_succ_le (n : ℕ) (X Y : S.Ind) : S.radPow (n + 1) X Y ≤ S.radPow n X Y := by
  intro f hf
  induction n generalizing X with
  | zero => exact Submodule.mem_top
  | succ n ih =>
      change f ∈ Submodule.span k _ at hf
      induction hf using Submodule.span_induction with
      | mem h hh =>
          obtain ⟨W, f₁, g₁, hf₁, hg₁, rfl⟩ := hh
          exact S.mem_radPow_succ_of hf₁ (ih W hg₁)
      | zero => simp
      | add a b _ _ ha hb => exact add_mem ha hb
      | smul c a _ ha => exact Submodule.smul_mem _ c ha

theorem radPow_anti {m n : ℕ} (h : m ≤ n) (X Y : S.Ind) :
    S.radPow n X Y ≤ S.radPow m X Y := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (S.radPow_succ_le _ X Y).trans ih

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A)

open MBDVendor.QSE.CategoricalIdeal MBDVendor.QSE.CategoricalRadical in
/-- The image of `J^n` in `mod A` lies in the `n`-th power of the vendored
radical ideal. -/
theorem map_mem_pow_of_mem_radPow {n : ℕ} {X Y : S.Ind} {f : X ⟶ Y}
    (hf : f ∈ S.radPow n X Y) :
    S.toFG.map f ∈ (HomIdeal.pow S.toVendor.fgNilpotentRadicalData.ideal n).hom _ _ := by
  induction n generalizing X with
  | zero => trivial
  | succ n ih =>
      rw [HomIdeal.pow_succ_eq_mul_pow]
      change f ∈ Submodule.span k _ at hf
      induction hf using Submodule.span_induction with
      | mem h hh =>
          obtain ⟨W, f₁, g₁, hf₁, hg₁, rfl⟩ := hh
          rw [Functor.map_comp]
          apply HomIdeal.comp_mem_mul
          · exact (S.toVendor.fgNilpotentRadicalData.mem_iff _).2 ((S.isRadical_iff f₁).1 hf₁)
          · exact ih hg₁
      | zero => rw [Functor.map_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [Functor.map_add]; exact add_mem ha hb
      | smul c a _ ha =>
          have h : S.toFG.map (c • a) = (c • 𝟙 _) ≫ S.toFG.map a := by
            simp [Functor.map_smul]
          rw [h]
          exact HomIdeal.precomp _ _ ha

/-- For a representation-finite algebra the radical of `ind(mod A)` is
nilpotent. -/
theorem exists_radPow_eq_bot : ∃ N : ℕ, ∀ X Y : S.Ind, S.radPow N X Y = ⊥ := by
  obtain ⟨N, hN⟩ := S.toVendor.fgNilpotentRadicalData.nilpotent
  refine ⟨N, fun X Y ↦ ?_⟩
  rw [eq_bot_iff]
  intro f hf
  have h := S.map_mem_pow_of_mem_radPow hf
  rw [hN] at h
  have h0 : S.toFG.map f = 0 := h
  rw [Submodule.mem_bot]
  exact S.toFG.map_injective (by rw [h0, Functor.map_zero])

end MultiplicativeBasisDeformations.IndSkeleton
