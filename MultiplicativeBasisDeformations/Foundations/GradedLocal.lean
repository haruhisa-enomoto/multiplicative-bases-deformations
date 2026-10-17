import MultiplicativeBasisDeformations.Foundations.LocalMesh
import MultiplicativeBasisDeformations.Foundations.MeshGrading

/-!
# The local structure of a finite-dimensional scalar mesh category

Proof of Lemma 2.7 (`graded-category.tex`): "The positive-degree ideal
is nilpotent, each degree-zero endomorphism ring is `k`, and degree-zero maps
between distinct objects vanish; so this ideal is the categorical radical."
For a finite-dimensional scalar mesh category on a finite translation quiver we
take as radical the span of the images of paths of positive length
(`radN 1`) and verify the axioms of `LocalFamily`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u w

namespace ScalarMeshCategory

variable {k : Type u} [Field k] {V : Type} [Quiver.{w} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (c : MeshCoefficients k Q)

/-- The span of the images of paths of length at least `n`. -/
def radN (n : ℕ) (x y : V) : Submodule k (obj c x ⟶ obj c y) :=
  Submodule.span k {f | ∃ p : Quiver.Path x y, n ≤ p.length ∧ f = pathMor c p}

theorem pathMor_mem_radN {n : ℕ} {x y : V} (p : Quiver.Path x y) (hp : n ≤ p.length) :
    pathMor c p ∈ radN c n x y :=
  Submodule.subset_span ⟨p, hp, rfl⟩

theorem radN_comp {m n : ℕ} {x y z : V} {f : obj c x ⟶ obj c y} {g : obj c y ⟶ obj c z}
    (hf : f ∈ radN c m x y) (hg : g ∈ radN c n y z) : f ≫ g ∈ radN c (m + n) x z := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨q, hq, rfl⟩ := hg
          rw [← pathMor_comp]
          exact pathMor_mem_radN c _ (by rw [Quiver.Path.length_comp]; omega)
      | zero => simp
      | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact add_mem ha hb
      | smul t a _ ha => rw [Linear.comp_smul]; exact Submodule.smul_mem _ t ha
  | zero => simp
  | add a b _ _ ha hb => rw [Preadditive.add_comp]; exact add_mem ha hb
  | smul t a _ ha => rw [Linear.smul_comp]; exact Submodule.smul_mem _ t ha

/-- Every morphism lies in `radN 0`. -/
theorem mem_radN_zero {x y : V} (f : obj c x ⟶ obj c y) : f ∈ radN c 0 x y := by
  obtain ⟨F, rfl⟩ := (RelationCategory.functor k (meshRelations c)).map_surjective f
  induction F using LinearPaths.induction_on with
  | h0 => simp
  | hadd F G hF hG => rw [Functor.map_add]; exact add_mem hF hG
  | hsingle p t =>
      rw [Functor.map_smul]
      exact Submodule.smul_mem _ t (pathMor_mem_radN c p (Nat.zero_le _))

theorem radN_eq_bot (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)) :
    ∃ N : ℕ, ∀ x y : V, radN c N x y = ⊥ := by
  obtain ⟨N, hN⟩ := exists_pathMor_eq_zero c hfin
  refine ⟨N, fun x y ↦ ?_⟩
  rw [eq_bot_iff, radN, Submodule.span_le]
  rintro _ ⟨p, hp, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_bot]
  exact hN x y p hp

/-- The degree-zero projection kills the mesh ideal. -/
theorem proj_zero_mem_ideal {x y : V} {F : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y}
    (hF : (RelationCategory.functor k (meshRelations c)).map F = 0) :
    LinearPaths.proj (k := k) 0 x y F = 0 := by
  rw [RelationCategory.functor_map_eq_zero_iff] at hF
  change F ∈ CategoricalIdeal.HomIdeal.generatedHomSubmodule k _ _ _ at hF
  induction hF using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨A, B, r, hr, a, b, rfl⟩ := hg
      obtain ⟨A', rfl⟩ : ∃ A' : V, LinearPaths.obj (k := k) A' = A := ⟨A, rfl⟩
      obtain ⟨B', rfl⟩ : ∃ B' : V, LinearPaths.obj (k := k) B' = B := ⟨B, rfl⟩
      obtain ⟨z, hX, hY, rfl⟩ := hr
      change A' = (Q.tau z).1 at hX
      change B' = z.1 at hY
      subst hX hY
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      have hdeg := meshRelation_mem_degreePart c z
      induction a using LinearPaths.induction_on with
      | h0 => simp
      | hadd a₁ a₂ h₁ h₂ => rw [Preadditive.add_comp, map_add, h₁, h₂, add_zero]
      | hsingle p t =>
          induction b using LinearPaths.induction_on with
          | h0 => simp
          | hadd b₁ b₂ h₁ h₂ => rw [Preadditive.comp_add, Preadditive.comp_add, map_add, h₁, h₂, add_zero]
          | hsingle q t' =>
              have hm := LinearPaths.comp_mem_degreePart
                (LinearPaths.comp_mem_degreePart (LinearPaths.path_mem_degreePart (k := k) p) hdeg)
                (LinearPaths.path_mem_degreePart (k := k) q)
              rw [Linear.smul_comp, Linear.comp_smul, Linear.comp_smul, map_smul, map_smul,
                Category.assoc, LinearPaths.proj_of_mem (by simpa [Category.assoc] using hm),
                if_neg (by omega), smul_zero, smul_zero]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul t a _ ha => rw [map_smul, ha, smul_zero]

/-- The positive-length part of a morphism of `kQ` maps into `radN 1`. -/
theorem sub_proj_zero_mem {x y : V} (F : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) :
    (RelationCategory.functor k (meshRelations c)).map (F - LinearPaths.proj 0 x y F) ∈
      radN c 1 x y := by
  induction F using LinearPaths.induction_on with
  | h0 => simp
  | hadd F G hF hG =>
      rw [map_add, show F + G - (LinearPaths.proj 0 x y F + LinearPaths.proj 0 x y G) =
        (F - LinearPaths.proj 0 x y F) + (G - LinearPaths.proj 0 x y G) by abel, Functor.map_add]
      exact add_mem hF hG
  | hsingle p t =>
      rw [map_smul, LinearPaths.proj_path, ← smul_sub, Functor.map_smul]
      refine Submodule.smul_mem _ t ?_
      split_ifs with h
      · simp
      · rw [sub_zero]
        exact pathMor_mem_radN c p (by omega)

theorem pathMor_nil_ne_zero (x : V) : pathMor c (Quiver.Path.nil : Quiver.Path x x) ≠ 0 := by
  intro h
  have := proj_zero_mem_ideal c h
  rw [LinearPaths.proj_path, if_pos (by rfl)] at this
  exact (Finsupp.single_ne_zero.2 one_ne_zero) this

theorem id_not_mem_radN (x : V) : 𝟙 (obj c x) ∉ radN c 1 x x := by
  intro h
  have hkill : ∀ f ∈ radN c 1 x x, degProj c 0 x x f = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨p, hp, rfl⟩ := hf
        rw [pathMor, degProj_apply, LinearPaths.proj_path, if_neg (by omega), Functor.map_zero]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul t a _ ha => rw [map_smul, ha, smul_zero]
  have h1 := hkill _ h
  have h2 : degProj c 0 x x (𝟙 (obj c x)) = 𝟙 (obj c x) := by
    have : 𝟙 (obj c x) = pathMor c (Quiver.Path.nil : Quiver.Path x x) := by
      rw [pathMor, ← CategoryTheory.Functor.map_id]; rfl
    rw [this, pathMor, degProj_apply, LinearPaths.proj_path, if_pos (by rfl)]
  rw [h2] at h1
  apply pathMor_nil_ne_zero c x
  rw [pathMor, ← h1]
  rw [← CategoryTheory.Functor.map_id]; rfl

theorem pow_mem_radN {x : V} {f : End (obj c x)} (hf : f ∈ radN c 1 x x) (n : ℕ) :
    f ^ n ∈ radN c n x x := by
  induction n with
  | zero => exact mem_radN_zero c _
  | succ n ih =>
      rw [pow_succ, End.mul_def]
      have := radN_comp c hf ih
      rwa [add_comm] at this

theorem prod_mem_radN (l : List (CatAlg.Alg (fun x : V ↦ obj c x)))
    (hl : ∀ a ∈ l, ∀ y z, a y z ∈ radN c 1 y z) (y z : V) : l.prod y z ∈ radN c l.length y z := by
  induction l generalizing y z with
  | nil => exact mem_radN_zero c _
  | cons a l ih =>
      rw [List.prod_cons, CatAlg.mul_apply, List.length_cons]
      refine Submodule.sum_mem _ fun t _ ↦ ?_
      have := radN_comp c (hl a List.mem_cons_self y t)
        (ih (fun b hb ↦ hl b (List.mem_cons_of_mem _ hb)) t z)
      rwa [add_comm] at this

/-- `graded-category.tex`: every positive-degree morphism into `x` is a
sum of composites with the arrows ending at `x`. -/
theorem exists_lastArrow {w x : V} {f : obj c w ⟶ obj c x} (hf : f ∈ radN c 1 w x) :
    ∃ g : ∀ a : Σ y : V, y ⟶ x, obj c w ⟶ obj c a.1, f = ∑ a, g a ≫ arrowMor c a.2 := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      cases p with
      | nil => simp at hp
      | cons p' α =>
          rename_i X
          let a₀ : Σ y : V, y ⟶ x := ⟨X, α⟩
          refine ⟨Function.update (fun _ ↦ 0) a₀ (pathMor c p'), ?_⟩
          rw [Finset.sum_eq_single a₀]
          · rw [Function.update_self, pathMor_cons]
          · intro a _ ha; rw [Function.update_of_ne ha, Limits.zero_comp]
          · simp
  | zero => exact ⟨fun _ ↦ 0, by simp⟩
  | add f g _ _ hf hg =>
      obtain ⟨G₁, rfl⟩ := hf
      obtain ⟨G₂, rfl⟩ := hg
      exact ⟨fun a ↦ G₁ a + G₂ a, by simp only [Preadditive.add_comp, Finset.sum_add_distrib]⟩
  | smul t f _ hf =>
      obtain ⟨G, rfl⟩ := hf
      exact ⟨fun a ↦ t • G a, by simp only [Linear.smul_comp, Finset.smul_sum]⟩

theorem arrowMor_mem_radN {x y : V} (a : x ⟶ y) : arrowMor c a ∈ radN c 1 x y := by
  rw [← pathMor_toPath]
  exact pathMor_mem_radN c _ (by simp)

/-- **The local structure of a finite-dimensional scalar mesh category.** -/
def localFamily (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)) :
    CatAlg.LocalFamily (k := k) (fun x : V ↦ obj c x) where
  rad x y := radN c 1 x y
  comp_left f _ hg := by
    have := radN_comp c (mem_radN_zero c f) hg
    rwa [zero_add] at this
  comp_right hf g := by
    have := radN_comp c hf (mem_radN_zero c g)
    rwa [add_zero] at this
  mem_of_ne {x y} h f := by
    obtain ⟨F, rfl⟩ := (RelationCategory.functor k (meshRelations c)).map_surjective f
    have h0 := LinearPaths.degreePart_zero_of_ne h (LinearPaths.proj_mem (d := 0) F)
    have := sub_proj_zero_mem c F
    rwa [h0, sub_zero] at this
  diag x f := by
    obtain ⟨F, rfl⟩ := (RelationCategory.functor k (meshRelations c)).map_surjective f
    have h0 := LinearPaths.degreePart_zero_self (LinearPaths.proj_mem (d := 0) F)
    refine ⟨LinearPaths.toFinsupp (LinearPaths.proj 0 x x F) Quiver.Path.nil, ?_⟩
    have := sub_proj_zero_mem c F
    rw [Functor.map_sub, h0, Functor.map_smul] at this
    convert this using 2
    rw [← CategoryTheory.Functor.map_id]; rfl
  id_not_mem x := id_not_mem_radN c x
  nilpotent x f hf := by
    obtain ⟨N, hN⟩ := radN_eq_bot c hfin
    refine ⟨N, ?_⟩
    have := pow_mem_radN c hf N
    rwa [hN, Submodule.mem_bot] at this
  idealNilp := by
    obtain ⟨N, hN⟩ := radN_eq_bot c hfin
    refine ⟨N, fun l hl hrad ↦ ?_⟩
    ext y z
    have h1 := prod_mem_radN c l hrad y z
    have h2 : radN c l.length y z ≤ radN c N y z := by
      rw [radN, radN]
      exact Submodule.span_mono fun f ⟨p, hp, hf⟩ ↦ ⟨p, le_trans hl hp, hf⟩
    have := h2 h1
    rw [hN, Submodule.mem_bot] at this
    exact this

end ScalarMeshCategory

end MultiplicativeBasisDeformations
