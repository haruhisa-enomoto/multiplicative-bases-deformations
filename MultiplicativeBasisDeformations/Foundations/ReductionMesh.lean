module

public import MultiplicativeBasisDeformations.Foundations.CoveringIdeals
public import MultiplicativeBasisDeformations.Foundations.MeshDerivativeRows
public import MultiplicativeBasisDeformations.Foundations.PathGrading

/-!
# Reduction of path categories and mesh relations along a ring map

For a ring map `red : 𝒪 → k`, reduction of coefficients on the linear path categories
(`redP`): it preserves composition, paths and degrees, sends the mesh relations of
coefficients `ũ` to those of `c` when `red ∘ ũ = c`, maps the mesh ideal into the mesh
ideal, and (for surjective `red`) every element of the mesh ideal over `k` lifts to one
over `𝒪`. This is the right exactness used in Lemma B.2
(`characteristic-two-mesh-calculations.tex`: "Right exactness of tensor product
gives `coker D_m(E₄) ⊗ 𝔽₂ ≅ coker D_m(C⁽²⁾)`").
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u u' v w

namespace LinearPaths

variable {O : Type u} {k : Type u'} [CommRing O] [CommRing k] (red : O →+* k) {V : Type v} [Quiver.{w} V]

/-- Reduction of coefficients of a path combination. -/
def redP {x y : V} : (obj (k := O) x ⟶ obj (k := O) y) →+ (obj (k := k) x ⟶ obj (k := k) y) where
  toFun f := ofFinsupp (Finsupp.mapRange red (map_zero red) (toFinsupp f))
  map_zero' := by simp; rfl
  map_add' f g := by
    change ofFinsupp (Finsupp.mapRange red _ (toFinsupp f + toFinsupp g)) = _
    rw [Finsupp.mapRange_add (map_add red)]; rfl

theorem redP_apply {x y : V} (f : obj (k := O) x ⟶ obj (k := O) y) :
    redP red f = ofFinsupp (Finsupp.mapRange red (map_zero red) (toFinsupp f)) := rfl

theorem redP_smul {x y : V} (a : O) (f : obj (k := O) x ⟶ obj (k := O) y) :
    redP red (a • f) = red a • redP red f := by
  rw [redP_apply, redP_apply, toFinsupp_smul]
  change (Finsupp.mapRange red (map_zero red) (a • toFinsupp f) : Quiver.Path x y →₀ k) =
    red a • Finsupp.mapRange red (map_zero red) (toFinsupp f)
  ext p
  simp [map_mul]

theorem redP_path {x y : V} (p : Quiver.Path x y) : redP red (path (k := O) p) = path p := by
  rw [redP_apply, toFinsupp_path, Finsupp.mapRange_single, map_one]; rfl

theorem redP_smul_path {x y : V} (a : O) (p : Quiver.Path x y) :
    redP red (a • path (k := O) p) = red a • path p := by
  rw [redP_smul, redP_path]

theorem redP_comp {x y z : V} (f : obj (k := O) x ⟶ obj (k := O) y)
    (g : obj (k := O) y ⟶ obj (k := O) z) : redP red (f ≫ g) = redP red f ≫ redP red g := by
  induction f using induction_on with
  | h0 => simp
  | hadd f₁ f₂ h₁ h₂ => rw [Preadditive.add_comp, map_add, h₁, h₂, map_add, Preadditive.add_comp]
  | hsingle p a =>
      induction g using induction_on with
      | h0 => simp
      | hadd g₁ g₂ h₁ h₂ =>
          rw [Preadditive.comp_add, map_add, h₁, h₂, map_add, Preadditive.comp_add]
      | hsingle q b =>
          rw [Linear.smul_comp, Linear.comp_smul, path_comp_path, smul_smul, redP_smul_path,
            redP_smul_path, redP_smul_path, Linear.smul_comp, Linear.comp_smul, path_comp_path,
            smul_smul, map_mul]

theorem redP_degreePart {x y : V} {n : ℕ} {f : obj (k := O) x ⟶ obj (k := O) y}
    (hf : f ∈ degreePart (k := O) n x y) : redP red f ∈ degreePart (k := k) n x y := by
  induction hf using Submodule.span_induction with
  | mem f hf => obtain ⟨p, hp, rfl⟩ := hf; rw [redP_path]; exact Submodule.subset_span ⟨p, hp, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
  | smul a f _ hf => rw [redP_smul]; exact Submodule.smul_mem _ _ hf

variable {red}

/-- **Lifting path combinations**, within a degree. -/
theorem exists_lift (hred : Function.Surjective red) {x y : V} {n : ℕ}
    {g : obj (k := k) x ⟶ obj (k := k) y} (hg : g ∈ degreePart (k := k) n x y) :
    ∃ f ∈ degreePart (k := O) n x y, redP red f = g := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨p, hp, rfl⟩ := hg
      exact ⟨path p, Submodule.subset_span ⟨p, hp, rfl⟩, redP_path red p⟩
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add g g' _ _ hg hg' =>
      obtain ⟨f, hf, rfl⟩ := hg
      obtain ⟨f', hf', rfl⟩ := hg'
      exact ⟨f + f', add_mem hf hf', map_add _ _ _⟩
  | smul a g _ hg =>
      obtain ⟨f, hf, rfl⟩ := hg
      obtain ⟨a', rfl⟩ := hred a
      exact ⟨a' • f, Submodule.smul_mem _ _ hf, redP_smul red a' f⟩

/-- Every path combination lifts. -/
theorem exists_lift' (hred : Function.Surjective red) {x y : V}
    (g : obj (k := k) x ⟶ obj (k := k) y) : ∃ f : obj (k := O) x ⟶ obj (k := O) y,
      redP red f = g := by
  induction g using induction_on with
  | h0 => exact ⟨0, map_zero _⟩
  | hadd g g' hg hg' =>
      obtain ⟨f, rfl⟩ := hg
      obtain ⟨f', rfl⟩ := hg'
      exact ⟨f + f', map_add _ _ _⟩
  | hsingle p a =>
      obtain ⟨a', rfl⟩ := hred a
      exact ⟨a' • path p, redP_smul_path red a' p⟩

end LinearPaths

namespace ScalarMeshCategory

open LinearPaths

variable {O : Type u} {k : Type u'} [CommRing O] [CommRing k] {red : O →+* k} {V : Type v} [Quiver.{w} V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  {u : MeshCoefficients O Q} {c : MeshCoefficients k Q}
  (hred : ∀ x y a, red (u x y a : O) = (c x y a : k))

include hred in
theorem redP_meshRelation (x : Q.nonprojective) :
    redP red (meshRelation u x) = meshRelation c x := by
  unfold meshRelation
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [redP_smul_path, hred]

include hred in
/-- **The mesh ideal reduces into the mesh ideal.** -/
theorem redP_mem_ideal {X Y : V} {f : LinearPaths.obj (k := O) X ⟶ LinearPaths.obj (k := O) Y}
    (hf : f ∈ (RelSystem.mesh u).ideal _ _) : redP red f ∈ (RelSystem.mesh c).ideal _ _ := by
  refine (RelSystem.mesh u).ideal_induction (P := fun f ↦ redP red f ∈ (RelSystem.mesh c).ideal _ _)
    (by rw [map_zero]; exact zero_mem _) (fun f g hf hg ↦ by rw [map_add]; exact add_mem hf hg)
    (fun a f hf ↦ by rw [redP_smul]; exact Submodule.smul_mem _ _ hf) (fun i p p' ↦ ?_) hf
  rw [redP_comp, redP_comp, redP_path, redP_path]
  have e := redP_meshRelation hred i
  erw [e]
  exact (RelSystem.mesh c).comp_rel_comp_mem i _ _

include hred in
/-- **The mesh ideal lifts.** -/
theorem exists_lift_ideal (hs : Function.Surjective red) {X Y : V}
    {g : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj (k := k) Y} (hg : g ∈ (RelSystem.mesh c).ideal _ _) :
    ∃ f ∈ (RelSystem.mesh u).ideal _ _, redP red f = g := by
  refine (RelSystem.mesh c).ideal_induction
    (P := fun g ↦ ∃ f ∈ (RelSystem.mesh u).ideal _ _, redP red f = g)
    ⟨0, zero_mem _, map_zero _⟩ (fun g g' ⟨f, hf, hfg⟩ ⟨f', hf', hfg'⟩ ↦
      ⟨f + f', add_mem hf hf', by rw [map_add, hfg, hfg']⟩)
    (fun a g ⟨f, hf, hfg⟩ ↦ by
      obtain ⟨a', rfl⟩ := hs a
      exact ⟨a' • f, Submodule.smul_mem _ _ hf, by rw [redP_smul, hfg]⟩) (fun i p p' ↦ ?_) hg
  refine ⟨path p ≫ (RelSystem.mesh u).rel i ≫ path p',
    (RelSystem.mesh u).comp_rel_comp_mem i _ _, ?_⟩
  rw [redP_comp, redP_comp, redP_path, redP_path]
  have e := redP_meshRelation hred i
  erw [e]
  rfl

/-! ### Reduction on the scalar mesh categories -/

include hred in
theorem functor_redP_eq {X Y : V} {Φ Φ' : LinearPaths.obj (k := O) X ⟶ LinearPaths.obj (k := O) Y}
    (h : (RelationCategory.functor O (meshRelations u)).map Φ =
      (RelationCategory.functor O (meshRelations u)).map Φ') :
    (RelationCategory.functor k (meshRelations c)).map (redP red Φ) =
      (RelationCategory.functor k (meshRelations c)).map (redP red Φ') := by
  rw [← sub_eq_zero, ← Functor.map_sub, ← map_sub, RelationCategory.functor_map_eq_zero_iff]
  rw [← sub_eq_zero, ← Functor.map_sub, RelationCategory.functor_map_eq_zero_iff] at h
  exact redP_mem_ideal hred h

variable (red u c) in
/-- **Reduction of morphisms of the scalar mesh category.** -/
def redE {X Y : V} (φ : obj u X ⟶ obj u Y) : obj c X ⟶ obj c Y :=
  (RelationCategory.functor k (meshRelations c)).map
    (redP red (Classical.choose (RelationCategory.functor_map_surjective (k := O) _ φ)))

include hred in
theorem redE_map {X Y : V} (Φ : LinearPaths.obj (k := O) X ⟶ LinearPaths.obj (k := O) Y) :
    redE red u c ((RelationCategory.functor O (meshRelations u)).map Φ) =
      (RelationCategory.functor k (meshRelations c)).map (redP red Φ) :=
  functor_redP_eq hred (Classical.choose_spec (RelationCategory.functor_map_surjective (k := O) _ _))

include hred in
theorem redE_add {X Y : V} (φ ψ : obj u X ⟶ obj u Y) :
    redE red u c (φ + ψ) = redE red u c φ + redE red u c ψ := by
  obtain ⟨Φ, rfl⟩ := RelationCategory.functor_map_surjective (k := O) _ φ
  obtain ⟨Ψ, rfl⟩ := RelationCategory.functor_map_surjective (k := O) _ ψ
  rw [← Functor.map_add, redE_map hred, redE_map hred, redE_map hred, map_add, Functor.map_add]

include hred in
theorem redE_zero {X Y : V} : redE red u c (0 : obj u X ⟶ obj u Y) = 0 := by
  rw [← Functor.map_zero (RelationCategory.functor O (meshRelations u)) (LinearPaths.obj X)
    (LinearPaths.obj Y), redE_map hred, map_zero, Functor.map_zero]

include hred in
theorem redE_sub {X Y : V} (φ ψ : obj u X ⟶ obj u Y) :
    redE red u c (φ - ψ) = redE red u c φ - redE red u c ψ := by
  rw [eq_sub_iff_add_eq, ← redE_add hred, sub_add_cancel]

include hred in
theorem redE_smul {X Y : V} (a : O) (φ : obj u X ⟶ obj u Y) :
    redE red u c (a • φ) = red a • redE red u c φ := by
  obtain ⟨Φ, rfl⟩ := RelationCategory.functor_map_surjective (k := O) _ φ
  rw [← Functor.map_smul, redE_map hred, redE_map hred, redP_smul, Functor.map_smul]

include hred in
theorem redE_sum {X Y : V} {ι : Type*} (s : Finset ι) (φ : ι → (obj u X ⟶ obj u Y)) :
    redE red u c (∑ i ∈ s, φ i) = ∑ i ∈ s, redE red u c (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [redE_zero hred]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, redE_add hred, ih]

include hred in
theorem redE_comp {X Y Z : V} (φ : obj u X ⟶ obj u Y) (ψ : obj u Y ⟶ obj u Z) :
    redE red u c (φ ≫ ψ) = redE red u c φ ≫ redE red u c ψ := by
  obtain ⟨Φ, rfl⟩ := RelationCategory.functor_map_surjective (k := O) _ φ
  obtain ⟨Ψ, rfl⟩ := RelationCategory.functor_map_surjective (k := O) _ ψ
  rw [← Functor.map_comp, redE_map hred, redE_map hred, redE_map hred, redP_comp, Functor.map_comp]

include hred in
theorem redE_pathMor {X Y : V} (p : Quiver.Path X Y) : redE red u c (pathMor u p) = pathMor c p := by
  rw [pathMor, redE_map hred, redP_path]; rfl

include hred in
theorem redE_arrowMor {X Y : V} (a : X ⟶ Y) : redE red u c (arrowMor u a) = arrowMor c a :=
  redE_pathMor hred a.toPath

include hred in
theorem redE_degreePart {X Y : V} {n : ℕ} {φ : obj u X ⟶ obj u Y} (hφ : φ ∈ degreePart u n X Y) :
    redE red u c φ ∈ degreePart c n X Y := by
  obtain ⟨Φ, hΦ, rfl⟩ := hφ
  change redE red u c ((RelationCategory.functor O (meshRelations u)).map Φ) ∈ _
  rw [redE_map hred]
  exact ⟨_, redP_degreePart red hΦ, rfl⟩

include hred in
theorem exists_lift_degreePart (hs : Function.Surjective red) {X Y : V} {n : ℕ}
    {ψ : obj c X ⟶ obj c Y} (hψ : ψ ∈ degreePart c n X Y) :
    ∃ φ ∈ degreePart u n X Y, redE red u c φ = ψ := by
  obtain ⟨Ψ, hΨ, rfl⟩ := hψ
  obtain ⟨Φ, hΦ, hΦΨ⟩ := LinearPaths.exists_lift hs hΨ
  refine ⟨_, ⟨Φ, hΦ, rfl⟩, ?_⟩
  change redE red u c ((RelationCategory.functor O (meshRelations u)).map Φ) = _
  rw [redE_map hred, hΦΨ]; rfl

/-! ### Families -/

variable (red u c) in
/-- Reduction of arrow families. -/
def redA (f : ArrowFamily u) : ArrowFamily c := fun a ↦ redE red u c (f a)

variable (red u c) in
/-- Reduction of mesh families. -/
def redF (g : MeshFamily u) : MeshFamily c := fun x ↦ redE red u c (g x)

include hred in
theorem redF_meshDerivative (f : ArrowFamily u) :
    redF red u c (meshDerivative u f) = meshDerivative c (redA red u c f) := by
  funext x
  simp only [redF, redA, meshDerivative]
  rw [redE_sum hred]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [redE_smul hred, redE_add hred, redE_comp hred, redE_comp hred, redE_arrowMor hred,
    redE_arrowMor hred, hred]

theorem redF_add (g g' : MeshFamily u) (hred' : ∀ x y a, red (u x y a : O) = (c x y a : k)) :
    redF red u c (g + g') = redF red u c g + redF red u c g' :=
  funext fun x ↦ redE_add hred' (g x) (g' x)

include hred in
theorem redF_smul (a : O) (g : MeshFamily u) : redF red u c (a • g) = red a • redF red u c g :=
  funext fun x ↦ redE_smul hred a (g x)

include hred in
theorem redF_sub (g g' : MeshFamily u) : redF red u c (g - g') = redF red u c g - redF red u c g' :=
  funext fun x ↦ redE_sub hred (g x) (g' x)

include hred in
theorem redF_sum {ι : Type*} (s : Finset ι) (g : ι → MeshFamily u) :
    redF red u c (∑ i ∈ s, g i) = ∑ i ∈ s, redF red u c (g i) := by
  funext x
  simp only [redF, Finset.sum_apply]
  exact redE_sum hred s fun i ↦ g i x

include hred in
theorem redF_row [DecidableEq V] (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1) :
    redF red u c (row u x w) = row c x w := by
  funext x'
  simp only [redF, row]
  by_cases h : x' = x
  · subst h; rw [Pi.single_eq_same, Pi.single_eq_same, redE_pathMor hred]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, redE_zero hred]

end ScalarMeshCategory

end MultiplicativeBasisDeformations
