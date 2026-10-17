import MultiplicativeBasisDeformations.Foundations.IntegralLifts
import MultiplicativeBasisDeformations.Foundations.GModLemmas

/-!
# Exact mesh relations for the lifted arrows (Proposition 10.1(3))

`integral-deformations.tex`: "The category `E₄` has a quadratic scalar mesh
presentation with unit coefficients reducing to the all-one presentation."

We use only the part needed later: the lifted arrows satisfy the mesh relations exactly for
unit coefficients `ũ` reducing to `c` (`WData.mesh_exact`). The mesh error of the lifted arrows
with the lifted coefficients reduces to zero, so it is twice an `A⁽²⁾`-map of degree two
(`exists_halfMap`); such a map is a combination of the length-two paths at the row, and
subtracting twice its coefficients corrects the mesh coefficients.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace WLift

open GExt

variable {Λ : Type*} [Ring Λ] [Algebra 𝔽₂ Λ] {GΛ : GAlg (R := 𝔽₂) Λ}
  {Λ' : Type*} [Ring Λ'] [Algebra (ZMod 4) Λ'] {GΛ' : GAlg (R := ZMod 4) Λ'} {π : Λ' →+* Λ}
  {M : Type*} [AddCommGroup M] [Module 𝔽₂ M] {M' : Type*} [AddCommGroup M']
  [Module (ZMod 4) M'] {MM' : GMod GΛ' M'} {MM : GMod GΛ M} {ρM : M' →+ M}
  {N : Type*} [AddCommGroup N] [Module 𝔽₂ N] {N' : Type*} [AddCommGroup N']
  [Module (ZMod 4) N'] {NN' : GMod GΛ' N'} {NN : GMod GΛ N} {ρN : N' →+ N}
  (HM : IsLift MM' MM π ρM) (HN : IsLift NN' NN π ρN)
  (e : M' →ₗ[ZMod 4] N') (he : ∀ m, ρN (e m) = 0)

include HM HN he in
theorem eq_of_ρ_eq {m n : M'} (h : ρM m = ρM n) : e m = e n := by
  obtain ⟨m', hm'⟩ := HM.ker (m - n) (by rw [map_sub, h, sub_self])
  have h0 : e (m - n) = 0 := by
    rw [hm', map_smul]
    have := HN.two_smul_eq_of_ρ (m := e m') (n := 0) (by rw [he, map_zero])
    rwa [smul_zero] at this
  rwa [map_sub, sub_eq_zero] at h0

/-- **Half of a map reducing to zero.** -/
def halfMap : M →ₗ[𝔽₂] N where
  toFun v := HN.half (e (Classical.choose (HM.ρ_surj v)))
  map_add' v w := by
    rw [← HN.half_add (he _) (he _), ← map_add]
    congr 1
    refine eq_of_ρ_eq HM HN e he ?_
    rw [map_add, Classical.choose_spec (HM.ρ_surj _), Classical.choose_spec (HM.ρ_surj _),
      Classical.choose_spec (HM.ρ_surj _)]
  map_smul' t v := by
    rw [RingHom.id_apply, ← Z4.red_lift t, ← HN.half_smul _ (he _), ← map_smul]
    congr 1
    refine eq_of_ρ_eq HM HN e he ?_
    rw [HM.smul, Classical.choose_spec (HM.ρ_surj _), Classical.choose_spec (HM.ρ_surj _),
      Z4.red_lift]

theorem halfMap_spec (m : M') : e m = HN.tw (halfMap HM HN e he (ρM m)) := by
  change e m = HN.tw (HN.half (e _))
  rw [HN.tw_half (he _)]
  exact eq_of_ρ_eq HM HN e he (Classical.choose_spec (HM.ρ_surj _)).symm

theorem halfMap_act (hπ : IsRed GΛ' GΛ π) (hact : ∀ m b, e (MM'.act m b) = NN'.act (e m) b)
    (v : M) (a : Λ) : halfMap HM HN e he (MM.act v a) = NN.act (halfMap HM HN e he v) a := by
  obtain ⟨m, rfl⟩ := HM.ρ_surj v
  obtain ⟨b, rfl⟩ := hπ.surj a
  apply HN.tw_injective
  rw [← HM.act, ← halfMap_spec, hact, halfMap_spec HM HN e he m, HN.tw_act]

theorem halfMap_deg {d : ℤ} (hdeg : ∀ p m, MM'.gr.IsHom p m → NN'.gr.IsHom (p + d) (e m))
    (p : ℤ) (v : M) (hv : MM.gr.IsHom p v) : NN.gr.IsHom (p + d) (halfMap HM HN e he v) := by
  obtain ⟨m, hm, rfl⟩ := HM.lift p v hv
  rw [← HN.half_eq_of_tw (halfMap_spec HM HN e he m).symm]
  exact HN.half_deg (hdeg p m hm) (he m)

end WLift


namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt WLift

attribute [local instance] Classical.decEq

/-- A path of length two is a composite of two arrows. -/
theorem path_length_two {V : Type} [Quiver.{0} V] {s t : V} (p : Quiver.Path s t)
    (hp : p.length = 2) : ∃ (y : V) (b : s ⟶ y) (a : y ⟶ t), p = b.toPath.comp a.toPath := by
  cases p with
  | nil => simp at hp
  | cons p' a =>
    cases p' with
    | nil => simp at hp
    | cons p'' b =>
      cases p'' with
      | nil => exact ⟨_, b, a, rfl⟩
      | cons _ _ => simp [Quiver.Path.length_cons] at hp

variable {V : Type} [Quiver.{0} V]
  [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients 𝔽₂ Q}
  {L : LocalFamily (k := 𝔽₂) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional 𝔽₂ (meshFam Q c x ⟶ meshFam Q c y)]
  {R : Type} [Fintype R] [DecidableEq R] {P : RaySys.Mult D.PV R} {T : TabIso D P}

/-- The length-two paths at a row are the mate composites. -/
theorem degreePart_two_eq (x : Q.nonprojective)
    {F : LinearPaths.obj (k := 𝔽₂) (Q.tau x).1 ⟶ LinearPaths.obj (k := 𝔽₂) x.1}
    (hF : F ∈ LinearPaths.degreePart 2 (Q.tau x).1 x.1) :
    ∃ l : (Σ y : V, y ⟶ x.1) → 𝔽₂, F = ∑ a, l a •
      LinearPaths.path ((Q.mate x a.1 a.2).toPath.comp a.2.toPath) := by
  have hmem : F ∈ Submodule.span 𝔽₂ (Set.range fun a : Σ y : V, y ⟶ x.1 ↦
      LinearPaths.path (k := 𝔽₂) ((Q.mate x a.1 a.2).toPath.comp a.2.toPath)) := by
    refine Submodule.span_le.2 ?_ hF
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨y, b, a, rfl⟩ := path_length_two p hp
    obtain rfl : b = Q.mate x y a := Subsingleton.elim _ _
    exact Submodule.subset_span ⟨⟨y, a⟩, rfl⟩
  obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝔽₂).1 hmem
  exact ⟨l, hl.symm⟩

variable (W : WData T)

/-- The mesh error of the lifted arrows with the Teichmüller coefficients. -/
def meshErr (x : Q.nonprojective) :
    (Fin (W.N (Q.tau x).1).n → ZMod 4) →ₗ[ZMod 4] (Fin (W.N x.1).n → ZMod 4) :=
  ∑ a : Σ y : V, y ⟶ x.1, Z4.lift (c x a.1 a.2 : 𝔽₂) • (W.φ a.2 ∘ₗ W.φ (Q.mate x a.1 a.2))

theorem meshErr_apply (x : Q.nonprojective) (m : Fin (W.N (Q.tau x).1).n → ZMod 4) :
    meshErr W x m = ∑ a : Σ y : V, y ⟶ x.1,
      Z4.lift (c x a.1 a.2 : 𝔽₂) • W.φ a.2 (W.φ (Q.mate x a.1 a.2) m) := by
  simp [meshErr, LinearMap.sum_apply]

theorem ρ_meshErr (x : Q.nonprojective) (m : Fin (W.N (Q.tau x).1).n → ZMod 4) :
    ρF (W.N x.1).β (meshErr W x m) = 0 := by
  have h := congrArg (fun f ↦ f (ρF (W.N (Q.tau x).1).β m)) (mesh_fA (D := D) x)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.zero_apply] at h
  rw [meshErr_apply, map_sum, ← h]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [ρF_smul, Z4.red_lift, W.φ_red, W.φ_red]

set_option maxHeartbeats 2000000 in
theorem meshErr_act (x : Q.nonprojective) (m : Fin (W.N (Q.tau x).1).n → ZMod 4)
    (b : P.Lin (ZMod 4)) :
    meshErr W x ((W.N (Q.tau x).1).MM.act m b) = (W.N x.1).MM.act (meshErr W x m) b := by
  rw [meshErr_apply, meshErr_apply]
  rw [GMod.act_sum (W.N x.1).MM Finset.univ _ b]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [W.φ_act, W.φ_act, GMod.act_smul]

theorem meshErr_deg (x : Q.nonprojective) (p : ℤ) (m : Fin (W.N (Q.tau x).1).n → ZMod 4)
    (hm : (W.N (Q.tau x).1).MM.gr.IsHom p m) :
    (W.N x.1).MM.gr.IsHom (p + 2) (meshErr W x m) := by
  rw [meshErr_apply]
  refine (W.N x.1).MM.gr.isHom_sum _ _ fun a _ ↦ (W.N x.1).MM.gr.isHom_smul _ ?_
  have := W.φ_deg a.2 _ _ (W.φ_deg (Q.mate x a.1 a.2) p m hm)
  rwa [add_assoc, show (1 : ℤ) + 1 = 2 by norm_num] at this

/-- Half the mesh error, an `A⁽²⁾`-map `M_{τx} → M_x`. -/
def meshHalf (x : Q.nonprojective) :
    Rep D.F0 (meshFam Q c (Q.tau x).1) →ₗ[𝔽₂] Rep D.F0 (meshFam Q c x.1) :=
  halfMap (W.N (Q.tau x).1).lift (W.N x.1).lift (meshErr W x) (ρ_meshErr W x)

theorem exists_meshHalf_eq (x : Q.nonprojective) : ∃ l : (Σ y : V, y ⟶ x.1) → 𝔽₂,
    meshHalf W x = ∑ a, l a • (fA D a.2 ∘ₗ fA D (Q.mate x a.1 a.2)) := by
  have hact : ∀ m a, meshHalf W x (evAct D _ m a) = evAct D _ (meshHalf W x m) a :=
    fun m a ↦ halfMap_act (W.N (Q.tau x).1).lift (W.N x.1).lift (meshErr W x) (ρ_meshErr W x)
      (isRed_πO T) (meshErr_act W x) m a
  obtain ⟨f, hf⟩ := exists_repMap D (meshHalf W x) hact
  have hdeg : f ∈ degreePart c 2 (Q.tau x).1 x.1 :=
    mem_degreePart_of_repMap D (hfin2 (c := c)) fun p m hm ↦ by
      rw [← hf]
      exact halfMap_deg (W.N (Q.tau x).1).lift (W.N x.1).lift (meshErr W x) (ρ_meshErr W x)
        (meshErr_deg W x) p m hm
  obtain ⟨F, hF, rfl⟩ := hdeg
  obtain ⟨l, rfl⟩ := degreePart_two_eq x hF
  refine ⟨l, ?_⟩
  rw [hf]
  have e1 : (Functor.mapLinearMap 𝔽₂ (RelationCategory.functor 𝔽₂ (meshRelations c)))
      (∑ a, l a • LinearPaths.path ((Q.mate x a.1 a.2).toPath.comp a.2.toPath)) =
      ∑ a, l a • (arrowMor c (Q.mate x a.1 a.2) ≫ arrowMor c a.2) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [map_smul]
    congr 1
    exact pathMor_comp c _ _
  change rs D _ = _
  rw [e1, rs_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [rs_smul, ← rs_comp]
  rfl

theorem red_tw (a : 𝔽₂) : Z4.red (Z4.tw a) = 0 := by
  revert a; decide

/-- **Proposition 10.1(3), the relations**: the lifted arrows satisfy the mesh relations
exactly, for unit coefficients reducing to `c`. That they present `E₄` is `evO_surj` and
`evO_eq_zero_iff` (`IntegralPresentation.lean`). -/
theorem exists_meshUnits : ∃ u : MeshCoefficients (ZMod 4) Q,
    (∀ x y a, Z4.red (u x y a : ZMod 4) = c x y a) ∧
    ∀ x : Q.nonprojective, ∑ a : Σ y : V, y ⟶ x.1,
      ((u x a.1 a.2 : (ZMod 4)ˣ) : ZMod 4) • (W.φ a.2 ∘ₗ W.φ (Q.mate x a.1 a.2)) = 0 := by
  choose l hl using exists_meshHalf_eq W
  have hu : ∀ (x : Q.nonprojective) (y : V) (a : y ⟶ x.1),
      IsUnit (Z4.lift (c x y a : 𝔽₂) - Z4.tw (l x ⟨y, a⟩)) := fun x y a ↦
    Z4.isUnit_of_red_ne_zero (by rw [map_sub, Z4.red_lift, red_tw, sub_zero]; exact Units.ne_zero _)
  refine ⟨fun x y a ↦ (hu x y a).unit, fun x y a ↦ ?_, fun x ↦ ?_⟩
  · rw [IsUnit.unit_spec, map_sub, Z4.red_lift, red_tw, sub_zero]
  · refine LinearMap.ext fun m ↦ ?_
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, IsUnit.unit_spec,
      sub_smul, Finset.sum_sub_distrib, LinearMap.zero_apply]
    rw [← meshErr_apply, sub_eq_zero,
      halfMap_spec (W.N (Q.tau x).1).lift (W.N x.1).lift (meshErr W x) (ρ_meshErr W x) m]
    change (W.N x.1).lift.tw (meshHalf W x _) = _
    rw [hl x, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [LinearMap.smul_apply, (W.N x.1).lift.tw_smul_k, LinearMap.comp_apply, ← W.φ_red,
      ← W.φ_red, (W.N x.1).lift.tw_ρ, smul_smul, Z4.tw_apply, mul_comm]

end MeshWalk

end MultiplicativeBasisDeformations
