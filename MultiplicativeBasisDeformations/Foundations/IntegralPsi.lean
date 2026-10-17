import MultiplicativeBasisDeformations.Foundations.IntegralCorner
import MultiplicativeBasisDeformations.Foundations.CornerDeriv
import MultiplicativeBasisDeformations.Foundations.IntegralCoker

/-!
# Lemma 10.2 for twice a cocycle of `A⁽²⁾` (Proposition 10.3)

`integral-deformations.tex:122–210`. For a Hochschild cocycle `μ̄` of `A⁽²⁾` of positive degree
`q`, the cocycle `μ̃ = 2μ̄` of `𝒪P` is a coboundary (`exists_hcobdry_twice`): the corrections of
the lifted modules and arrows are twice those of `μ̄` (`IntegralTransport`); their mesh errors are
twice a family of degree `q + 2 ≥ 3`, a derivative by Lemma B.2 (`two_smul_mem_imageD`), so an
arrow change removes them; the projective corner of the lifted modules is `𝒪P`
(`corner_surj`, `corner_inj`), and `CornerDeriv.eq_hcobdry` concludes.

This is the composite `j = 0` and injectivity of `Ψ₄` used in the proof of Proposition 10.3,
restricted to the classes `i_*[μ̄]`, which is all that proof uses.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace PathEval

open GExt

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ] {GΛ : GAlg (R := R) Λ}
  {V : Type} [Quiver.{0} V] {N : V → Type*} [∀ X, AddCommGroup (N X)] [∀ X, Module R (N X)]
  {MM : ∀ X, GMod GΛ (N X)} {φ : ∀ {y x : V}, (y ⟶ x) → (N y →ₗ[R] N x)}
  (hφ : ∀ {y x : V} (a : y ⟶ x) m b, φ a ((MM y).act m b) = (MM x).act (φ a m) b)
include hφ

theorem evP_act_of {Y X : V} (p : Quiver.Path Y X) (m : N Y) (b : Λ) :
    evP N φ p ((MM Y).act m b) = (MM X).act (evP N φ p m) b := by
  induction p with
  | nil => rw [evP_nil]; rfl
  | cons p a ih => rw [evP_cons, LinearMap.comp_apply, ih, hφ, LinearMap.comp_apply]

theorem evL_act_of {Y X : V} (F : LinearPaths.obj (k := R) Y ⟶ LinearPaths.obj (k := R) X)
    (m : N Y) (b : Λ) : evL N φ F ((MM Y).act m b) = (MM X).act (evL N φ F m) b := by
  induction F using rq_induction with
  | h0 => simp
  | hadd F G hF hG => rw [map_add, LinearMap.add_apply, LinearMap.add_apply, hF, hG, map_add,
      LinearMap.add_apply]
  | hsmul t F hF => rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hF, GMod.act_smul]
  | hpath p => rw [evL_path, evP_act_of hφ]

end PathEval

namespace GExt

theorem GMod.act_neg {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ]
    {GΛ : GAlg (R := R) Λ} {M : Type*} [AddCommGroup M] [Module R M] (MM : GMod GΛ M) (m : M)
    (b : Λ) : MM.act (-m) b = -MM.act m b := by
  rw [map_neg, LinearMap.neg_apply]

end GExt

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt WLift PathEval

attribute [local instance] Classical.decEq

variable {V : Type} [Quiver.{0} V]
  [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients 𝔽₂ Q}
  {L : LocalFamily (k := 𝔽₂) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional 𝔽₂ (meshFam Q c x ⟶ meshFam Q c y)]
  {R : Type} [Fintype R] [DecidableEq R] {P : RaySys.Mult D.PV R} {T : TabIso D P}
  (W : WData T)

/-- The lifted module of `X`. -/
abbrev NW (X : V) : Type := Fin (W.N X).n → ZMod 4

/-- The evaluation of `𝒪Q` on the lifted modules. -/
abbrev evO {Y X : V} :
    (LinearPaths.obj (k := ZMod 4) Y ⟶ LinearPaths.obj (k := ZMod 4) X) →ₗ[ZMod 4] (NW W Y →ₗ[ZMod 4] NW W X) :=
  evL (NW W) W.φ

/-- The reduction of a lifted module. -/
abbrev ρW (X : V) : NW W X →+ Rep D.F0 (meshFam Q c X) := ρF (W.N X).β

/-- The image of a path combination in `C(Q, c)`. -/
abbrev imgk {Y X : V} (F : LinearPaths.obj (k := 𝔽₂) Y ⟶ LinearPaths.obj (k := 𝔽₂) X) :
    obj c Y ⟶ obj c X :=
  (RelationCategory.functor 𝔽₂ (meshRelations c)).map F

theorem imgk_add {Y X : V} (F G : LinearPaths.obj (k := 𝔽₂) Y ⟶ LinearPaths.obj (k := 𝔽₂) X) :
    imgk (c := c) (F + G) = imgk F + imgk G := Functor.map_add _

theorem imgk_smul {Y X : V} (t : 𝔽₂) (F : LinearPaths.obj (k := 𝔽₂) Y ⟶ LinearPaths.obj (k := 𝔽₂) X) :
    imgk (c := c) (t • F) = t • imgk F := Functor.map_smul _ _ _

theorem ρW_evP {Y X : V} (p : Quiver.Path Y X) (n : NW W Y) :
    ρW W X (evP (NW W) W.φ p n) = rs D (pathMor c p) (ρW W Y n) := by
  induction p with
  | nil => rw [evP_nil, pathMor_nil, rs_id]; rfl
  | cons p a ih => rw [evP_cons, LinearMap.comp_apply, W.φ_red, ih, rs_pathMor_cons]; rfl

/-- **Evaluation commutes with reduction.** -/
theorem ρW_evO {Y X : V} (F : LinearPaths.obj (k := ZMod 4) Y ⟶ LinearPaths.obj (k := ZMod 4) X)
    (n : NW W Y) : ρW W X (evO W F n) = rs D (imgk (LinearPaths.redP Z4.red F)) (ρW W Y n) := by
  induction F using rq_induction with
  | h0 => simp [rs_zero]
  | hadd F G hF hG =>
    rw [map_add, LinearMap.add_apply, map_add, hF, hG, map_add, imgk_add, rs_add,
      LinearMap.add_apply]
  | hsmul t F hF =>
    rw [map_smul, LinearMap.smul_apply, ρF_smul, hF, LinearPaths.redP_smul, imgk_smul,
      rs_smul, LinearMap.smul_apply]
  | hpath p => rw [evL_path, ρW_evP, LinearPaths.redP_path]; rfl

theorem evO_act {Y X : V} (F : LinearPaths.obj (k := ZMod 4) Y ⟶ LinearPaths.obj (k := ZMod 4) X)
    (m : NW W Y) (b : P.Lin (ZMod 4)) :
    evO W F ((W.N Y).MM.act m b) = (W.N X).MM.act (evO W F m) b :=
  evL_act_of (MM := fun X ↦ (W.N X).MM) (fun a m b ↦ W.φ_act a m b) F m b

/-! ### Evaluation of the mesh category over `𝒪` -/

section EvE

variable (u : MeshCoefficients (ZMod 4) Q)
  (hmesh : ∀ x : Q.nonprojective, ∑ a : Σ y : V, y ⟶ x.1,
    ((u x a.1 a.2 : (ZMod 4)ˣ) : ZMod 4) • (W.φ a.2 ∘ₗ W.φ (Q.mate x a.1 a.2)) = 0)

/-- The image of a path combination in `C(Q, ũ)`. -/
abbrev imgO {Y X : V} (F : LinearPaths.obj (k := ZMod 4) Y ⟶ LinearPaths.obj (k := ZMod 4) X) :
    obj u Y ⟶ obj u X :=
  (RelationCategory.functor (ZMod 4) (meshRelations u)).map F

/-- A preimage in `𝒪Q`. -/
def preO {Y X : V} (φ : obj u Y ⟶ obj u X) :
    LinearPaths.obj (k := ZMod 4) Y ⟶ LinearPaths.obj (k := ZMod 4) X :=
  Classical.choose (RelationCategory.functor_map_surjective (meshRelations u) φ)

theorem imgO_preO {Y X : V} (φ : obj u Y ⟶ obj u X) : imgO u (preO u φ) = φ :=
  Classical.choose_spec (RelationCategory.functor_map_surjective (meshRelations u) φ)

/-- **The evaluation of `C(Q, ũ)` on the lifted modules.** -/
def evE {Y X : V} (φ : obj u Y ⟶ obj u X) : NW W Y →ₗ[ZMod 4] NW W X := evO W (preO u φ)

variable {u}

include hmesh in
theorem evO_eq_of_imgO {Y X : V}
    {F G : LinearPaths.obj (k := ZMod 4) Y ⟶ LinearPaths.obj (k := ZMod 4) X}
    (h : imgO u F = imgO u G) : evO W F = evO W G := by
  have h0 : imgO u (F - G) = 0 := by
    simp only [imgO] at h ⊢
    rw [Functor.map_sub, h, sub_self]
  rw [RelationCategory.functor_map_eq_zero_iff] at h0
  have := evL_ideal hmesh h0
  rwa [map_sub, sub_eq_zero] at this

include hmesh in
theorem evE_imgO {Y X : V} (F : LinearPaths.obj (k := ZMod 4) Y ⟶ LinearPaths.obj (k := ZMod 4) X) :
    evE W u (imgO u F) = evO W F :=
  evO_eq_of_imgO W hmesh (imgO_preO u _)

include hmesh in
theorem evE_comp {Y X Z : V} (φ : obj u Y ⟶ obj u X) (ψ : obj u X ⟶ obj u Z) :
    evE W u (φ ≫ ψ) = evE W u ψ ∘ₗ evE W u φ := by
  rw [← imgO_preO u φ, ← imgO_preO u ψ, ← Functor.map_comp, evE_imgO W hmesh, evE_imgO W hmesh,
    evE_imgO W hmesh, evL_comp]

include hmesh in
theorem evE_add {Y X : V} (φ ψ : obj u Y ⟶ obj u X) :
    evE W u (φ + ψ) = evE W u φ + evE W u ψ := by
  rw [← imgO_preO u φ, ← imgO_preO u ψ, ← Functor.map_add, evE_imgO W hmesh, evE_imgO W hmesh,
    evE_imgO W hmesh, map_add]

include hmesh in
theorem evE_smul {Y X : V} (t : ZMod 4) (φ : obj u Y ⟶ obj u X) :
    evE W u (t • φ) = t • evE W u φ := by
  rw [← imgO_preO u φ, ← Functor.map_smul, evE_imgO W hmesh, evE_imgO W hmesh, map_smul]

include hmesh in
theorem evE_sum {Y X : V} {κ : Type*} (s : Finset κ) (φ : κ → (obj u Y ⟶ obj u X)) :
    evE W u (∑ i ∈ s, φ i) = ∑ i ∈ s, evE W u (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, ← Functor.map_zero
      (RelationCategory.functor (ZMod 4) (meshRelations u)) (LinearPaths.obj Y) (LinearPaths.obj X),
      evE_imgO W hmesh, map_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, evE_add W hmesh, ih]

include hmesh in
theorem evE_arrowMor {Y X : V} (a : Y ⟶ X) : evE W u (arrowMor u a) = W.φ a := by
  rw [arrowMor, evE_imgO W hmesh, LinearPaths.arrow, evL_path, evP_toPath]

include hmesh in
theorem evE_act {Y X : V} (φ : obj u Y ⟶ obj u X) (m : NW W Y)
    (b : P.Lin (ZMod 4)) :
    evE W u φ ((W.N Y).MM.act m b) = (W.N X).MM.act (evE W u φ m) b :=
  evO_act W _ m b

include hmesh in
/-- **The mesh derivative evaluates to the first-order mesh error of an arrow change.** -/
theorem evE_meshDerivative (f : ArrowFamily u) (x : Q.nonprojective) :
    evE W u (meshDerivative u f x) = ∑ a : Σ y : V, y ⟶ x.1, ((u x a.1 a.2 : (ZMod 4)ˣ) : ZMod 4) •
      (W.φ a.2 ∘ₗ evE W u (f ⟨(Q.tau x).1, a.1, Q.mate x a.1 a.2⟩) +
        evE W u (f ⟨a.1, x.1, a.2⟩) ∘ₗ W.φ (Q.mate x a.1 a.2)) := by
  rw [meshDerivative, evE_sum W hmesh]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [evE_smul W hmesh, evE_add W hmesh, evE_comp W hmesh, evE_comp W hmesh, evE_arrowMor W hmesh,
    evE_arrowMor W hmesh]

variable (hred : ∀ x y a, Z4.red (u x y a : ZMod 4) = (c x y a : 𝔽₂))

include hmesh hred in
/-- **Evaluation commutes with reduction**, on `C(Q, ũ)`. -/
theorem ρW_evE {Y X : V} (φ : obj u Y ⟶ obj u X) (n : NW W Y) :
    ρW W X (evE W u φ n) = rs D (redE Z4.red u c φ) (ρW W Y n) := by
  conv_rhs => rw [← imgO_preO u φ]
  rw [redE_map hred]
  exact ρW_evO W _ n

end EvE

/-! ### The projective corner -/

section Corner

variable (P) in
/-- The vertex idempotent `ẽ_s` of `𝒪P`. -/
abbrev eO (s : D.PV) : P.Lin (ZMod 4) :=
  P.b (ZMod 4) (P.e s)

theorem πO_eO (s : D.PV) : πO T (eO P s) = eP D s := by
  rw [πO_b, T.Θ_e]

theorem eO_idem (s : D.PV) : eO P s * eO P s = eO P s := by
  rw [RaySys.Mult.b_e_mul, if_pos (by rw [P.src_e])]

theorem sum_eO : ∑ s, eO P s = 1 := P.sum_b_e (ZMod 4)

theorem hψ1 (s : D.PV) (m : Rep D.F0 (meshFam Q c s.1)) :
    (gmodEv D (hfin2 (c := c)) s.1).act (unit (F := D.F0) s)
      (ψP D (hfin2 (c := c)) s m) = m :=
  act_ψP s m

theorem hψ2 (s : D.PV) (x : (Alg D.F0)ᵐᵒᵖ) :
    ψP D (hfin2 (c := c)) s ((gmodEv D (hfin2 (c := c)) s.1).act (unit (F := D.F0) s) x) =
      πO T (eO P s) * x := by
  rw [πO_eO]; exact ψP_gA s x

/-- The generator `w_s ∈ M̃_s`. -/
abbrev wO (s : D.PV) : NW W s.1 := wG (W.N s.1).lift (eO P s) (unit (F := D.F0) s)

/-- The regular corner `ψ̃_s : M̃_s → ẽ_s𝒪P`. -/
abbrev ψO (s : D.PV) : NW W s.1 →ₗ[ZMod 4] P.Lin (ZMod 4) :=
  ψG (isRed_πO T) (W.N s.1).lift (eO P s) (eO_idem s) (unit (F := D.F0) s)
    (ψP D (hfin2 (c := c)) s) (hψ1 s) (hψ2 s)

theorem ρW_wO (s : D.PV) : ρW W s.1 (wO W s) = unit (F := D.F0) s :=
  ρ_wG (W.N s.1).lift _ _ _ (hψ1 s) (hψ2 s)

theorem wO_eO (s : D.PV) : (W.N s.1).MM.act (wO W s) (eO P s) = wO W s := by
  have := act_wG_e (W.N s.1).lift (eO P s) (eO_idem s) (unit (F := D.F0) s) 1
  rwa [mul_one, (W.N s.1).MM.act_one] at this

/-! ### Yoneda at projective labels -/

theorem rs_unit_apply {s : D.PV} {X : V} (f : obj c s.1 ⟶ obj c X) :
    rs D f (unit (F := D.F0) s) s = f :=
  unit_comp_apply (F := D.F0) s f

theorem rs_unit_eq_act {s : D.PV} {X : V} (m : Rep D.F0 (meshFam Q c X)) :
    rs D (m s) (unit (F := D.F0) s) = (gmodEv D (hfin2 (c := c)) X).act m (eP D s) := by
  funext y
  change idTo (F := D.F0) y s ≫ m s = (idem (F := D.F0) s • m) y
  rw [idem_smul_rep]
  by_cases h : y = s
  · subst h; rw [if_pos rfl, idTo_self, Category.id_comp]
  · rw [if_neg h, idTo_ne h, Limits.zero_comp]

end Corner

/-! ### Bijectivity of the corner evaluation -/

section CornerEval

variable {u : MeshCoefficients (ZMod 4) Q}
  (hmesh : ∀ x : Q.nonprojective, ∑ a : Σ y : V, y ⟶ x.1,
    ((u x a.1 a.2 : (ZMod 4)ˣ) : ZMod 4) • (W.φ a.2 ∘ₗ W.φ (Q.mate x a.1 a.2)) = 0)
  (hred : ∀ x y a, Z4.red (u x y a : ZMod 4) = (c x y a : 𝔽₂))

theorem ρW_evO_wO {s : D.PV} {X : V}
    (F : LinearPaths.obj (k := ZMod 4) s.1 ⟶ LinearPaths.obj (k := ZMod 4) X) :
    ρW W X (evO W F (wO W s)) = rs D (imgk (LinearPaths.redP Z4.red F)) (unit (F := D.F0) s) := by
  rw [ρW_evO, ρW_wO]

theorem evO_wO_eO {s : D.PV} {X : V}
    (F : LinearPaths.obj (k := ZMod 4) s.1 ⟶ LinearPaths.obj (k := ZMod 4) X) :
    (W.N X).MM.act (evO W F (wO W s)) (eO P s) = evO W F (wO W s) := by
  rw [← evO_act, wO_eO]

set_option maxHeartbeats 1000000 in
theorem corner_step_surj (s p : D.PV) (n : NW W p.1)
    (hn : (W.N p.1).MM.act n (eO P s) = n) :
    ∃ (F : LinearPaths.obj (k := ZMod 4) s.1 ⟶ LinearPaths.obj (k := ZMod 4) p.1) (n₁ : NW W p.1),
      (W.N p.1).MM.act n₁ (eO P s) = n₁ ∧ n = evO W F (wO W s) + (2 : ZMod 4) • n₁ := by
  obtain ⟨G, hG⟩ := RelationCategory.functor_map_surjective (k := 𝔽₂) (meshRelations c)
    ((ρW W p.1 n) s : obj c s.1 ⟶ obj c p.1)
  obtain ⟨F, hFG⟩ := LinearPaths.exists_lift' Z4.red_surjective G
  have h0 : ρW W p.1 (n - evO W F (wO W s)) = 0 := by
    rw [map_sub, ρW_evO_wO, hFG]
    simp only [imgk, hG]
    rw [rs_unit_eq_act, ← πO_eO (T := T) s, ← (W.N p.1).lift.act, hn,
      sub_self]
  obtain ⟨n₁, hn₁⟩ := (W.N p.1).lift.ker _ h0
  refine ⟨F, (W.N p.1).MM.act n₁ (eO P s), by rw [(W.N p.1).MM.act_mul, eO_idem], ?_⟩
  rw [← GMod.act_smul, ← hn₁, map_sub, LinearMap.sub_apply, hn, evO_wO_eO, add_sub_cancel]

/-- **The corner evaluation is surjective.** -/
theorem corner_surj (s p : D.PV) (n : NW W p.1) (hn : (W.N p.1).MM.act n (eO P s) = n) :
    ∃ F : LinearPaths.obj (k := ZMod 4) s.1 ⟶ LinearPaths.obj (k := ZMod 4) p.1,
      evO W F (wO W s) = n := by
  obtain ⟨F, n₁, h₁, rfl⟩ := corner_step_surj W s p n hn
  obtain ⟨F₁, n₂, -, rfl⟩ := corner_step_surj W s p n₁ h₁
  refine ⟨F + (2 : ZMod 4) • F₁, ?_⟩
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_add, four_smul',
    add_zero]

include hred in
theorem corner_step_inj (s p : D.PV)
    {F : LinearPaths.obj (k := ZMod 4) s.1 ⟶ LinearPaths.obj (k := ZMod 4) p.1}
    (hFw : ρW W p.1 (evO W F (wO W s)) = 0) :
    ∃ G ∈ (CategoricalIdeal.HomIdeal.linearSpan (ZMod 4) (meshRelations u)).hom
      (LinearPaths.obj s.1) (LinearPaths.obj p.1), ∃ H, F = G + (2 : ZMod 4) • H := by
  rw [ρW_evO_wO] at hFw
  have h1 : imgk (c := c) (LinearPaths.redP Z4.red F) = 0 := by
    rw [← rs_unit_apply (s := s) (imgk (LinearPaths.redP Z4.red F)), hFw]; rfl
  rw [imgk, RelationCategory.functor_map_eq_zero_iff] at h1
  obtain ⟨G, hG, hGF⟩ := exists_lift_ideal hred Z4.red_surjective h1
  obtain ⟨H, hH⟩ := eq_two_smul_of_redP (Φ := F - G) (by rw [map_sub, hGF, sub_self])
  exact ⟨G, hG, H, by rw [← hH, add_sub_cancel]⟩

include hmesh hred in
/-- **The corner evaluation is injective modulo the mesh ideal.** -/
theorem corner_inj (s p : D.PV)
    (F : LinearPaths.obj (k := ZMod 4) s.1 ⟶ LinearPaths.obj (k := ZMod 4) p.1)
    (hFw : evO W F (wO W s) = 0) :
    F ∈ (CategoricalIdeal.HomIdeal.linearSpan (ZMod 4) (meshRelations u)).hom
      (LinearPaths.obj s.1) (LinearPaths.obj p.1) := by
  obtain ⟨G, hG, H, rfl⟩ := corner_step_inj W hred s p (F := F) (by rw [hFw, map_zero])
  have hG0 : evO W G = 0 := evL_ideal hmesh hG
  have hH : ρW W p.1 (evO W H (wO W s)) = 0 := by
    refine (W.N p.1).lift.ann _ ?_
    rw [← LinearMap.smul_apply, ← map_smul, ← zero_add (evO W ((2 : ZMod 4) • H)), ← hG0,
      ← map_add, hFw]
  obtain ⟨G', hG', H', rfl⟩ := corner_step_inj W hred s p hH
  rw [smul_add, smul_smul, Z4.four_eq_zero, zero_smul, add_zero, two_smul]
  exact add_mem hG (add_mem hG' hG')

end CornerEval

/-! ### Lemma 10.2 for twice a cocycle -/

section Pieces

variable {q : ℕ} {μ : (Alg D.F0)ᵐᵒᵖ →ₗ[𝔽₂] (Alg D.F0)ᵐᵒᵖ →ₗ[𝔽₂] (Alg D.F0)ᵐᵒᵖ}
  {μO : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4) →ₗ[ZMod 4]
    P.Lin (ZMod 4)}
  (hμO : ∀ a b x, πO T x = μ (πO T a) (πO T b) →
    μO a b = (2 : ZMod 4) • x)
  (Ld : LiftData D (hfin2 (c := c)) q μ)

/-- The lifted actions over `𝒪`, twice those of `μ`. -/
abbrev LfO (X : V) : ActLift μO (q : ℤ) (W.N X).MM :=
  actLiftTw (W.N X).lift (isRed_πO T) hμO (Ld.L X)

variable {u : MeshCoefficients (ZMod 4) Q}
  (hmesh : ∀ x : Q.nonprojective, ∑ a : Σ y : V, y ⟶ x.1,
    ((u x a.1 a.2 : (ZMod 4)ˣ) : ZMod 4) • (W.φ a.2 ∘ₗ W.φ (Q.mate x a.1 a.2)) = 0)
  (hred : ∀ x y a, Z4.red (u x y a : ZMod 4) = (c x y a : 𝔽₂))
  (f : ArrowFamily u)

/-- The arrow corrections: twice those of `μ`, changed by the evaluation of `f`. -/
abbrev gO {y x : V} (a : y ⟶ x) : NW W y →ₗ[ZMod 4] NW W x :=
  twMap (W.N y).lift (W.N x).lift (Ld.g a) - evE W u (f ⟨y, x, a⟩)

set_option maxHeartbeats 1000000 in
include hmesh in
theorem lift_gO {y x : V} (a : y ⟶ x) :
    IsLiftHom (LfO W hμO Ld y) (LfO W hμO Ld x) (W.φ a) (gO W Ld f a) := by
  have h1 := isLiftHom_tw (W.N y).lift (W.N x).lift (isRed_πO T) hμO (Ld.L y) (Ld.L x)
    (Ld.lift a) (W.φ_act a) (W.φ_red a)
  have h2 : IsLiftHom (LfO W hμO Ld y) (LfO W hμO Ld x) 0 (-evE W u (f ⟨y, x, a⟩)) :=
    (isLiftHom_zero_iff _ _ _).2 fun m b ↦ by
      rw [LinearMap.neg_apply, LinearMap.neg_apply, evE_act W hmesh, GMod.act_neg]
  have := h1.add h2
  rwa [add_zero, ← sub_eq_add_neg] at this

include hmesh hred in
/-- **The first-order mesh errors vanish** once `f` removes twice the mesh errors of `μ`. -/
theorem zmesh_gO {G : MeshFamily u} (hfD : meshDerivative u f = (2 : ZMod 4) • G)
    (hGred : ∀ x, redE Z4.red u c (G x) = zhat Ld x) (x : Q.nonprojective) :
    ∑ a : Σ y : V, y ⟶ x.1, ((u x a.1 a.2 : (ZMod 4)ˣ) : ZMod 4) •
      (W.φ a.2 ∘ₗ gO W Ld f (Q.mate x a.1 a.2) + gO W Ld f a.2 ∘ₗ W.φ (Q.mate x a.1 a.2)) = 0 := by
  have e1 : ∑ a : Σ y : V, y ⟶ x.1, ((u x a.1 a.2 : (ZMod 4)ˣ) : ZMod 4) •
      (W.φ a.2 ∘ₗ gO W Ld f (Q.mate x a.1 a.2) + gO W Ld f a.2 ∘ₗ W.φ (Q.mate x a.1 a.2)) =
      ∑ a : Σ y : V, y ⟶ x.1, ((u x a.1 a.2 : (ZMod 4)ˣ) : ZMod 4) •
        (W.φ a.2 ∘ₗ twMap (W.N (Q.tau x).1).lift (W.N a.1).lift (Ld.g (Q.mate x a.1 a.2)) +
          twMap (W.N a.1).lift (W.N x.1).lift (Ld.g a.2) ∘ₗ W.φ (Q.mate x a.1 a.2)) -
      ∑ a : Σ y : V, y ⟶ x.1, ((u x a.1 a.2 : (ZMod 4)ˣ) : ZMod 4) •
        (W.φ a.2 ∘ₗ evE W u (f ⟨(Q.tau x).1, a.1, Q.mate x a.1 a.2⟩) +
          evE W u (f ⟨a.1, x.1, a.2⟩) ∘ₗ W.φ (Q.mate x a.1 a.2)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [gO, LinearMap.comp_sub, LinearMap.sub_comp, smul_add, smul_sub]
    abel
  have e2 : ∑ a : Σ y : V, y ⟶ x.1, ((u x a.1 a.2 : (ZMod 4)ˣ) : ZMod 4) •
      (W.φ a.2 ∘ₗ twMap (W.N (Q.tau x).1).lift (W.N a.1).lift (Ld.g (Q.mate x a.1 a.2)) +
        twMap (W.N a.1).lift (W.N x.1).lift (Ld.g a.2) ∘ₗ W.φ (Q.mate x a.1 a.2)) =
      twMap (W.N (Q.tau x).1).lift (W.N x.1).lift (zE Ld x) := by
    rw [zE, twMap_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [comp_twMap (W.N (Q.tau x).1).lift (W.N a.1).lift (W.N x.1).lift (W.φ_red a.2),
      twMap_comp (W.N (Q.tau x).1).lift (W.N a.1).lift (W.N x.1).lift (W.φ_red _),
      ← twMap_add, ← twMap_red_smul, hred]
  rw [e1, e2, ← evE_meshDerivative W hmesh f x, hfD, Pi.smul_apply, evE_smul W hmesh, sub_eq_zero]
  refine LinearMap.ext fun n ↦ ?_
  rw [twMap_apply, LinearMap.smul_apply, ← (W.N x.1).lift.tw_ρ, ρW_evE W hmesh hred, hGred,
    zhat_spec']

include hμO in
theorem reg_O (J : InjData D) (h1 : DegOne D) (hμ : IsHCocycle μ)
    (hdeg : HDeg (galgA0 D (hfin2 (c := c))) μ (q : ℤ))
    (hLd : ∀ X, Ld.L X = stdL J h1 hμ hdeg X) (p : D.PV) (n : NW W p.1)
    (b : P.Lin (ZMod 4)) :
    (LfO W hμO Ld p.1).act n b = (W.N p.1).MM.act (wO W p) (μO (ψO W p n) b) := by
  have hπ := isRed_πO T
  rw [actLiftTw_act, hLd, stdL_act,
    hμO (ψO W p n) b _ (liftR_spec hπ (μ (πO T (ψO W p n)) (πO T b))),
    map_smul, ← (W.N p.1).lift.tw_ρ,
    ρ_act_wG (W.N p.1).lift (eO P p) (unit (F := D.F0) p) (ψP D (hfin2 (c := c)) p)
      (hψ1 p) (hψ2 p), liftR_spec, π_ψG]

end Pieces

section Main

variable (J : InjData D) (h1 : DegOne D) {S : RowSet Q} (hspan : CokerSpan c S)
  (htwo : TwoRows.{0} Q S)
  {q : ℕ} (hq : 1 ≤ q) {μ : (Alg D.F0)ᵐᵒᵖ →ₗ[𝔽₂] (Alg D.F0)ᵐᵒᵖ →ₗ[𝔽₂] (Alg D.F0)ᵐᵒᵖ}
  (hμ : IsHCocycle μ) (hdeg : HDeg (galgA0 D (hfin2 (c := c))) μ (q : ℤ))
  {μO : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4) →ₗ[ZMod 4]
    P.Lin (ZMod 4)}
  (hμO : ∀ a b x, πO T x = μ (πO T a) (πO T b) →
    μO a b = (2 : ZMod 4) • x)

include J h1 hspan htwo hq hμ hdeg hμO in
/-- **Lemma 10.2 and Lemma B.2 for twice a cocycle** (`integral-deformations.tex:122–210`):
for a cocycle `μ` of `A⁽²⁾` of positive degree, the cocycle `2μ` of `𝒪P` is a coboundary. -/
theorem exists_hcobdry_twice (hμOc : IsHCocycle μO) : ∃ h, μO = hcobdry h := by
  classical
  have : Fintype Q.nonprojective := Fintype.ofFinite _
  obtain ⟨W⟩ := exists_wData (T := T) J h1
  obtain ⟨u, hred, hmesh⟩ := exists_meshUnits W
  obtain ⟨Ld, hLd⟩ := exists_liftData J h1 hμ hdeg
  -- Lemma B.2: twice the mesh errors are a derivative
  choose G hGdeg hGred using fun x : Q.nonprojective ↦
    exists_lift_degreePart (n := q + 1 + 1) hred Z4.red_surjective (zhat_mem Ld x)
  have hB2 := two_smul_mem_imageD hred hspan htwo (m := q + 1) (by omega) (g := G) hGdeg
  have hB2' : ∃ f ∈ familiesDeg u (q + 1), meshDerivativeₗ u f = (2 : ZMod 4) • G := hB2
  obtain ⟨f, -, hfD⟩ := hB2'
  have H : CornerDeriv.Hyp u (NW W) (fun X ↦ (W.N X).MM) (LfO W hμO Ld) W.φ (gO W Ld f)
      (fun p : D.PV ↦ p.1) (eO P) (wO W) (ψO W) :=
    { e_idem := eO_idem
      e_sum := sum_eO
      φ_act := W.φ_act
      lift := lift_gO W hμO Ld hmesh f
      mesh := hmesh
      zmesh := zmesh_gO W Ld hmesh hred f hfD hGred
      w_e := wO_eO W
      ψ_w := fun p b ↦ ψG_w _ _ _ _ _ _ _ _ b
      w_ψ := fun p n ↦ w_ψG _ _ _ _ _ _ _ _ n
      reg := reg_O W hμO Ld J h1 hμ hdeg hLd
      surj := corner_surj W
      inj := corner_inj W hmesh hred }
  exact CornerDeriv.eq_hcobdry H hμOc

end Main

end MeshWalk

end MultiplicativeBasisDeformations
