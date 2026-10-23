module

public import MultiplicativeBasisDeformations.Foundations.RayDegree
public import MultiplicativeBasisDeformations.Foundations.FilteredA
public import MultiplicativeBasisDeformations.Foundations.A0Graded

/-!
# Lemma 3.7 for the categorical filtration

`projective-rays.tex` (`lem:ray-degree`): "Write `F^nA(x,y) = J^n(P_y,P_x)` […] Every
space `A₀(x,y)_d` of degree `d` has dimension at most one, and initial forms give a bijection
between the nonzero rays of `A` and the nonzero spaces `A₀(x,y)_d`. If the endpoint
subbimodules satisfy `U_{r'} ⊊ U_r`, then `deg_J(r') > deg_J(r)`."

The proof only uses that the filtration is multiplicative, starts at `A`, ends at zero, and
contains the radical in degree one ("endpoint radicals belong to `J`"). We prove the lemma for
every positive filtered deformation `P` of a graded algebra `Λ` with this property
(`PosFiltration.RadOne`): the corner layers have dimension at most one
(`finrank_corner_le`), elements of one degree lie in one ray (`ray_eq_of_degree`), a smaller
subbimodule has a larger degree (`degree_lt_of_lt`), and the initial form `σ_d` maps the
corner `F^dA(x,y)` onto the corner `Λ(x,y)_d` of `Λ` cut out by the idempotents
`σ₀(e_x)`, with kernel `F^{d+1}A(x,y)` (`σ_piece_surj`, `finrank_piece_le`).

For `A` itself, `posFiltA` is the filtration `J^n` of the source (`FilteredA.lean`), and the
radical lies in `J¹` because the degree-zero part of `A₀` has no nonzero nilpotents
(`lenA0_noNil`). This gives the literal Lemma 3.7 (`IndSkeleton.rayDegree_J`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace PosFiltration

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  {B : Type w} [Ring B] [Algebra k B] (P : PosFiltration G B)

/-- The radical lies in degree one. -/
def RadOne : Prop := algebraRadical k B ≤ P.F 1

theorem σ_zero_mul (a b : B) : P.σ 0 (a * b) = P.σ 0 a * P.σ 0 b := by
  simpa using P.σ_mul 0 0 a b (P.mem_zero a) (P.mem_zero b)

theorem σ_zero_pow_succ (a : B) (n : ℕ) : P.σ 0 (a ^ (n + 1)) = P.σ 0 a ^ (n + 1) := by
  induction n with
  | zero => rw [pow_one, pow_one]
  | succ n ih => rw [pow_succ, P.σ_zero_mul, ih, ← pow_succ]

/-- **The radical lies in `F¹`** when the degree-zero part of `Λ` has no nonzero nilpotents. -/
theorem radOne_of [FiniteDimensional k B] (h : ∀ z, G.IsHom 0 z → IsNilpotent z → z = 0) :
    P.RadOne := by
  intro a ha
  obtain ⟨K, hK⟩ := algebraRadical_pow_eq_bot (k := k) (A := B)
  have hpow : a ^ (K + 1) = 0 := by
    have : a ^ (K + 1) ∈ algebraRadical k B ^ (K + 1) := Submodule.pow_mem_pow _ ha _
    rw [pow_succ (algebraRadical k B), hK, Submodule.bot_mul] at this
    exact (Submodule.mem_bot _).1 this
  have h0 : P.σ 0 a = 0 := h _ (P.σ_hom 0 a) ⟨K + 1, by rw [← P.σ_zero_pow_succ, hpow, map_zero]⟩
  simpa using (P.σ_ker 0 a (P.mem_zero a)).1 h0

theorem rad_mul_F (hP : P.RadOne) (d : ℕ) {a z : B} (ha : a ∈ algebraRadical k B)
    (hz : z ∈ P.F d) : a * z ∈ P.F (d + 1) := by
  have := P.F_mul 1 d a z (hP ha) hz
  rwa [Nat.add_comm] at this

theorem F_mul_rad (hP : P.RadOne) (d : ℕ) {a z : B} (ha : a ∈ algebraRadical k B)
    (hz : z ∈ P.F d) : z * a ∈ P.F (d + 1) :=
  P.F_mul d 1 z a hz (hP ha)

variable [IsAlgClosed k] [FiniteDimensional k B] (F : PrimitiveIdempotents B)

theorem isEndpoint_F (x y : Fin F.m) (d : ℕ) :
    F.IsEndpointSubbimodule x y (F.corner (k := k) x y ⊓ P.F d) :=
  ⟨inf_le_left, fun _ ha _ hn ↦ ⟨F.corner_mul_corner ha hn.1, P.mul_mem_left _ hn.2⟩,
    fun _ hb _ hn ↦ ⟨F.corner_mul_corner hn.1 hb, P.mul_mem_right _ hn.2⟩⟩

/-- `R(g) ⊆ F^{d+1}` for `g ∈ F^d`: endpoint radicals belong to `F¹`. -/
theorem endpointRadical_le_F (hP : P.RadOne) {x y : Fin F.m} {g : B}
    (hg : g ∈ F.corner (k := k) x y) {d : ℕ} (hgd : g ∈ P.F d) :
    F.endpointRadical (k := k) x y g ≤ F.corner (k := k) x y ⊓ P.F (d + 1) := by
  refine Submodule.span_le.2 ?_
  rintro _ (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
  · exact ⟨F.corner_mul_corner (F.corner_mul_corner ha.1 hg) hb,
      P.mul_mem_right b (P.rad_mul_F hP d ha.2 hgd)⟩
  · exact ⟨F.corner_mul_corner (F.corner_mul_corner ha hg) hb.1,
      P.F_mul_rad hP d hb.2 (P.mul_mem_left a hgd)⟩

/-- **Each layer of the filtration of a corner has dimension at most one.** -/
theorem finrank_corner_le (hP : P.RadOne) (hA : IsRepresentationFinite k B) (x y : Fin F.m)
    (d : ℕ) :
    Module.finrank k (F.corner (k := k) x y ⊓ P.F d : Submodule k B) ≤
      Module.finrank k (F.corner (k := k) x y ⊓ P.F (d + 1) : Submodule k B) + 1 := by
  set N := F.corner (k := k) x y ⊓ P.F d
  by_cases hN0 : N = ⊥
  · rw [hN0, finrank_bot]; omega
  obtain ⟨g, hgN, -, hNU⟩ := F.exists_cyclic hA (P.isEndpoint_F F x y d) hN0
  have hR := P.endpointRadical_le_F F hP hgN.1 hgN.2
  have hle : N ≤ (k ∙ g) ⊔ (F.corner (k := k) x y ⊓ P.F (d + 1)) := by
    change F.corner (k := k) x y ⊓ P.F d ≤ _
    rw [hNU, F.endpointSpan_eq hgN.1]
    exact sup_le_sup_left hR _
  calc Module.finrank k N ≤ Module.finrank k
        ((k ∙ g) ⊔ (F.corner (k := k) x y ⊓ P.F (d + 1)) : Submodule k B) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank k (k ∙ g) + Module.finrank k
        (F.corner (k := k) x y ⊓ P.F (d + 1) : Submodule k B) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ 1 + _ := by
        gcongr
        exact (finrank_span_le_card ({g} : Set B)).trans (by simp)
    _ = _ := add_comm _ _

/-- **Elements of the same degree lie in the same ray.** -/
theorem ray_eq_of_degree (hP : P.RadOne) (hA : IsRepresentationFinite k B) {x y : Fin F.m}
    {f g : B} (hf : f ∈ F.corner (k := k) x y) (hg : g ∈ F.corner (k := k) x y) {d : ℕ}
    (hfd : f ∈ P.F d) (hfd' : f ∉ P.F (d + 1)) (hgd : g ∈ P.F d) (hgd' : g ∉ P.F (d + 1)) :
    F.ray (k := k) x y f = F.ray (k := k) x y g := by
  set N := F.corner (k := k) x y ⊓ P.F d
  have hN0 : N ≠ ⊥ := fun h ↦ hfd' (by
    have : f ∈ N := ⟨hf, hfd⟩
    rw [h, Submodule.mem_bot] at this
    rw [this]; exact Submodule.zero_mem _)
  obtain ⟨h, hhN, hh0, hNU⟩ := F.exists_cyclic hA (P.isEndpoint_F F x y d) hN0
  have hR := P.endpointRadical_le_F F hP hhN.1 hhN.2
  have key : ∀ z, z ∈ F.corner (k := k) x y → z ∈ P.F d → z ∉ P.F (d + 1) →
      F.ray (k := k) x y z = F.ray (k := k) x y h := fun z hz hzd hzd' ↦
    F.ray_eq_of_mem hhN.1 ((F.mem_ray_iff hA hhN.1 hh0 z).2
      ⟨hNU ▸ ⟨hz, hzd⟩, fun hzR ↦ hzd' (hR hzR).2⟩)
  rw [key f hf hfd hfd', key g hg hgd hgd']

/-- **A strictly smaller subbimodule has a strictly larger degree.** -/
theorem degree_lt_of_lt (hP : P.RadOne) (hA : IsRepresentationFinite k B) {x y : Fin F.m}
    {f g : B} (hf : f ∈ F.corner (k := k) x y) (hg : g ∈ F.corner (k := k) x y)
    (hlt : F.endpointSpan (k := k) x y g < F.endpointSpan (k := k) x y f) {d d' : ℕ}
    (hfd : f ∈ P.F d) (hgd' : g ∈ P.F d') (hgd'' : g ∉ P.F (d' + 1)) : d < d' := by
  have hfg : f ∉ F.endpointSpan (k := k) x y g := fun h ↦
    (not_le_of_gt hlt) (F.endpointSpan_le (F.isEndpoint_endpointSpan hg) h)
  have hgR := F.le_endpointRadical hA hf (F.isEndpoint_endpointSpan hg) hlt.le hfg
    (F.mem_endpointSpan_self hg)
  have hg1 := (P.endpointRadical_le_F F hP hf hfd hgR).2
  by_contra hdd
  exact hgd'' (P.F_anti (by omega) hg1)

/-- Every nonzero element has a degree. -/
theorem exists_degree {f : B} (hf0 : f ≠ 0) : ∃ d, f ∈ P.F d ∧ f ∉ P.F (d + 1) := by
  classical
  have hex : ∃ n, f ∉ P.F n := ⟨P.M, fun h ↦ hf0 (by rwa [P.F_M, Submodule.mem_bot] at h)⟩
  have hn0 : Nat.find hex ≠ 0 := fun h ↦ (Nat.find_spec hex) (h ▸ P.mem_zero f)
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨d, ?_, by have := Nat.find_spec hex; rwa [hd] at this⟩
  by_contra h
  exact absurd (Nat.find_min' hex h) (by omega)

theorem mem_F_of_ray {x y : Fin F.m} {f g : B} (hg : g ∈ F.ray (k := k) x y f) {d : ℕ}
    (hf : f ∈ P.F d) : g ∈ P.F d := by
  obtain ⟨u, w, -, -, rfl⟩ := hg
  exact P.mul_mem_right _ (P.mul_mem_left _ hf)

/-! ### The initial forms on corners -/

/-- The corner `Λ(x, y)_d`: degree-`d` elements of `σ₀(e_x) Λ σ₀(e_y)`. -/
def piece (x y : Fin F.m) (d : ℕ) : Submodule k Λ where
  carrier := {z | P.σ 0 (F.e x) * z * P.σ 0 (F.e y) = z ∧ G.IsHom d z}
  add_mem' ha hb := ⟨by rw [mul_add, add_mul, ha.1, hb.1], by
    show G.proj d _ = _; rw [map_add, ha.2, hb.2]⟩
  zero_mem' := ⟨by simp, by show G.proj d 0 = 0; rw [map_zero]⟩
  smul_mem' t z hz := ⟨by rw [mul_smul_comm, smul_mul_assoc, hz.1], by
    show G.proj d _ = _; rw [map_smul, hz.2]⟩

theorem σ_corner_mem {x y : Fin F.m} {d : ℕ} {a : B} (ha : a ∈ F.corner (k := k) x y)
    (had : a ∈ P.F d) : P.σ d a ∈ P.piece F x y d := by
  refine ⟨?_, P.σ_hom d a⟩
  have e : F.e x * a * F.e y = a := (PrimitiveIdempotents.mem_corner_iff' F).1 ha
  have h1 := P.σ_mul 0 d (F.e x) a (P.mem_zero _) had
  have h2 := P.σ_mul (0 + d) 0 (F.e x * a) (F.e y) (P.F_mul 0 d _ _ (P.mem_zero _) had)
    (P.mem_zero _)
  simp only [Nat.zero_add, Nat.add_zero] at h1 h2
  rw [← h1, ← h2, e]

/-- **Initial forms map the corner layers onto the corner pieces.** -/
theorem σ_piece_surj {x y : Fin F.m} {d : ℕ} {z : Λ} (hz : z ∈ P.piece F x y d) :
    ∃ a ∈ F.corner (k := k) x y ⊓ P.F d, P.σ d a = z := by
  obtain ⟨a, had, rfl⟩ := P.σ_surj d z hz.2
  refine ⟨F.e x * a * F.e y, ⟨F.eAe_mem_corner x y a, P.mul_mem_right _ (P.mul_mem_left _ had)⟩,
    ?_⟩
  have h1 := P.σ_mul 0 d (F.e x) a (P.mem_zero _) had
  have h2 := P.σ_mul (0 + d) 0 (F.e x * a) (F.e y) (P.F_mul 0 d _ _ (P.mem_zero _) had)
    (P.mem_zero _)
  simp only [Nat.zero_add, Nat.add_zero] at h1 h2
  rw [h2, h1, hz.1]

/-- The initial form on a corner layer. -/
def σCorner (x y : Fin F.m) (d : ℕ) :
    (F.corner (k := k) x y ⊓ P.F d : Submodule k B) →ₗ[k] P.piece F x y d where
  toFun a := ⟨P.σ d a, P.σ_corner_mem F a.2.1 a.2.2⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' t a := Subtype.ext (map_smul _ _ _)

theorem σCorner_surjective (x y : Fin F.m) (d : ℕ) : Function.Surjective (P.σCorner F x y d) := by
  rintro ⟨z, hz⟩
  obtain ⟨a, ha, rfl⟩ := P.σ_piece_surj F hz
  exact ⟨⟨a, ha⟩, rfl⟩

theorem σCorner_ker (x y : Fin F.m) (d : ℕ) (a : (F.corner (k := k) x y ⊓ P.F d : Submodule k B)) :
    P.σCorner F x y d a = 0 ↔ (a : B) ∈ P.F (d + 1) := by
  rw [← P.σ_ker d a a.2.2]
  exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩

/-- `dim Λ(x,y)_d = dim F^dA(x,y) - dim F^{d+1}A(x,y)`. -/
theorem finrank_piece (x y : Fin F.m) (d : ℕ) :
    Module.finrank k (P.piece F x y d) + Module.finrank k (F.corner (k := k) x y ⊓ P.F (d + 1) :
      Submodule k B) = Module.finrank k (F.corner (k := k) x y ⊓ P.F d : Submodule k B) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (P.σCorner F x y d)
  rw [LinearMap.range_eq_top.2 (P.σCorner_surjective F x y d), finrank_top] at hrn
  rw [← hrn]
  congr 1
  refine LinearEquiv.finrank_eq
    { toFun := fun a ↦ ⟨⟨a.1, a.2.1, P.F_succ_le d a.2.2⟩, by
        rw [LinearMap.mem_ker, P.σCorner_ker]; exact a.2.2⟩
      invFun := fun a ↦ ⟨a.1.1, a.1.2.1, (P.σCorner_ker F x y d a.1).1 a.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- **Lemma 3.7, first assertion**: every piece `Λ(x,y)_d` has dimension at most one. -/
theorem finrank_piece_le (hP : P.RadOne) (hA : IsRepresentationFinite k B) (x y : Fin F.m)
    (d : ℕ) : Module.finrank k (P.piece F x y d) ≤ 1 := by
  have h1 := P.finrank_piece F x y d
  have h2 := P.finrank_corner_le F hP hA x y d
  omega

/-- **Lemma 3.7, the bijection**: a nonzero `f` of the corner of degree `d` has nonzero initial
form, which spans `Λ(x,y)_d`; two nonzero elements of a corner have the same ray iff they have
the same degree, and every nonzero piece is the initial form of a nonzero element. -/
theorem rayDegree (hP : P.RadOne) (hA : IsRepresentationFinite k B) (x y : Fin F.m) :
    (∀ d, Module.finrank k (P.piece F x y d) ≤ 1) ∧
    (∀ (f : B) (d : ℕ), f ∈ F.corner (k := k) x y → f ∈ P.F d → f ∉ P.F (d + 1) →
      P.σ d f ≠ 0 ∧ P.piece F x y d = k ∙ P.σ d f) ∧
    (∀ (f g : B) (d d' : ℕ), f ∈ F.corner (k := k) x y → g ∈ F.corner (k := k) x y →
      f ∈ P.F d → f ∉ P.F (d + 1) → g ∈ P.F d' → g ∉ P.F (d' + 1) →
      (F.ray (k := k) x y f = F.ray (k := k) x y g ↔ d = d')) ∧
    (∀ d, P.piece F x y d ≠ ⊥ →
      ∃ f ∈ F.corner (k := k) x y, f ∈ P.F d ∧ f ∉ P.F (d + 1)) ∧
    (∀ (f g : B), f ∈ F.corner (k := k) x y → g ∈ F.corner (k := k) x y →
      F.endpointSpan (k := k) x y g < F.endpointSpan (k := k) x y f →
      ∀ d d', f ∈ P.F d → g ∈ P.F d' → g ∉ P.F (d' + 1) → d < d') := by
  refine ⟨P.finrank_piece_le F hP hA x y, fun f d hf hfd hfd' ↦ ?_, fun f g d d' hf hg hfd hfd'
    hgd hgd' ↦ ?_, fun d hd ↦ ?_, fun f g hf hg hlt d d' hfd hgd hgd' ↦
    P.degree_lt_of_lt F hP hA hf hg hlt hfd hgd hgd'⟩
  · have h0 : P.σ d f ≠ 0 := fun h ↦ hfd' ((P.σ_ker d f hfd).1 h)
    refine ⟨h0, ?_⟩
    have hmem := P.σ_corner_mem F hf hfd
    have : FiniteDimensional k (P.piece F x y d) :=
      Module.Finite.of_surjective _ (P.σCorner_surjective F x y d)
    refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
    · exact (Submodule.span_singleton_le_iff_mem _ _).2 hmem
    · rw [finrank_span_singleton h0]; exact P.finrank_piece_le F hP hA x y d
  · constructor
    · intro hr
      have h1 : g ∈ P.F d := P.mem_F_of_ray F (hr ▸ F.mem_ray_self hg) hfd
      have h2 : f ∈ P.F d' := P.mem_F_of_ray F (hr.symm ▸ F.mem_ray_self hf) hgd
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hfd' (P.F_anti (by omega) h2)
      · exact hgd' (P.F_anti (by omega) h1)
    · rintro rfl; exact P.ray_eq_of_degree F hP hA hf hg hfd hfd' hgd hgd'
  · obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hd
    obtain ⟨a, ha, rfl⟩ := P.σ_piece_surj F hz
    exact ⟨a, ha.1, ha.2, fun h ↦ hz0 ((P.σ_ker d a ha.2).2 h)⟩

end PosFiltration

/-! ### The degree-zero part of `A₀` -/

namespace MeshWalk

open ScalarMeshCategory CatAlg

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))

/-- A diagonal scalar element `∑ t_p e_p` of `A₀`. -/
def IsDiag (z : (Alg D.F0)ᵐᵒᵖ) (t : D.PV → k) : Prop :=
  ∀ p q, z.unop p q = t p • idTo (F := D.F0) p q

theorem isDiag_mul {z w : (Alg D.F0)ᵐᵒᵖ} {t s : D.PV → k} (hz : IsDiag D z t) (hw : IsDiag D w s) :
    IsDiag D (z * w) (s * t) := by
  intro p r
  rw [MulOpposite.unop_mul, mul_apply, Finset.sum_eq_single p]
  · rw [hw p p, hz p r, idTo_self, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
      smul_smul, Pi.mul_apply]
  · intro q _ hq; rw [hw p q, idTo_ne (Ne.symm hq), smul_zero, Limits.zero_comp]
  · intro h; exact absurd (Finset.mem_univ p) h

theorem isDiag_pow {z : (Alg D.F0)ᵐᵒᵖ} {t : D.PV → k} (hz : IsDiag D z t) (n : ℕ) :
    IsDiag D (z ^ (n + 1)) (t ^ (n + 1)) := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
      have := isDiag_mul D ih hz
      rwa [← pow_succ', ← pow_succ] at this

include hfin in
theorem isDiag_of_isHom {z : (Alg D.F0)ᵐᵒᵖ} (hz : (lenA0 D hfin).IsHom 0 z) :
    ∃ t, IsDiag D z t := by
  classical
  have hmem : ∀ p q, z.unop p q ∈ degreePart c 0 p.1 q.1 := by
    intro p q
    have := congrArg (fun w : (Alg D.F0)ᵐᵒᵖ ↦ w.unop p q) hz
    change degProj c 0 p.1 q.1 (z.unop p q) = z.unop p q at this
    rw [← this]
    exact degProj_mem c 0 _
  choose t ht using fun p : D.PV ↦ degreePart_zero_eq c (hmem p p)
  refine ⟨t, fun p q ↦ ?_⟩
  by_cases h : p = q
  · subst h; rw [idTo_self]; exact ht p
  · rw [idTo_ne h, smul_zero]
    exact degreePart_zero_ne (fun h' ↦ h (Subtype.ext h')) (hmem p q)

include hfin in
/-- **The degree-zero part of `A₀` has no nonzero nilpotents.** -/
theorem lenA0_noNil (z : (Alg D.F0)ᵐᵒᵖ) (hz : (lenA0 D hfin).IsHom 0 z) (hn : IsNilpotent z) :
    z = 0 := by
  obtain ⟨t, ht⟩ := isDiag_of_isHom D hfin hz
  obtain ⟨n, hn⟩ := hn
  have ht0 : ∀ p, t p = 0 := by
    intro p
    have h1 := isDiag_pow D ht n
    have h2 : (z ^ (n + 1)).unop p p = 0 := by
      rw [pow_succ, hn, zero_mul]; rfl
    rw [h1 p p, idTo_self, Pi.pow_apply] at h2
    have h3 := (smul_eq_zero.1 h2).resolve_right (CatAlg.MeshData.id_ne_zero (L := L) p.1)
    exact pow_eq_zero_iff (n := n + 1) (by omega) |>.1 h3
  apply MulOpposite.unop_injective
  apply CatAlg.ext; intro p q
  rw [ht p q, ht0, zero_smul]; rfl

end MeshWalk

/-! ### Lemma 3.7 for `A` -/

namespace IndSkeleton

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)
  {n : ℕ} {e : Fin n → A} (he : CompleteOrthogonalIdempotents e)
  (hprim : ∀ i, IsPrimitiveIdempotent (e i))
  (hbasic : ∀ i j, (∃ x y : A, e i * x * e j = x ∧ e j * y * e i = y ∧ x * y = e i ∧
    y * x = e j) → i = j)

/-- **The radical of `A` lies in `J¹`.** -/
theorem posFiltA_radOne : (S.posFiltA b he hprim hbasic).RadOne :=
  PosFiltration.radOne_of _ (MeshWalk.lenA0_noNil (S.arMeshData b) (S.hfinA0 b))

/-- **Lemma 3.7** (`lem:ray-degree`) for the categorical filtration `F^dA(x,y) = J^d(P_y,P_x)`
(`posFiltA`): in every corner, the pieces `A₀(x,y)_d` (cut out by the initial forms of the
idempotents) have dimension at most one; a nonzero element of degree `d` has nonzero initial
form spanning `A₀(x,y)_d`; two nonzero elements have the same ray iff they have the same
degree; every nonzero piece is reached; and `U_{r'} ⊊ U_r` forces `deg_J r' > deg_J r`. -/
theorem rayDegree_J (hA : IsRepresentationFinite k A) (F : PrimitiveIdempotents A)
    (x y : Fin F.m) :
    let P := S.posFiltA b he hprim hbasic
    (∀ d, Module.finrank k (P.piece F x y d) ≤ 1) ∧
    (∀ (f : A) (d : ℕ), f ∈ F.corner (k := k) x y → f ∈ P.F d → f ∉ P.F (d + 1) →
      P.σ d f ≠ 0 ∧ P.piece F x y d = k ∙ P.σ d f) ∧
    (∀ (f g : A) (d d' : ℕ), f ∈ F.corner (k := k) x y → g ∈ F.corner (k := k) x y →
      f ∈ P.F d → f ∉ P.F (d + 1) → g ∈ P.F d' → g ∉ P.F (d' + 1) →
      (F.ray (k := k) x y f = F.ray (k := k) x y g ↔ d = d')) ∧
    (∀ d, P.piece F x y d ≠ ⊥ →
      ∃ f ∈ F.corner (k := k) x y, f ∈ P.F d ∧ f ∉ P.F (d + 1)) ∧
    (∀ (f g : A), f ∈ F.corner (k := k) x y → g ∈ F.corner (k := k) x y →
      F.endpointSpan (k := k) x y g < F.endpointSpan (k := k) x y f →
      ∀ d d', f ∈ P.F d → g ∈ P.F d' → g ∉ P.F (d' + 1) → d < d') :=
  (S.posFiltA b he hprim hbasic).rayDegree F (S.posFiltA_radOne b he hprim hbasic) hA x y

end IndSkeleton

end MultiplicativeBasisDeformations
