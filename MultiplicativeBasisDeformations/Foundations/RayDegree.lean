import MultiplicativeBasisDeformations.Foundations.RayProduct
import MultiplicativeBasisDeformations.Foundations.A0Normed

/-!
# The radical degree of a ray

Lemma 3.7 (`projective-rays.tex:216–240`). Write `F^d A(x,y)` for the radical
filtration of a corner (`F^0 = A(x,y)`, `F^d = A(x,y) ∩ (rad A)^d`). "Every
`F^dV` is one of these submodules. Since endpoint radicals belong to `J`,
`F^dV = U_i ⟹ U_{i+1} ⊆ F^{d+1}V ⊆ U_i`. Thus the filtration stays at a layer
or drops to its successor […]. The rays are `U_i ∖ U_{i+1}`."

Here: each `F^dV ≠ 0` is `U(g)` with `R(g) ⊆ F^{d+1}V` (`radFilt_cyclic`), so
the graded pieces have dimension at most one (`finrank_radFilt_le`), elements of
the same degree lie in the same ray (`ray_eq_of_degree`), and a strictly smaller
subbimodule has a strictly larger degree (`degree_lt_of_lt`). The pieces
`F^dV/F^{d+1}V` are the graded pieces `A₀(x,y)_d` of `gr_J` on projectives.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

variable (k A) in
/-- The radical filtration: `F^0 = A`, `F^d = (rad A)^d`. -/
def radFilt : ℕ → Submodule k A
  | 0 => ⊤
  | d + 1 => algebraRadicalPow k A (d + 1)

theorem radFilt_mul_left (d : ℕ) (a : A) {z : A} (hz : z ∈ radFilt k A d) :
    a * z ∈ radFilt k A d := by
  cases d with
  | zero => trivial
  | succ d => exact algebraRadicalPow_mul_left (by omega) a hz

theorem radFilt_mul_right (d : ℕ) (a : A) {z : A} (hz : z ∈ radFilt k A d) :
    z * a ∈ radFilt k A d := by
  cases d with
  | zero => trivial
  | succ d => exact algebraRadicalPow_mul_right (by omega) a hz

theorem rad_mul_radFilt (d : ℕ) {a z : A} (ha : a ∈ algebraRadical k A) (hz : z ∈ radFilt k A d) :
    a * z ∈ radFilt k A (d + 1) := by
  cases d with
  | zero =>
      change a * z ∈ algebraRadicalPow k A 1
      rw [algebraRadicalPow, pow_one]
      exact (Ring.jacobson A).mul_mem_right z ha
  | succ d =>
      change a * z ∈ algebraRadicalPow k A (d + 2)
      rw [algebraRadicalPow, pow_succ']
      exact Submodule.mul_mem_mul ha hz

theorem radFilt_mul_rad (d : ℕ) {a z : A} (ha : a ∈ algebraRadical k A) (hz : z ∈ radFilt k A d) :
    z * a ∈ radFilt k A (d + 1) := by
  cases d with
  | zero =>
      change z * a ∈ algebraRadicalPow k A 1
      rw [algebraRadicalPow, pow_one]
      exact (Ring.jacobson A).mul_mem_left z ha
  | succ d =>
      change z * a ∈ algebraRadicalPow k A (d + 2)
      rw [algebraRadicalPow, pow_succ]
      exact Submodule.mul_mem_mul hz ha

theorem radFilt_succ_le (d : ℕ) : radFilt k A (d + 1) ≤ radFilt k A d := by
  cases d with
  | zero => exact le_top
  | succ d =>
      intro z hz
      change z ∈ algebraRadicalPow k A (d + 2) at hz
      rw [algebraRadicalPow, pow_succ] at hz
      refine Submodule.mul_induction_on hz (fun a ha b _ ↦ ?_) (fun a b ha hb ↦ ?_)
      · exact algebraRadicalPow_mul_right (by omega) b ha
      · exact Submodule.add_mem _ ha hb

theorem radFilt_antitone {d d' : ℕ} (h : d ≤ d') : radFilt k A d' ≤ radFilt k A d := by
  induction d', h using Nat.le_induction with
  | base => exact le_rfl
  | succ d' _ ih => exact (radFilt_succ_le d').trans ih

namespace PrimitiveIdempotents

variable [IsAlgClosed k] [FiniteDimensional k A] (F : PrimitiveIdempotents A)

theorem radFilt_isEndpoint (x y : Fin F.m) (d : ℕ) :
    F.IsEndpointSubbimodule x y (F.corner (k := k) x y ⊓ radFilt k A d) :=
  ⟨inf_le_left, fun _ ha _ hn ↦ ⟨F.corner_mul_corner ha hn.1, radFilt_mul_left d _ hn.2⟩,
    fun _ hb _ hn ↦ ⟨F.corner_mul_corner hn.1 hb, radFilt_mul_right d _ hn.2⟩⟩

/-- `R(g) ⊆ F^{d+1}` for `g ∈ F^d`: endpoint radicals belong to `J`. -/
theorem endpointRadical_le_radFilt {x y : Fin F.m} {g : A} (hg : g ∈ F.corner (k := k) x y)
    {d : ℕ} (hgd : g ∈ radFilt k A d) :
    F.endpointRadical (k := k) x y g ≤ F.corner (k := k) x y ⊓ radFilt k A (d + 1) := by
  refine Submodule.span_le.2 ?_
  rintro _ (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
  · exact ⟨F.corner_mul_corner (F.corner_mul_corner ha.1 hg) hb,
      radFilt_mul_right _ b (rad_mul_radFilt d ha.2 hgd)⟩
  · exact ⟨F.corner_mul_corner (F.corner_mul_corner ha hg) hb.1,
      radFilt_mul_rad d hb.2 (radFilt_mul_left d a hgd)⟩

/-- **Each graded piece of the radical filtration of a corner has dimension at
most one.** -/
theorem finrank_radFilt_le (hA : IsRepresentationFinite k A) (x y : Fin F.m) (d : ℕ) :
    Module.finrank k (F.corner (k := k) x y ⊓ radFilt k A d : Submodule k A) ≤
      Module.finrank k (F.corner (k := k) x y ⊓ radFilt k A (d + 1) : Submodule k A) + 1 := by
  set N := F.corner (k := k) x y ⊓ radFilt k A d
  by_cases hN0 : N = ⊥
  · rw [hN0, finrank_bot]; omega
  obtain ⟨g, hgN, -, hNU⟩ := F.exists_cyclic hA (F.radFilt_isEndpoint x y d) hN0
  have hR := F.endpointRadical_le_radFilt hgN.1 hgN.2
  have hle : N ≤ (k ∙ g) ⊔ (F.corner (k := k) x y ⊓ radFilt k A (d + 1)) := by
    change F.corner (k := k) x y ⊓ radFilt k A d ≤ _
    rw [hNU, F.endpointSpan_eq hgN.1]
    exact sup_le_sup_left hR _
  calc Module.finrank k N ≤ Module.finrank k
        ((k ∙ g) ⊔ (F.corner (k := k) x y ⊓ radFilt k A (d + 1)) : Submodule k A) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank k (k ∙ g) + Module.finrank k
        (F.corner (k := k) x y ⊓ radFilt k A (d + 1) : Submodule k A) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ 1 + _ := by
        gcongr
        exact (finrank_span_le_card ({g} : Set A)).trans (by simp)
    _ = _ := add_comm _ _

/-- **Elements of the same radical degree lie in the same ray.** -/
theorem ray_eq_of_degree (hA : IsRepresentationFinite k A) {x y : Fin F.m} {f g : A}
    (hf : f ∈ F.corner (k := k) x y) (hg : g ∈ F.corner (k := k) x y) {d : ℕ}
    (hfd : f ∈ radFilt k A d) (hfd' : f ∉ radFilt k A (d + 1))
    (hgd : g ∈ radFilt k A d) (hgd' : g ∉ radFilt k A (d + 1)) :
    F.ray (k := k) x y f = F.ray (k := k) x y g := by
  set N := F.corner (k := k) x y ⊓ radFilt k A d
  have hN0 : N ≠ ⊥ := fun h ↦ hfd' (by
    have : f ∈ N := ⟨hf, hfd⟩
    rw [h, Submodule.mem_bot] at this
    rw [this]; exact Submodule.zero_mem _)
  obtain ⟨h, hhN, hh0, hNU⟩ := F.exists_cyclic hA (F.radFilt_isEndpoint x y d) hN0
  have hR := F.endpointRadical_le_radFilt hhN.1 hhN.2
  have key : ∀ z, z ∈ F.corner (k := k) x y → z ∈ radFilt k A d → z ∉ radFilt k A (d + 1) →
      F.ray (k := k) x y z = F.ray (k := k) x y h := fun z hz hzd hzd' ↦
    F.ray_eq_of_mem hhN.1 ((F.mem_ray_iff hA hhN.1 hh0 z).2
      ⟨hNU ▸ ⟨hz, hzd⟩, fun hzR ↦ hzd' (hR hzR).2⟩)
  rw [key f hf hfd hfd', key g hg hgd hgd']

/-- **A strictly smaller subbimodule has a strictly larger radical degree.** -/
theorem degree_lt_of_lt (hA : IsRepresentationFinite k A) {x y : Fin F.m} {f g : A}
    (hf : f ∈ F.corner (k := k) x y) (hg : g ∈ F.corner (k := k) x y)
    (hlt : F.endpointSpan (k := k) x y g < F.endpointSpan (k := k) x y f) {d d' : ℕ}
    (hfd : f ∈ radFilt k A d) (hgd' : g ∈ radFilt k A d') (hgd'' : g ∉ radFilt k A (d' + 1)) :
    d < d' := by
  have hfg : f ∉ F.endpointSpan (k := k) x y g := fun h ↦
    (not_le_of_gt hlt) (F.endpointSpan_le (F.isEndpoint_endpointSpan hg) h)
  have hgR := F.le_endpointRadical hA hf (F.isEndpoint_endpointSpan hg) hlt.le hfg
    (F.mem_endpointSpan_self hg)
  have hg1 := (F.endpointRadical_le_radFilt hf hfd hgR).2
  by_contra hdd
  exact hgd'' (radFilt_antitone (by omega) hg1)

/-- Every nonzero element has a radical degree. -/
theorem exists_degree {f : A} (hf0 : f ≠ 0) :
    ∃ d, f ∈ radFilt k A d ∧ f ∉ radFilt k A (d + 1) := by
  classical
  obtain ⟨K, hK⟩ := algebraRadical_pow_eq_bot (k := k) (A := A)
  have hex : ∃ n, f ∉ radFilt k A n := ⟨K + 1, fun h ↦ hf0 (by
    have : radFilt k A (K + 1) ≤ ⊥ := by
      change algebraRadicalPow k A (K + 1) ≤ ⊥
      rw [algebraRadicalPow, pow_succ, hK, Submodule.bot_mul]
    exact (Submodule.mem_bot k).1 (this h))⟩
  have hn0 : Nat.find hex ≠ 0 := fun h ↦ (Nat.find_spec hex) (h ▸ trivial)
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨d, ?_, by have := Nat.find_spec hex; rwa [hd] at this⟩
  by_contra h
  exact absurd (Nat.find_min' hex h) (by omega)

end PrimitiveIdempotents

end MultiplicativeBasisDeformations
