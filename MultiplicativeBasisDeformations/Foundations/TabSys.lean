import MultiplicativeBasisDeformations.Foundations.LinCorners
import MultiplicativeBasisDeformations.Foundations.EndpointChains
import MultiplicativeBasisDeformations.Foundations.LocalCorner
import MultiplicativeBasisDeformations.Foundations.GradedLayers

/-!
# Setting 8.4 from a representation-finite ray table

Setting 8.4 (`local-ray-geometry.tex`) for a finite ray table `P` with
representation-finite linearization: "Write `R_x = k[q_x]/(q_x^{N_x})` when `R_x ≠ k`,
choosing `q_x` as its homogeneous radical generator", with the endpoint chains of
Lemma 3.1(3). The identity vectors of `kP` are a complete set of primitive orthogonal
idempotents; the corners are spanned by rays, and the corner radicals by the local rays of
positive degree. By Lemma 3.1(3) (`exists_rad_gen`) at most one positive local ray at `x` is
not a product of two positive local rays; it generates all local rays (`q_x`). Every Hom is
cyclic over one endpoint (`endpointSpan_one_sided`) and its endpoint subbimodules form a
chain (`isChain_subbimodules`), which gives the fields `cyc` and `chain` of `Sys`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Tab

variable {V R L : Type} [AddCommGroup L] [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R]
  (P : Tab V R L) (k : Type u) [Field k] [IsAlgClosed k]

theorem b_e_complete : CompleteOrthogonalIdempotents fun x ↦ P.b k (P.e x) := by
  refine ⟨⟨fun x ↦ ?_, fun x y hxy ↦ ?_⟩, Mult.sum_b_e _ k⟩
  · change _ * _ = _; rw [Mult.b_e_mul, if_pos (P.src_e x).symm]
  · change _ * _ = _; rw [Mult.b_e_mul, if_neg (by rw [P.src_e]; exact hxy)]

theorem b_e_primitive (x : V) : IsPrimitiveIdempotent (P.b k (P.e x)) := by
  refine ⟨(P.b_e_complete k).idem x, Mult.b_ne_zero _ k _, fun f hf h1 h2 ↦ ?_⟩
  have hc : f ∈ P.corSp k x x := by
    have := P.e_mul_mul_e_mem k x x f
    rwa [h1, h2] at this
  exact P.idem_local k hc hf.eq

/-- The identity vectors of `kP` as primitive idempotents. -/
def linIdem : PrimitiveIdempotents (P.Lin k) where
  m := Fintype.card V
  e i := P.b k (P.e ((Fintype.equivFin V).symm i))
  complete := (CompleteOrthogonalIdempotents.equiv (Fintype.equivFin V).symm).2 (P.b_e_complete k)
  primitive _ := P.b_e_primitive k _

/-- Vertices as indices of the identity vectors. -/
def linIdx : V ≃ Fin (P.linIdem k).m := Fintype.equivFin V

theorem linIdem_e (x : V) : (P.linIdem k).e (P.linIdx k x) = P.b k (P.e x) := by
  change P.b k (P.e ((Fintype.equivFin V).symm (Fintype.equivFin V x))) = _
  rw [Equiv.symm_apply_apply]

theorem linIdem_e' (i : Fin (P.linIdem k).m) :
    (P.linIdem k).e i = P.b k (P.e ((P.linIdx k).symm i)) := rfl

theorem corner_eq (x y : V) :
    (P.linIdem k).corner (k := k) (P.linIdx k x) (P.linIdx k y) = P.corSp k x y := by
  ext a
  rw [PrimitiveIdempotents.mem_corner_iff', linIdem_e, linIdem_e]
  constructor
  · intro h; rw [← h]; exact P.e_mul_mul_e_mem k x y a
  · intro h; rw [P.e_mul_of_mem_corSp k h, P.mul_e_of_mem_corSp k h]

/-- Rays of positive degree span a two-sided ideal contained in the radical. -/
theorem degSp_le_radical : P.degSp k 1 ≤ algebraRadical k (P.Lin k) := by
  intro n hn
  obtain ⟨N, hN⟩ := P.nilpotent_degSp k
  have h0 : ∀ y : P.Lin k, y ∈ P.degSp k 0 := fun y ↦ by
    rw [P.mem_degSp_iff]; intro r _; exact P.deg_nonneg r
  refine mem_jacobson_of_forall_isUnit fun y ↦ ?_
  refine IsNilpotent.isUnit_one_sub ⟨N, hN _ ?_⟩
  simpa using P.mul_mem_degSp k (h0 y) hn

theorem cornerRadical_eq (x : V) :
    (P.linIdem k).cornerRadical (k := k) (P.linIdx k x) = P.corSp k x x ⊓ P.degSp k 1 := by
  ext a
  simp only [PrimitiveIdempotents.cornerRadical, Submodule.mem_inf, corner_eq]
  constructor
  · rintro ⟨ha, har⟩
    refine ⟨ha, ?_⟩
    have hn := P.local_decomp k ha
    set c := (P.basis k).repr a (P.e x)
    by_cases hc : c = 0
    · have : a = a - c • P.b k (P.e x) := by rw [hc, zero_smul, sub_zero]
      rw [this]; exact hn.2
    · exfalso
      have he : P.b k (P.e x) ∈ algebraRadical k (P.Lin k) := by
        have h1 : c • P.b k (P.e x) ∈ algebraRadical k (P.Lin k) := by
          have := sub_mem har (P.degSp_le_radical k hn.2)
          rwa [sub_sub_cancel] at this
        have := Submodule.smul_mem _ c⁻¹ h1
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
      obtain ⟨K, hK⟩ := algebraRadical_pow_eq_bot (k := k) (A := P.Lin k)
      have hpow : P.b k (P.e x) ^ (K + 1) ∈ algebraRadical k (P.Lin k) ^ (K + 1) :=
        Submodule.pow_mem_pow _ he _
      have hidem : P.b k (P.e x) ^ (K + 1) = P.b k (P.e x) :=
        ((P.b_e_complete k).idem x).pow_succ_eq K
      rw [hidem, pow_succ, hK, Submodule.bot_mul, Submodule.mem_bot] at hpow
      exact Mult.b_ne_zero _ k _ hpow
  · rintro ⟨ha, hn⟩
    exact ⟨ha, P.degSp_le_radical k hn⟩

/-! ### Elements of the ray monoid as vectors -/

/-- The vector of a ray, and zero. -/
def vecT (a : M P.toMult) : P.Lin k := Elt.rec 0 0 (fun r ↦ P.b k r) a

theorem vecT_rr (r : R) : P.vecT k (P.rr r) = P.b k r := rfl

theorem vecT_zero : P.vecT k 0 = 0 := rfl

theorem b_mul_b' (u v : R) : P.b k u * P.b k v = P.vecT k (P.rr u * P.rr v) := by
  rw [Mult.b_mul, Mult.rr_mul_rr]
  cases P.mul u v <;> rfl

theorem vecT_mul_b (w : R) {a : M P.toMult} (ha : a = 0 ∨ ∃ u, a = P.rr u) :
    P.vecT k a * P.b k w = P.vecT k (a * P.rr w) := by
  rcases ha with rfl | ⟨u, rfl⟩
  · rw [vecT_zero, zero_mul, zero_mul]; rfl
  · rw [vecT_rr, b_mul_b']

theorem b_mul_vecT (u : R) {a : M P.toMult} (ha : a = 0 ∨ ∃ w, a = P.rr w) :
    P.b k u * P.vecT k a = P.vecT k (P.rr u * a) := by
  rcases ha with rfl | ⟨w, rfl⟩
  · rw [vecT_zero, mul_zero, mul_zero]; rfl
  · rw [vecT_rr, b_mul_b']

theorem rr_mul_rr_cases' (u v : R) : P.rr u * P.rr v = 0 ∨ ∃ t, P.rr u * P.rr v = P.rr t := by
  rw [Mult.rr_mul_rr]
  cases P.mul u v with
  | none => exact Or.inl rfl
  | some t => exact Or.inr ⟨t, rfl⟩

theorem mul_rr_cases {a : M P.toMult} (ha : a = 0 ∨ ∃ u, a = P.rr u) (v : R) :
    a * P.rr v = 0 ∨ ∃ t, a * P.rr v = P.rr t := by
  rcases ha with rfl | ⟨u, rfl⟩
  · left; exact zero_mul _
  · exact P.rr_mul_rr_cases' u v

theorem rr_mul_cases (u : R) {a : M P.toMult} (ha : a = 0 ∨ ∃ v, a = P.rr v) :
    P.rr u * a = 0 ∨ ∃ t, P.rr u * a = P.rr t := by
  rcases ha with rfl | ⟨v, rfl⟩
  · left; exact mul_zero _
  · exact P.rr_mul_rr_cases' u v

/-! ### The local generator -/

/-- Local rays of positive degree at `x`. -/
def PosL (x : V) : Set R := {l | P.src l = x ∧ P.tgt l = x ∧ l ≠ P.e x}

/-- Positive local rays which are products of two positive local rays. -/
def ProdL (x : V) : Set R :=
  {t | ∃ l₁ l₂, l₁ ∈ P.PosL x ∧ l₂ ∈ P.PosL x ∧ P.mul l₁ l₂ = some t}

/-- Positive local rays which are not such products. -/
def GenL (x : V) : Set R := {g | g ∈ P.PosL x ∧ g ∉ P.ProdL x}

theorem posL_deg {x : V} {l : R} (hl : l ∈ P.PosL x) : 1 ≤ P.deg (P.wt l) := by
  have := P.deg_pos l (by rw [hl.1]; exact hl.2.2); omega

theorem corRad_span (x : V) :
    P.corSp k x x ⊓ P.degSp k 1 = Submodule.span k (P.basis k '' P.PosL x) := by
  ext a
  rw [Submodule.mem_inf, P.mem_corSp_iff, P.mem_degSp_iff, Module.Basis.mem_span_image]
  constructor
  · rintro ⟨h1, h2⟩ r hr
    have hr' := Finsupp.mem_support_iff.1 hr
    obtain ⟨e1, e2⟩ := h1 r hr'
    refine ⟨e1, e2, fun he ↦ ?_⟩
    have := h2 r hr'
    rw [he, P.wt_e, map_zero] at this
    omega
  · intro h
    refine ⟨fun r hr ↦ ?_, fun r hr ↦ ?_⟩
    · obtain ⟨e1, e2, -⟩ := h (Finsupp.mem_support_iff.2 hr); exact ⟨e1, e2⟩
    · exact P.posL_deg (h (Finsupp.mem_support_iff.2 hr))

theorem corRad_sq_le (x : V) :
    (P.corSp k x x ⊓ P.degSp k 1) * (P.corSp k x x ⊓ P.degSp k 1) ≤
      Submodule.span k (P.basis k '' P.ProdL x) := by
  rw [P.corRad_span k x, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨l₁, h₁, rfl⟩, _, ⟨l₂, h₂, rfl⟩, rfl⟩
  simp only [Mult.basis_apply]
  rw [Mult.b_mul]
  rcases h : P.mul l₁ l₂ with _ | t
  · exact zero_mem _
  · show P.b k t ∈ _
    exact Submodule.subset_span ⟨t, ⟨l₁, l₂, h₁, h₂, h⟩, rfl⟩

theorem repr_eq_zero_of_mem_span {T : Set R} {a : P.Lin k}
    (ha : a ∈ Submodule.span k (P.basis k '' T)) {r : R} (hr : r ∉ T) :
    (P.basis k).repr a r = 0 := by
  rw [Module.Basis.mem_span_image] at ha
  by_contra h
  exact hr (ha (Finsupp.mem_support_iff.2 h))

variable (hfin : IsRepresentationFinite k (P.Lin k))

include hfin in
/-- **At most one positive local ray is not a product** (`dim rad/rad² ≤ 1`, Lemma 3.1(3)). -/
theorem genL_unique {x : V} {g g' : R} (hg : g ∈ P.GenL x) (hg' : g' ∈ P.GenL x) : g = g' := by
  classical
  obtain ⟨t, -, ht⟩ := (P.linIdem k).exists_rad_gen hfin (P.linIdx k x)
  rw [cornerRadical_eq] at ht
  have hdec : ∀ l ∈ P.GenL x, ∃ α : k, ∃ p ∈ Submodule.span k (P.basis k '' P.ProdL x),
      P.b k l = α • t + p := by
    intro l hl
    have hl' : P.b k l ∈ P.corSp k x x ⊓ P.degSp k 1 := by
      rw [P.corRad_span k x]
      exact Submodule.subset_span ⟨l, hl.1, Mult.basis_apply _ _ l⟩
    obtain ⟨u, hu, p, hp, hup⟩ := Submodule.mem_sup.1 (ht hl')
    obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.1 hu
    exact ⟨α, p, P.corRad_sq_le k x hp, hup.symm⟩
  obtain ⟨α, p, hp, hgp⟩ := hdec g hg
  obtain ⟨α', p', hp', hgp'⟩ := hdec g' hg'
  have hrep : ∀ l, (P.basis k).repr (P.b k l) = Finsupp.single l 1 := fun l ↦ by
    rw [← Mult.basis_apply, Module.Basis.repr_self]
  have e1 := congrArg (fun z ↦ (P.basis k).repr z g) hgp
  have e2 := congrArg (fun z ↦ (P.basis k).repr z g') hgp'
  simp only [hrep, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_eq_same, P.repr_eq_zero_of_mem_span k hp hg.2,
    P.repr_eq_zero_of_mem_span k hp' hg'.2, add_zero] at e1 e2
  by_contra hne
  have e3 := congrArg (fun z ↦ (P.basis k).repr z g) hgp'
  simp only [hrep, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    P.repr_eq_zero_of_mem_span k hp' hg.2, add_zero] at e3
  rw [Finsupp.single_apply, if_neg (fun h ↦ hne h.symm)] at e3
  have : α' = 0 := by
    rcases mul_eq_zero.1 e3.symm with h | h
    · exact h
    · rw [h, mul_zero] at e1; exact absurd e1 one_ne_zero
  rw [this, zero_mul] at e2
  exact one_ne_zero e2

theorem genL_exists {x : V} (h : (P.PosL x).Nonempty) : ∃ g, g ∈ P.GenL x := by
  classical
  obtain ⟨l, hl, hmin⟩ := (Set.toFinite (P.PosL x)).toFinset.exists_min_image
    (fun l ↦ P.deg (P.wt l)) (by simpa using h)
  rw [Set.Finite.mem_toFinset] at hl
  refine ⟨l, hl, ?_⟩
  rintro ⟨l₁, l₂, h₁, h₂, h12⟩
  have hm := hmin l₁ (by rw [Set.Finite.mem_toFinset]; exact h₁)
  have hw := P.wt_mul l₁ l₂ l h12
  have h2 := P.posL_deg h₂
  rw [hw, map_add] at hm
  omega

include hfin in
/-- **Every positive local ray is a power of the generator.** -/
theorem posL_eq_pow {x : V} {g : R} (hg : g ∈ P.GenL x) :
    ∀ l ∈ P.PosL x, ∃ j : ℕ, 1 ≤ j ∧ P.rr l = P.rr g ^ j := by
  classical
  intro l hl
  induction hd : (P.deg (P.wt l)).toNat using Nat.strong_induction_on generalizing l with
  | _ d ih =>
    by_cases hp : l ∈ P.ProdL x
    · obtain ⟨l₁, l₂, h₁, h₂, h12⟩ := hp
      have hw : P.deg (P.wt l) = P.deg (P.wt l₁) + P.deg (P.wt l₂) := by
        rw [P.wt_mul l₁ l₂ l h12, map_add]
      have d1 := P.posL_deg h₁
      have d2 := P.posL_deg h₂
      obtain ⟨a, ha, ea⟩ := ih _ (by omega) l₁ h₁ rfl
      obtain ⟨b, hb, eb⟩ := ih _ (by omega) l₂ h₂ rfl
      refine ⟨a + b, by omega, ?_⟩
      rw [pow_add, ← ea, ← eb, Mult.rr_mul_rr, h12]; rfl
    · exact ⟨1, le_rfl, by rw [pow_one, P.genL_unique k hfin hg ⟨hl, hp⟩]⟩

open Classical in
/-- **The local generator** `q_x` (zero when `R_x = k`). -/
def qT (x : V) : M P.toMult := if h : ∃ g, g ∈ P.GenL x then P.rr h.choose else 0

theorem qT_cases (x : V) : P.qT x = 0 ∨
    ∃ g, P.qT x = P.rr g ∧ P.src g = x ∧ P.tgt g = x ∧ g ≠ P.e x := by
  classical
  unfold qT
  split_ifs with h
  · right
    obtain ⟨h1, h2, h3⟩ := h.choose_spec.1
    exact ⟨h.choose, rfl, h1, h2, h3⟩
  · left; rfl

theorem qT_mul_e (x : V) : P.qT x * P.rr (P.e x) = P.qT x := by
  rcases P.qT_cases x with h | ⟨g, hg, -, h2, -⟩
  · rw [h, zero_mul]
  · rw [hg, ← h2]; exact Mult.rr_mul_e _ g

theorem e_mul_qT (x : V) : P.rr (P.e x) * P.qT x = P.qT x := by
  rcases P.qT_cases x with h | ⟨g, hg, h1, -, -⟩
  · rw [h, mul_zero]
  · rw [hg, ← h1]; exact Mult.e_mul_rr _ g

theorem qTpow_comm_e (x : V) (j : ℕ) : P.qT x ^ j * P.rr (P.e x) = P.rr (P.e x) * P.qT x ^ j :=
  (Commute.pow_left (show Commute (P.qT x) (P.rr (P.e x)) from
    (P.qT_mul_e x).trans (P.e_mul_qT x).symm) j).eq

include hfin in
theorem qT_pow (r : R) (h : P.src r = P.tgt r) :
    ∃ j : ℕ, P.qT (P.src r) ^ j * P.rr (P.e (P.src r)) = P.rr r := by
  classical
  by_cases hr : r = P.e (P.src r)
  · exact ⟨0, by rw [pow_zero, one_mul, ← hr]⟩
  have hpos : r ∈ P.PosL (P.src r) := ⟨rfl, h.symm, hr⟩
  have hex := P.genL_exists ⟨r, hpos⟩
  have hq : P.qT (P.src r) = P.rr hex.choose := by unfold qT; rw [dif_pos hex]
  obtain ⟨j, hj, hrj⟩ := P.posL_eq_pow k hfin hex.choose_spec r hpos
  obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le hj
  refine ⟨1 + j', ?_⟩
  rw [hq, hrj, add_comm, pow_succ, mul_assoc]
  congr 1
  have h2 : P.tgt hex.choose = P.src r := hex.choose_spec.1.2.1
  have := Mult.rr_mul_e P.toMult hex.choose
  rwa [h2] at this

/-- Local powers of the generator are local rays or zero. -/
theorem qTpow_e_cases (x : V) (j : ℕ) : P.qT x ^ j * P.rr (P.e x) = 0 ∨
    ∃ l, P.qT x ^ j * P.rr (P.e x) = P.rr l ∧ P.src l = x ∧ P.tgt l = x := by
  induction j with
  | zero => right; exact ⟨P.e x, by rw [pow_zero, one_mul], P.src_e x, P.tgt_e x⟩
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    rcases ih with h | ⟨l, hl, l1, l2⟩
    · left; rw [h, mul_zero]
    · rw [hl]
      rcases P.qT_cases x with hq | ⟨g, hg, g1, -, -⟩
      · left; rw [hq, zero_mul]
      · rw [hg]
        rcases P.rr_mul_rr_cases' g l with h0 | ⟨t, ht⟩
        · left; exact h0
        · right
          obtain ⟨e1, e2, -⟩ := P.mul_eq_rr_of ht
          exact ⟨t, ht, by rw [e1, g1], by rw [e2, l2]⟩

theorem zero_ne_one_M : (0 : M P.toMult) ≠ 1 := fun h ↦ by cases h

theorem mul_rr_mul_ne_one (a b : M P.toMult) (r : R) : a * P.rr r * b ≠ 1 := by
  rcases P.cases_elt a with rfl | rfl | ⟨u, rfl⟩
  · rw [one_mul]
    rcases P.cases_elt b with rfl | rfl | ⟨v, rfl⟩
    · rw [mul_one]; exact P.rr_ne_one r
    · rw [mul_zero]; exact P.zero_ne_one_M
    · rcases P.rr_mul_rr_cases' r v with h | ⟨t, ht⟩
      · rw [h]; exact P.zero_ne_one_M
      · rw [ht]; exact P.rr_ne_one t
  · rw [zero_mul, zero_mul]; exact P.zero_ne_one_M
  · rcases P.rr_mul_rr_cases' u r with h | ⟨t, ht⟩
    · rw [h, zero_mul]; exact P.zero_ne_one_M
    · rw [ht]
      rcases P.cases_elt b with rfl | rfl | ⟨v, rfl⟩
      · rw [mul_one]; exact P.rr_ne_one t
      · rw [mul_zero]; exact P.zero_ne_one_M
      · rcases P.rr_mul_rr_cases' t v with h | ⟨t', ht'⟩
        · rw [h]; exact P.zero_ne_one_M
        · rw [ht']; exact P.rr_ne_one t'

theorem eq_rr_of_ne_zero {a b : M P.toMult} {r : R} (h : a * P.rr r * b ≠ 0) :
    ∃ t, a * P.rr r * b = P.rr t := by
  rcases P.cases_elt (a * P.rr r * b) with h1 | h0 | ht
  · exact absurd h1 (P.mul_rr_mul_ne_one a b r)
  · exact absurd h0 h
  · exact ht

include hfin in
/-- A local ray is a local power of the generator times the identity. -/
theorem local_eq_qTpow {l : R} {x : V} (h1 : P.src l = x) (h2 : P.tgt l = x) :
    ∃ j : ℕ, P.rr l = P.qT x ^ j * P.rr (P.e x) := by
  obtain ⟨j, hj⟩ := P.qT_pow k hfin l (h1.trans h2.symm)
  exact ⟨j, by rw [← h1]; exact hj.symm⟩

include hfin in
theorem both_span (r : R) {a c : P.Lin k} (ha : a ∈ P.corSp k (P.src r) (P.src r))
    (hc : c ∈ P.corSp k (P.tgt r) (P.tgt r)) :
    a * P.b k r * c ∈ Submodule.span k (P.basis k ''
      {s | ∃ i j : ℕ, P.rr s = P.qT (P.src r) ^ i * P.rr r * P.qT (P.tgt r) ^ j}) := by
  have key : ∀ l l', P.src l = P.src r → P.tgt l = P.src r → P.src l' = P.tgt r →
      P.tgt l' = P.tgt r → P.b k l * P.b k r * P.b k l' ∈ Submodule.span k (P.basis k ''
        {s | ∃ i j : ℕ, P.rr s = P.qT (P.src r) ^ i * P.rr r * P.qT (P.tgt r) ^ j}) := by
    intro l l' l1 l2 l1' l2'
    obtain ⟨i, hi⟩ := P.local_eq_qTpow k hfin l1 l2
    obtain ⟨j, hj⟩ := P.local_eq_qTpow k hfin l1' l2'
    rw [P.b_mul_b' k, P.vecT_mul_b k l' (P.rr_mul_rr_cases' l r)]
    have e : P.rr l * P.rr r * P.rr l' = P.qT (P.src r) ^ i * P.rr r * P.qT (P.tgt r) ^ j := by
      rw [hi, hj, P.qTpow_comm_e (P.tgt r)]
      simp only [mul_assoc]
      rw [← mul_assoc (P.rr r) (P.rr (P.e (P.tgt r))), Mult.rr_mul_e,
        ← mul_assoc (P.rr (P.e (P.src r))) (P.rr r), Mult.e_mul_rr]
    rw [e]
    by_cases h0 : P.qT (P.src r) ^ i * P.rr r * P.qT (P.tgt r) ^ j = 0
    · rw [h0, vecT_zero]; exact zero_mem _
    · obtain ⟨t, ht⟩ := P.eq_rr_of_ne_zero h0
      rw [ht, vecT_rr]
      exact Submodule.subset_span ⟨t, ⟨i, j, ht.symm⟩, Mult.basis_apply _ _ t⟩
  have hc' : ∀ l, P.src l = P.src r → P.tgt l = P.src r → P.b k l * P.b k r * c ∈
      Submodule.span k (P.basis k ''
        {s | ∃ i j : ℕ, P.rr s = P.qT (P.src r) ^ i * P.rr r * P.qT (P.tgt r) ^ j}) := by
    intro l l1 l2
    induction hc using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l', ⟨l1', l2'⟩, rfl⟩ := hz
      rw [Mult.basis_apply]; exact key l l' l1 l2 l1' l2'
    | zero => rw [mul_zero]; exact zero_mem _
    | add z z' _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | smul t z _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ t h
  induction ha using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, ⟨l1, l2⟩, rfl⟩ := hz
    rw [Mult.basis_apply]; exact hc' l l1 l2
  | zero => rw [zero_mul, zero_mul]; exact zero_mem _
  | add z z' _ _ h1 h2 => rw [add_mul, add_mul]; exact add_mem h1 h2
  | smul t z _ h => rw [smul_mul_assoc, smul_mul_assoc]; exact Submodule.smul_mem _ t h

theorem mem_of_b_mem_span {T : Set R} {r : R} (h : P.b k r ∈ Submodule.span k (P.basis k '' T)) :
    r ∈ T := by
  rw [Module.Basis.mem_span_image, ← Mult.basis_apply, Module.Basis.repr_self,
    Finsupp.support_single_ne_zero _ one_ne_zero, Finset.coe_singleton,
    Set.singleton_subset_iff] at h
  exact h

theorem b_mem_corner (r : R) :
    P.b k r ∈ (P.linIdem k).corner (k := k) (P.linIdx k (P.src r)) (P.linIdx k (P.tgt r)) := by
  rw [corner_eq]; exact P.b_mem_corSp k r

include hfin in
theorem b_mem_endpointSpan {r t : R} {i j : ℕ}
    (ht : P.rr t = P.qT (P.src r) ^ i * P.rr r * P.qT (P.tgt r) ^ j) :
    P.b k t ∈ (P.linIdem k).endpointSpan (k := k) (P.linIdx k (P.src r)) (P.linIdx k (P.tgt r))
      (P.b k r) := by
  have hne : P.qT (P.src r) ^ i * P.rr r * P.qT (P.tgt r) ^ j ≠ 0 := by
    rw [← ht]; exact Mult.rr_ne_zero _ t
  have hl : P.qT (P.src r) ^ i * P.rr r = P.qT (P.src r) ^ i * P.rr (P.e (P.src r)) * P.rr r := by
    rw [mul_assoc, Mult.e_mul_rr]
  have hr : P.rr r * P.qT (P.tgt r) ^ j = P.rr r * (P.qT (P.tgt r) ^ j * P.rr (P.e (P.tgt r))) := by
    rw [P.qTpow_comm_e, ← mul_assoc, Mult.rr_mul_e]
  rcases P.qTpow_e_cases (P.src r) i with h0 | ⟨l, hl', l1, l2⟩
  · exact absurd (by rw [hl, h0, zero_mul, zero_mul]) hne
  rcases P.qTpow_e_cases (P.tgt r) j with h0 | ⟨l', hl'', l1', l2'⟩
  · exact absurd (by rw [mul_assoc, hr, h0, mul_zero, mul_zero]) hne
  have e : P.b k t = P.b k l * P.b k r * P.b k l' := by
    rw [P.b_mul_b' k, P.vecT_mul_b k l' (P.rr_mul_rr_cases' l r), ← hl', ← hl'', ← vecT_rr]
    congr 1
    rw [ht, mul_assoc, hr, ← mul_assoc, hl, mul_assoc (P.qT _ ^ i)]
  rw [e]
  refine Submodule.subset_span ⟨P.b k l, ?_, P.b k l', ?_, rfl⟩
  · rw [corner_eq]; exact P.b_mem_corSp' k l1 l2
  · rw [corner_eq]; exact P.b_mem_corSp' k l1' l2'

include hfin in
theorem left_span (r : R) {a : P.Lin k} (ha : a ∈ P.corSp k (P.src r) (P.src r)) :
    a * P.b k r ∈ Submodule.span k (P.basis k '' {s | ∃ i : ℕ, P.rr s = P.qT (P.src r) ^ i * P.rr r}) := by
  induction ha using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, ⟨l1, l2⟩, rfl⟩ := hz
    rw [Mult.basis_apply, P.b_mul_b' k]
    obtain ⟨i, hi⟩ := P.local_eq_qTpow k hfin l1 l2
    rcases P.rr_mul_rr_cases' l r with h0 | ⟨t, ht⟩
    · rw [h0, vecT_zero]; exact zero_mem _
    · rw [ht, vecT_rr]
      refine Submodule.subset_span ⟨t, ⟨i, ?_⟩, Mult.basis_apply _ _ t⟩
      rw [← ht, hi, mul_assoc, Mult.e_mul_rr]
  | zero => rw [zero_mul]; exact zero_mem _
  | add z z' _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | smul t z _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ t h

include hfin in
theorem right_span (r : R) {c : P.Lin k} (hc : c ∈ P.corSp k (P.tgt r) (P.tgt r)) :
    P.b k r * c ∈ Submodule.span k (P.basis k '' {s | ∃ j : ℕ, P.rr s = P.rr r * P.qT (P.tgt r) ^ j}) := by
  induction hc using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, ⟨l1, l2⟩, rfl⟩ := hz
    rw [Mult.basis_apply, P.b_mul_b' k]
    obtain ⟨j, hj⟩ := P.local_eq_qTpow k hfin l1 l2
    rcases P.rr_mul_rr_cases' r l with h0 | ⟨t, ht⟩
    · rw [h0, vecT_zero]; exact zero_mem _
    · rw [ht, vecT_rr]
      refine Submodule.subset_span ⟨t, ⟨j, ?_⟩, Mult.basis_apply _ _ t⟩
      rw [← ht, hj, P.qTpow_comm_e, ← mul_assoc, Mult.rr_mul_e]
  | zero => rw [mul_zero]; exact zero_mem _
  | add z z' _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | smul t z _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ t h

include hfin in
theorem cycT (r : R) :
    (∀ i j : ℕ, P.qT (P.src r) ^ i * P.rr r * P.qT (P.tgt r) ^ j ≠ 0 →
      ∃ i' : ℕ, P.qT (P.src r) ^ i * P.rr r * P.qT (P.tgt r) ^ j = P.qT (P.src r) ^ i' * P.rr r) ∨
    (∀ i j : ℕ, P.qT (P.src r) ^ i * P.rr r * P.qT (P.tgt r) ^ j ≠ 0 →
      ∃ j' : ℕ, P.qT (P.src r) ^ i * P.rr r * P.qT (P.tgt r) ^ j = P.rr r * P.qT (P.tgt r) ^ j') := by
  rcases (P.linIdem k).endpointSpan_one_sided hfin (P.b_mem_corner k r) with hL | hR
  · left
    intro i j hne
    obtain ⟨t, ht⟩ := P.eq_rr_of_ne_zero hne
    have hb := P.b_mem_endpointSpan k hfin ht.symm
    rw [hL] at hb
    have hle : Submodule.span k {g | ∃ a ∈ (P.linIdem k).corner (k := k) (P.linIdx k (P.src r))
        (P.linIdx k (P.src r)), g = a * P.b k r} ≤
        Submodule.span k (P.basis k '' {s | ∃ i : ℕ, P.rr s = P.qT (P.src r) ^ i * P.rr r}) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      rw [corner_eq] at ha
      exact P.left_span k hfin r ha
    obtain ⟨i', hi'⟩ := P.mem_of_b_mem_span k (hle hb)
    exact ⟨i', ht.trans hi'⟩
  · right
    intro i j hne
    obtain ⟨t, ht⟩ := P.eq_rr_of_ne_zero hne
    have hb := P.b_mem_endpointSpan k hfin ht.symm
    rw [hR] at hb
    have hle : Submodule.span k {g | ∃ c ∈ (P.linIdem k).corner (k := k) (P.linIdx k (P.tgt r))
        (P.linIdx k (P.tgt r)), g = P.b k r * c} ≤
        Submodule.span k (P.basis k '' {s | ∃ j : ℕ, P.rr s = P.rr r * P.qT (P.tgt r) ^ j}) := by
      rw [Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [corner_eq] at hc
      exact P.right_span k hfin r hc
    obtain ⟨j', hj'⟩ := P.mem_of_b_mem_span k (hle hb)
    exact ⟨j', ht.trans hj'⟩

include hfin in
theorem endpointSpan_le_both (s : R) :
    (P.linIdem k).endpointSpan (k := k) (P.linIdx k (P.src s)) (P.linIdx k (P.tgt s)) (P.b k s) ≤
      Submodule.span k (P.basis k ''
        {t | ∃ i j : ℕ, P.rr t = P.qT (P.src s) ^ i * P.rr s * P.qT (P.tgt s) ^ j}) := by
  rw [PrimitiveIdempotents.endpointSpan, Submodule.span_le]
  rintro _ ⟨a, ha, c, hc, rfl⟩
  rw [corner_eq] at ha hc
  exact P.both_span k hfin s ha hc

include hfin in
theorem chainT (r s : R) (h1 : P.src r = P.src s) (h2 : P.tgt r = P.tgt s) :
    (∃ i j : ℕ, P.rr r = P.qT (P.src r) ^ i * P.rr s * P.qT (P.tgt r) ^ j) ∨
      (∃ i j : ℕ, P.rr s = P.qT (P.src r) ^ i * P.rr r * P.qT (P.tgt r) ^ j) := by
  have hr := P.b_mem_corner k r
  have hs := P.b_mem_corner k s
  rw [← h1, ← h2] at hs
  have hUr := (P.linIdem k).isEndpoint_endpointSpan hr
  have hUs := (P.linIdem k).isEndpoint_endpointSpan hs
  have hrU := (P.linIdem k).mem_endpointSpan_self hr
  have hsU := (P.linIdem k).mem_endpointSpan_self hs
  have hleS := P.endpointSpan_le_both k hfin s
  have hleR := P.endpointSpan_le_both k hfin r
  rw [← h1, ← h2] at hleS
  have caseS : (P.linIdem k).endpointSpan (k := k) (P.linIdx k (P.src r)) (P.linIdx k (P.tgt r))
      (P.b k r) ≤ (P.linIdem k).endpointSpan (k := k) (P.linIdx k (P.src r))
      (P.linIdx k (P.tgt r)) (P.b k s) → ∃ i j : ℕ,
        P.rr r = P.qT (P.src r) ^ i * P.rr s * P.qT (P.tgt r) ^ j := fun h ↦ by
    exact P.mem_of_b_mem_span k (hleS (h hrU))
  by_cases heq : (P.linIdem k).endpointSpan (k := k) (P.linIdx k (P.src r)) (P.linIdx k (P.tgt r))
      (P.b k r) = (P.linIdem k).endpointSpan (k := k) (P.linIdx k (P.src r))
      (P.linIdx k (P.tgt r)) (P.b k s)
  · exact Or.inl (caseS heq.le)
  rcases (P.linIdem k).isChain_subbimodules hfin _ _ hUr hUs heq with h | h
  · exact Or.inl (caseS h)
  · exact Or.inr (P.mem_of_b_mem_span k (hleR (h hsU)))

/-- **Setting 8.4 for a representation-finite ray table.** -/
def toSys : Sys V R L where
  P := P
  q := P.qT
  q_cases := P.qT_cases
  q_pow := P.qT_pow k hfin
  cyc := P.cycT k hfin
  chain := P.chainT k hfin

theorem toSys_P : (P.toSys k hfin).P = P := rfl

end Tab

end RaySys

end MultiplicativeBasisDeformations
