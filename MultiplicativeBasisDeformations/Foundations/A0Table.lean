import MultiplicativeBasisDeformations.Foundations.TableOfBasis
import MultiplicativeBasisDeformations.Foundations.TabSys
import MultiplicativeBasisDeformations.Foundations.A0Normed
import MultiplicativeBasisDeformations.Foundations.RayWeights
import MultiplicativeBasisDeformations.Foundations.MeshWeights
import MultiplicativeBasisDeformations.Foundations.RayBasis

/-!
# The ray table of `A₀`

Setting 8.4 (`local-ray-geometry.tex`) for `A₀`: "`A₀ = kP` … identified with `kP` by
Proposition 4.14. We use its normed homogeneous ray basis." The basis of Proposition 4.14
(`basisA0`) consists of one vector on each nonzero deck-homogeneous piece `A₀(x, y)_g`; its
multiplication table is the ray table `P` (`A0Tab`), with the weight `[x, y, g] ∈ W(P)` of
Definition 7.1 (`cls`) and the degree given by the length mesh weight. Rays with the same
endpoints and the same weight are equal, since both lie in one length degree and the length
pieces of a corner are lines (`lines`, Lemma 3.7 for `A₀`). By Theorem 4.? `A₀` is
representation-finite, so the table carries Setting 8.4 (`A0Sys`).

The basis vector of the piece `(x, y, g)` lies in the corner `e_y A₀ e_x` of the opposite
algebra, so the table has source `y` and target `x`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)

variable [IsAlgClosed k] [hone : ∀ x y : V, Subsingleton (x ⟶ y)]
  [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (v₀ : V) (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)

/-- The chosen deck-homogeneous vectors of Proposition 4.14. -/
def deckV : ∀ x y : D.PV, Deck Q v₀ → (D.F0 x ⟶ D.F0 y) :=
  (exists_deckVectors (Q := Q) (c := c) (v₀ := v₀) (D := D) hF).choose

theorem deckV_mem (x y : D.PV) (g : Deck Q v₀) : deckV D v₀ hF x y g ∈ (D0 Q c v₀ D).part g x y :=
  (exists_deckVectors (Q := Q) (c := c) (v₀ := v₀) (D := D) hF).choose_spec.1 x y g

theorem deckV_span (x y : D.PV) (g : Deck Q v₀) (f : D.F0 x ⟶ D.F0 y)
    (hf : f ∈ (D0 Q c v₀ D).part g x y) : ∃ c : k, f = c • deckV D v₀ hF x y g :=
  (exists_deckVectors (Q := Q) (c := c) (v₀ := v₀) (D := D) hF).choose_spec.2.1 x y g f hf

theorem deckV_ne (x y : D.PV) (g : Deck Q v₀) (h : (D0 Q c v₀ D).part g x y ≠ ⊥) :
    deckV D v₀ hF x y g ≠ 0 :=
  (exists_deckVectors (Q := Q) (c := c) (v₀ := v₀) (D := D) hF).choose_spec.2.2.1 x y g h

theorem deckV_id (x : D.PV) : deckV D v₀ hF x x 1 = 𝟙 (D.F0 x) :=
  (exists_deckVectors (Q := Q) (c := c) (v₀ := v₀) (D := D) hF).choose_spec.2.2.2.1 x

theorem deckV_mul (x y z : D.PV) (g h : Deck Q v₀) :
    deckV D v₀ hF x y g ≫ deckV D v₀ hF y z h = 0 ∨
      deckV D v₀ hF x y g ≫ deckV D v₀ hF y z h = deckV D v₀ hF x z (g * h) :=
  (exists_deckVectors (Q := Q) (c := c) (v₀ := v₀) (D := D) hF).choose_spec.2.2.2.2 x y z g h

/-- The rays of `A₀`: the nonzero deck-homogeneous pieces. -/
abbrev RayA0 := Idx (D0 Q c v₀ D)

/-- **The normed homogeneous ray basis of `A₀`** (Proposition 4.14). -/
def basisR : Module.Basis (RayA0 D v₀) k (Alg D.F0)ᵐᵒᵖ :=
  basisA0 (deckV D v₀ hF) (deckV_mem D v₀ hF) (deckV_span D v₀ hF) (deckV_ne D v₀ hF)

instance : Finite (RayA0 D v₀) :=
  Set.Finite.to_subtype (finite_nz (Q := Q) (c := c) (v₀ := v₀) (D := D))

theorem idTo_ne_zero' (x : D.PV) : 𝟙 (D.F0 x) ≠ 0 := id_ne_zero (L := L) x.1

/-- The identity piece of a vertex. -/
def eR (x : D.PV) : RayA0 D v₀ :=
  idIdx (deckV D v₀ hF) (deckV_mem D v₀ hF) (deckV_id D v₀ hF) (idTo_ne_zero' D) x

theorem basisR_eR (x : D.PV) :
    basisR D v₀ hF (eR D v₀ hF x) = MulOpposite.op (unitM x x (𝟙 (D.F0 x))) :=
  basisA0_idIdx _ _ _ _ _ _ x

theorem basisR_apply (t : RayA0 D v₀) :
    basisR D v₀ hF t = MulOpposite.op (unitM t.1.1 t.1.2.1 (deckV D v₀ hF t.1.1 t.1.2.1 t.1.2.2)) :=
  basisA0_apply _ _ _ _ t

theorem basisR_mult : IsMultiplicativeBasis (basisR D v₀ hF) :=
  basisA0_isMultiplicative _ _ _ _ (deckV_mul D v₀ hF)

theorem basisR_complete : CompleteOrthogonalIdempotents fun x ↦ basisR D v₀ hF (eR D v₀ hF x) :=
  idIdx_complete _ _ _ _ _ _

/-- Source of a ray of `A₀` (the opposite convention). -/
def srcR (t : RayA0 D v₀) : D.PV := t.1.2.1

/-- Target of a ray of `A₀`. -/
def tgtR (t : RayA0 D v₀) : D.PV := t.1.1

theorem basisR_corner (t : RayA0 D v₀) :
    basisR D v₀ hF (eR D v₀ hF (srcR D v₀ t)) * basisR D v₀ hF t *
      basisR D v₀ hF (eR D v₀ hF (tgtR D v₀ t)) = basisR D v₀ hF t := by
  rw [basisR_eR, basisR_eR, basisR_apply]
  exact op_unitM_corner_mul _ _ _

theorem srcR_eR (x : D.PV) : srcR D v₀ (eR D v₀ hF x) = x := rfl

theorem tgtR_eR (x : D.PV) : tgtR D v₀ (eR D v₀ hF x) = x := rfl

instance : Fintype (RayA0 D v₀) := Fintype.ofFinite _

/-- **The multiplication table of `A₀`.** -/
def A0Mult : RaySys.Mult D.PV (RayA0 D v₀) :=
  RaySys.OfBasis.multOfBasis (basisR D v₀ hF) (basisR_mult D v₀ hF) (eR D v₀ hF)
    (basisR_complete D v₀ hF) (srcR D v₀) (tgtR D v₀) (basisR_corner D v₀ hF) (srcR_eR D v₀ hF)
    (tgtR_eR D v₀ hF)

/-! ### Idempotents and length grading of `A₀` -/

theorem hfinObj : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y) := fun x y ↦ hfd x y

/-- The vertex idempotents of `A₀` as primitive idempotents. -/
def FpA0 : PrimitiveIdempotents (Alg D.F0)ᵐᵒᵖ where
  m := Fintype.card D.PV
  e i := basisR D v₀ hF (eR D v₀ hF ((Fintype.equivFin D.PV).symm i))
  complete := (CompleteOrthogonalIdempotents.equiv (Fintype.equivFin D.PV).symm).2
    (basisR_complete D v₀ hF)
  primitive i := idIdx_primitive _ _ _ _ _ _ (fun x φ hφ ↦ by
    haveI := L.end_isLocalRing x.1
    exact idem_eq_zero_or_one (R := End (meshFam Q c x.1)) (p := φ) hφ) _

/-- Vertices as indices of the idempotents of `A₀`. -/
def idxA0 : D.PV ≃ Fin (FpA0 D v₀ hF).m := Fintype.equivFin D.PV

theorem FpA0_e (x : D.PV) : (FpA0 D v₀ hF).e (idxA0 D v₀ hF x) = MulOpposite.op (unitM x x (𝟙 (D.F0 x))) := by
  change basisR D v₀ hF (eR D v₀ hF ((Fintype.equivFin D.PV).symm (Fintype.equivFin D.PV x))) = _
  rw [Equiv.symm_apply_apply, basisR_eR]

theorem FpA0_he0 (i : Fin (FpA0 D v₀ hF).m) : (lenA0 D (hfinObj (c := c))).IsHom 0 ((FpA0 D v₀ hF).e i) := by
  obtain ⟨x, rfl⟩ := (idxA0 D v₀ hF).surjective i
  rw [FpA0_e]
  have hone0 : 𝟙 (D.F0 x) ∈ degreePart c 0 x.1 x.1 := by
    have := pathMor_mem_degreePart c (Quiver.Path.nil : Quiver.Path x.1 x.1)
    rwa [pathMor_nil] at this
  exact unitM_isHom D hfinObj hone0

theorem FpA0_hcorner0 (i : Fin (FpA0 D v₀ hF).m) (a : (Alg D.F0)ᵐᵒᵖ)
    (ha : a ∈ (FpA0 D v₀ hF).corner (k := k) i i) (h0 : (lenA0 D (hfinObj (c := c))).IsHom 0 a) :
    ∃ t : k, a = t • (FpA0 D v₀ hF).e i := by
  obtain ⟨x, rfl⟩ := (idxA0 D v₀ hF).surjective i
  rw [PrimitiveIdempotents.mem_corner_iff', FpA0_e] at ha
  rw [FpA0_e]
  obtain ⟨a', rfl⟩ : ∃ a' : Alg D.F0, MulOpposite.op a' = a := ⟨a.unop, rfl⟩
  rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, MulOpposite.op_inj] at ha
  set E := unitM x x (𝟙 (D.F0 x))
  have hEE : E * E = E := by rw [unitM_mul, Category.comp_id]
  have h1 : a' * E = a' := by
    calc a' * E = E * (a' * E) * E := by rw [ha]
      _ = E * (a' * (E * E)) := by simp only [mul_assoc]
      _ = a' := by rw [hEE, ha]
  have h2 : E * a' = a' := by
    calc E * a' = E * (E * (a' * E)) := by rw [ha]
      _ = E * E * (a' * E) := by rw [mul_assoc]
      _ = a' := by rw [hEE, ha]
  have heq := eq_unitM_of_corner h1 h2
  have hdeg : a' x x ∈ degreePart c 0 x.1 x.1 := by
    have := congrArg (fun z : (Alg D.F0)ᵐᵒᵖ ↦ z.unop x x) h0
    change degProj c 0 x.1 x.1 (a' x x) = a' x x at this
    rw [← this]
    exact degProj_mem c 0 _
  obtain ⟨t, ht⟩ := degreePart_zero_eq c hdeg
  refine ⟨t, ?_⟩
  rw [heq, ht, unitM_smul, MulOpposite.op_smul]

theorem basisR_mem_corner (t : RayA0 D v₀) :
    basisR D v₀ hF t ∈ (FpA0 D v₀ hF).corner (k := k) (idxA0 D v₀ hF (srcR D v₀ t))
      (idxA0 D v₀ hF (tgtR D v₀ t)) := by
  rw [PrimitiveIdempotents.mem_corner_iff', FpA0_e, FpA0_e, basisR_apply]
  exact op_unitM_corner_mul _ _ _

/-! ### Weights and degrees -/

/-- The length mesh weight: every arrow has weight one. -/
def lenW : MeshWt Q ℤ where
  w _ := 1
  ν _ := 2
  mesh _ _ := by norm_num

theorem lenW_pw {y x : V} (p : Quiver.Path y x) : (lenW (Q := Q)).pw p = p.length := by
  induction p with
  | nil => simp [MeshWt.pw]
  | cons p a ih => rw [MeshWt.pw, ih, Quiver.Path.length_cons]; simp [lenW]

theorem deg_cls_path {x y : D.PV} {g : Deck Q v₀} (h : NZ Q c v₀ D (x, y, g))
    {p : Quiver.Path x.1 y.1} (hp : (degW Q v₀).deg p = g) :
    (lenW (Q := Q)).res c D (cls Q c v₀ D (x, y, g)) = p.length := by
  rw [MeshWt.res_cls, MeshWt.rv_path _ h hp, lenW_pw]

theorem basisR_isHom {x y : D.PV} {g : Deck Q v₀} (h : NZ Q c v₀ D (x, y, g))
    {p : Quiver.Path x.1 y.1} (hp : (degW Q v₀).deg p = g) :
    (lenA0 D (hfinObj (c := c))).IsHom p.length (basisR D v₀ hF ⟨(x, y, g), h⟩) := by
  subst hp
  rw [basisR_apply]
  refine unitM_isHom D hfinObj ?_
  have := deck_part_le (c := c) v₀ _ x.1 y.1 (deckV_mem D v₀ hF x y ((degW Q v₀).deg p))
  rw [hgt_degW, Int.toNat_natCast] at this
  exact this

/-! ### Products of rays -/

/-- **A nonzero product of rays of `A₀`** is the composite piece. -/
theorem basisR_mul_eq {r s t : RayA0 D v₀} (h : basisR D v₀ hF r * basisR D v₀ hF s = basisR D v₀ hF t) :
    ∃ (hm : s.1.2.1 = r.1.1),
      deckV D v₀ hF s.1.1 s.1.2.1 s.1.2.2 ≫ eqToHom (by rw [hm]) ≫
        deckV D v₀ hF r.1.1 r.1.2.1 r.1.2.2 ≠ 0 ∧
      t.1 = (s.1.1, r.1.2.1, s.1.2.2 * r.1.2.2) := by
  obtain ⟨⟨xr, yr, gr⟩, hr⟩ := r
  obtain ⟨⟨xs, ys, gs⟩, hs⟩ := s
  simp only at *
  rw [basisR_apply, basisR_apply, ← MulOpposite.op_mul] at h
  by_cases hyx : ys = xr
  · subst hyx
    refine ⟨rfl, ?_⟩
    rw [unitM_mul] at h
    simp only [eqToHom_refl, Category.id_comp]
    have hz : deckV D v₀ hF xs ys gs ≫ deckV D v₀ hF ys yr gr ≠ 0 := by
      intro h0
      rw [h0, unitM_zero, MulOpposite.op_zero] at h
      exact (basisR D v₀ hF).ne_zero t h.symm
    refine ⟨hz, ?_⟩
    rcases deckV_mul D v₀ hF xs ys yr gs gr with h0 | h1
    · exact absurd h0 hz
    · have hp : (D0 Q c v₀ D).part (gs * gr) xs yr ≠ ⊥ := by
        intro hb
        apply hz
        have := deckV_mem D v₀ hF xs yr (gs * gr)
        rw [hb, Submodule.mem_bot] at this
        rw [h1, this]
      have ht : basisR D v₀ hF ⟨(xs, yr, gs * gr), hp⟩ = basisR D v₀ hF t := by
        rw [basisR_apply, ← h, h1]
      rw [← (basisR D v₀ hF).injective ht]
  · exfalso
    rw [unitM_mul_ne hyx, MulOpposite.op_zero] at h
    exact (basisR D v₀ hF).ne_zero t h.symm

theorem A0Mult_mul_eq {r s t : RayA0 D v₀} (h : (A0Mult D v₀ hF).mul r s = some t) :
    basisR D v₀ hF r * basisR D v₀ hF s = basisR D v₀ hF t :=
  (RaySys.OfBasis.mulB_eq_some _).1 h

theorem cls_mul_A0 {r s t : RayA0 D v₀} (h : (A0Mult D v₀ hF).mul r s = some t) :
    cls Q c v₀ D t.1 = cls Q c v₀ D r.1 + cls Q c v₀ D s.1 := by
  obtain ⟨hm, hz, ht⟩ := basisR_mul_eq D v₀ hF (A0Mult_mul_eq D v₀ hF h)
  obtain ⟨⟨xr, yr, gr⟩, hr⟩ := r
  obtain ⟨⟨xs, ys, gs⟩, hs⟩ := s
  simp only at hm hz ht
  subst hm
  simp only [eqToHom_refl, Category.id_comp] at hz
  rw [ht, cls_mul (deckV_mem D v₀ hF _ _ _) (deckV_mem D v₀ hF _ _ _) hz, add_comm]

/-- The weight of a ray of `A₀` in `W(P)`. -/
def wtR (t : RayA0 D v₀) : WP Q c v₀ D := cls Q c v₀ D t.1

/-- The length degree on `W(P)`. -/
def degR : WP Q c v₀ D →+ ℤ := (lenW (Q := Q)).res c D

theorem degR_wtR_path {t : RayA0 D v₀} {p : Quiver.Path t.1.1.1 t.1.2.1.1}
    (hp : (degW Q v₀).deg p = t.1.2.2) : degR D v₀ (wtR D v₀ t) = p.length := by
  obtain ⟨⟨x, y, g⟩, ht⟩ := t
  exact deg_cls_path D v₀ ht hp

theorem degR_pos (t : RayA0 D v₀) (h : t ≠ eR D v₀ hF (srcR D v₀ t)) : 0 < degR D v₀ (wtR D v₀ t) := by
  obtain ⟨⟨x, y, g⟩, ht⟩ := t
  obtain ⟨p, hp⟩ := exists_path_of_nz ht
  rw [degR_wtR_path D v₀ (t := ⟨(x, y, g), ht⟩) hp]
  by_contra hl
  have hl0 : p.length = 0 := by omega
  have hxy : x.1 = y.1 := Quiver.Path.eq_of_length_zero p hl0
  have hxy' : x = y := Subtype.ext hxy
  subst hxy'
  have hpn := Quiver.Path.eq_nil_of_length_zero p hl0
  rw [hpn, PathWeight.deg_nil] at hp
  subst hp
  exact h rfl

include hF in
theorem degR_nonneg (t : RayA0 D v₀) : 0 ≤ degR D v₀ (wtR D v₀ t) := by
  obtain ⟨⟨x, y, g⟩, ht⟩ := t
  obtain ⟨p, hp⟩ := exists_path_of_nz ht
  rw [degR_wtR_path D v₀ (t := ⟨(x, y, g), ht⟩) hp]
  omega

include hF in
/-- **Rays of `A₀` with the same endpoints and weight are equal** (one line per length
degree in each corner). -/
theorem sepR_deg (r s : RayA0 D v₀) (h1 : srcR D v₀ r = srcR D v₀ s) (h2 : tgtR D v₀ r = tgtR D v₀ s)
    (hw : degR D v₀ (wtR D v₀ r) = degR D v₀ (wtR D v₀ s)) : r = s := by
  classical
  obtain ⟨⟨xr, yr, gr⟩, hr⟩ := r
  obtain ⟨⟨xs, ys, gs⟩, hs⟩ := s
  change yr = ys at h1
  change xr = xs at h2
  subst h1 h2
  obtain ⟨pr, hpr⟩ := exists_path_of_nz hr
  obtain ⟨ps, hps⟩ := exists_path_of_nz hs
  have hl : pr.length = ps.length := by
    have e1 := degR_wtR_path D v₀ (t := ⟨(xr, yr, gr), hr⟩) hpr
    have e2 := degR_wtR_path D v₀ (t := ⟨(xr, yr, gs), hs⟩) hps
    rw [hw] at e1
    exact_mod_cast e1.symm.trans e2
  have hhr := basisR_isHom D v₀ hF hr hpr
  have hhs := basisR_isHom D v₀ hF hs hps
  rw [← hl] at hhs
  have hcr := basisR_mem_corner D v₀ hF ⟨(xr, yr, gr), hr⟩
  have hcs := basisR_mem_corner D v₀ hF ⟨(xr, yr, gs), hs⟩
  set N := (FpA0 D v₀ hF).corner (k := k) (idxA0 D v₀ hF yr) (idxA0 D v₀ hF xr)
  obtain ⟨w, hw'⟩ := (FpA0 D v₀ hF).lines (lenA0 D hfinObj) (FpA0_he0 D v₀ hF)
    (FpA0_hcorner0 D v₀ hF) hF _ N rfl ((FpA0 D v₀ hF).corner_isEndpoint _ _) pr.length
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 (hw' _ hcr hhr)
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.1 (hw' _ hcs hhs)
  by_contra hne
  have hrep : ∀ t, (basisR D v₀ hF).repr (basisR D v₀ hF t) = Finsupp.single t 1 :=
    fun t ↦ (basisR D v₀ hF).repr_self t
  have key : β • basisR D v₀ hF ⟨(xr, yr, gr), hr⟩ = α • basisR D v₀ hF ⟨(xr, yr, gs), hs⟩ := by
    rw [← hα, ← hβ, smul_smul, smul_smul, mul_comm]
  have e := congrArg (fun z ↦ (basisR D v₀ hF).repr z ⟨(xr, yr, gr), hr⟩) key
  simp only [map_smul, hrep, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at e
  rw [Finsupp.single_apply, if_neg (fun h ↦ hne h.symm), mul_zero] at e
  apply (basisR D v₀ hF).ne_zero ⟨(xr, yr, gs), hs⟩
  rw [← hβ, e, zero_smul]

include hF in
theorem sepR (r s : RayA0 D v₀) (h1 : srcR D v₀ r = srcR D v₀ s) (h2 : tgtR D v₀ r = tgtR D v₀ s)
    (hw : wtR D v₀ r = wtR D v₀ s) : r = s :=
  sepR_deg D v₀ hF r s h1 h2 (by rw [hw])

/-- **The ray table `P = ray A₀`** with weights in `W(P)`. -/
def A0Tab : RaySys.Tab D.PV (RayA0 D v₀) (WP Q c v₀ D) where
  toMult := A0Mult D v₀ hF
  wt := wtR D v₀
  wt_mul _ _ _ h := cls_mul_A0 D v₀ hF h
  deg := degR D v₀
  deg_pos := degR_pos D v₀ hF
  sep := sepR D v₀ hF

/-- **`kP ≅ A₀`** (Proposition 4.14). -/
def thetaA0 : (A0Tab D v₀ hF).Lin k ≃ₐ[k] (Alg D.F0)ᵐᵒᵖ :=
  RaySys.OfBasis.linEquiv (basisR D v₀ hF) (basisR_mult D v₀ hF) (eR D v₀ hF)
    (basisR_complete D v₀ hF) (srcR D v₀) (tgtR D v₀) (basisR_corner D v₀ hF) (srcR_eR D v₀ hF)
    (tgtR_eR D v₀ hF)

theorem thetaA0_b (t : RayA0 D v₀) : thetaA0 D v₀ hF ((A0Tab D v₀ hF).b k t) = basisR D v₀ hF t :=
  RaySys.OfBasis.linEquiv_b (basisR D v₀ hF) (basisR_mult D v₀ hF) (eR D v₀ hF)
    (basisR_complete D v₀ hF) (srcR D v₀) (tgtR D v₀) (basisR_corner D v₀ hF) (srcR_eR D v₀ hF)
    (tgtR_eR D v₀ hF) t

theorem A0Tab_isRepresentationFinite : IsRepresentationFinite k ((A0Tab D v₀ hF).Lin k) :=
  isRepresentationFinite_of_surjective (thetaA0 D v₀ hF).symm.toAlgHom
    (thetaA0 D v₀ hF).symm.surjective hF

/-- **Setting 8.4 for `A₀`.** -/
def A0Sys : RaySys.Sys D.PV (RayA0 D v₀) (WP Q c v₀ D) :=
  (A0Tab D v₀ hF).toSys k (A0Tab_isRepresentationFinite D v₀ hF)

/-! ### Other weight lattices

Any mesh weight `Wt` with values in `L`, with a homomorphism `dg : L → ℤ` recovering the
length, gives ray weights `Wt.res [x, y, g]` making the same table a ray table with
weights in `L`. -/

section Lattice

variable {L' : Type} [AddCommGroup L'] (Wt : MeshWt Q L') (dg : L' →+ ℤ)

/-- The ray weights in `L'`. -/
def wtLat (t : RayA0 D v₀) : L' := Wt.res c D (cls Q c v₀ D t.1)

theorem dg_wtLat (hdg : dg.comp (Wt.res (v₀ := v₀) c D) = (lenW (Q := Q)).res (v₀ := v₀) c D) (t : RayA0 D v₀) : dg (wtLat D v₀ Wt t) = degR D v₀ (wtR D v₀ t) := by
  rw [wtLat, degR, wtR, ← hdg]; rfl

/-- **The ray table of `A₀` with weights in `L'`.** -/
def A0TabL (hdg : dg.comp (Wt.res (v₀ := v₀) c D) = (lenW (Q := Q)).res (v₀ := v₀) c D) : RaySys.Tab D.PV (RayA0 D v₀) L' where
  toMult := A0Mult D v₀ hF
  wt := wtLat D v₀ Wt
  wt_mul _ _ _ h := by rw [wtLat, wtLat, wtLat, cls_mul_A0 D v₀ hF h, map_add]
  deg := dg
  deg_pos t h := by rw [dg_wtLat D v₀ Wt dg hdg]; exact degR_pos D v₀ hF t h
  sep r s h1 h2 hw := sepR_deg D v₀ hF r s h1 h2 (by
    rw [← dg_wtLat D v₀ Wt dg hdg, ← dg_wtLat D v₀ Wt dg hdg, hw])

/-- `kP ≅ A₀` for the table with weights in `L'`. -/
def thetaA0L (hdg : dg.comp (Wt.res (v₀ := v₀) c D) = (lenW (Q := Q)).res (v₀ := v₀) c D) : (A0TabL D v₀ hF Wt dg hdg).Lin k ≃ₐ[k] (Alg D.F0)ᵐᵒᵖ := thetaA0 D v₀ hF

theorem thetaA0L_b (hdg : dg.comp (Wt.res (v₀ := v₀) c D) = (lenW (Q := Q)).res (v₀ := v₀) c D) (t : RayA0 D v₀) :
    thetaA0L D v₀ hF Wt dg hdg ((A0TabL D v₀ hF Wt dg hdg).b k t) = basisR D v₀ hF t :=
  thetaA0_b D v₀ hF t

theorem A0TabL_isRepresentationFinite (hdg : dg.comp (Wt.res (v₀ := v₀) c D) = (lenW (Q := Q)).res (v₀ := v₀) c D) :
    IsRepresentationFinite k ((A0TabL D v₀ hF Wt dg hdg).Lin k) :=
  A0Tab_isRepresentationFinite D v₀ hF

/-- **Setting 8.4 for `A₀` with weights in `L'`.** -/
def A0SysL (hdg : dg.comp (Wt.res (v₀ := v₀) c D) = (lenW (Q := Q)).res (v₀ := v₀) c D) : RaySys.Sys D.PV (RayA0 D v₀) L' :=
  (A0TabL D v₀ hF Wt dg hdg).toSys k (A0TabL_isRepresentationFinite D v₀ hF Wt dg hdg)

end Lattice

end MeshWalk

end MultiplicativeBasisDeformations
