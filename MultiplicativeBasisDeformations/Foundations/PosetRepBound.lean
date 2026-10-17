import MultiplicativeBasisDeformations.Foundations.PosetRepInfinite
import MultiplicativeBasisDeformations.Foundations.TableBound

/-!
# Lemma 8.8 with one zero relation

`lem:dimension-infinity` with `F = d_p d_r` for a single zero relation `p → m → r` of length
two in a poset with unique paths: the linearization of the bound incidence table
(`RaySys.incZ`, zero set `{(x, z) | x ≤ p, r ≤ z}`) is representation-infinite when
`∑ d_v² + d_p d_r ≤ ∑_{x → y} d_x d_y` and `d ≠ 0`. This is the form needed for Case 2 of
Lemma 8.11 (`local-ray-geometry.tex`, `N = 22`, `D = 21`, `F = 1`).

The module of a point of the zero set is a module over the bound algebra, through the
matrix units of the incidence algebra; isomorphisms of such modules are conjugations
(`conj_of_iso`), and `OrbitDim.orbits_not_finite` applies with the `F` entries of the
composite along the relation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

namespace PosetRep

universe u

variable {k : Type u} [Field k] {P : Type} [PartialOrder P] [Fintype P] [DecidableEq P]
  [LocallyFiniteOrder P] [DecidableLE P] {E : P → P → Prop}
  (d : P → ℕ) (hE : ∀ x y, E x y → x < y) (huniq : ∀ x y, Subsingleton (EPath E x y))
  (hex : ∀ x y, x ≤ y → Nonempty (EPath E x y))
  {p m r : P} (hpm : E p m) (hmr : E m r)

/-- The zero set of the relation `p → m → r`. -/
def Zr (p r : P) (x z : P) : Prop := x ≤ p ∧ r ≤ z

instance (p r : P) : DecidableRel (Zr p r) := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

include hE hpm hmr in
theorem zr_zeroSet : RaySys.ZeroSet P (Zr p r) :=
  ⟨fun _ _ _ _ hz h1 h2 ↦ ⟨h1.trans hz.1, hz.2.trans h2⟩, fun a hz ↦
    (hz.1.trans_lt ((hE _ _ hpm).trans (hE _ _ hmr))).not_ge hz.2⟩

variable {M : ∀ x y, E x y → (Sp k d x →ₗ[k] Sp k d y)}

include hE huniq hpm hmr in
/-- **The transport vanishes on the zero set.** -/
theorem T_zero (hM : M m r hmr ∘ₗ M p m hpm = 0) {x z : P} (hz : Zr p r x z) :
    T d hex M x z = 0 := by
  have hxp := hz.1
  have hrz := hz.2
  have hpm' := (hE _ _ hpm).le
  have hmr' := (hE _ _ hmr).le
  rw [T_trans d hE huniq hex M (hxp.trans (hpm'.trans hmr')) hrz,
    T_trans d hE huniq hex M hxp (hpm'.trans hmr'), T_trans d hE huniq hex M hpm' hmr',
    T_arrow d hE huniq hex M hpm, T_arrow d hE huniq hex M hmr, hM]
  simp

include hE huniq hpm hmr in
theorem act_sgl_zero (hM : M m r hmr ∘ₗ M p m hpm = 0) {x z : P} (hxz : x ≤ z)
    (hz : Zr p r x z) (w : ∀ v, Sp k d v) : act d hex M (sgl x z hxz) w = 0 := by
  rw [act_sgl, T_zero d hE huniq hex hpm hmr hM hz]
  simp

/-! ### The bound algebra acting on a point of the zero set -/

theorem sgl_mul (x y y' z : P) (h : x ≤ y) (h' : y' ≤ z) :
    (sgl x y h : IncidenceAlgebra k P) * sgl y' z h' =
      if hy : y = y' then sgl x z (h.trans (hy ▸ h')) else 0 := by
  ext a c hac
  rw [IncidenceAlgebra.mul_apply]
  simp only [sgl, IncidenceAlgebra.coe_mk]
  split_ifs with hy
  · subst hy
    simp only [IncidenceAlgebra.coe_mk]
    by_cases hac' : a = x ∧ c = z
    · obtain ⟨rfl, rfl⟩ := hac'
      rw [if_pos ⟨rfl, rfl⟩, Finset.sum_eq_single y]
      · simp
      · intro b _ hb; rw [if_neg (fun h ↦ hb h.2)]; simp
      · intro hy; exfalso; exact hy (Finset.mem_Icc.2 ⟨h, h'⟩)
    · rw [if_neg hac']
      refine Finset.sum_eq_zero fun b _ ↦ ?_
      by_cases h1 : a = x ∧ b = y
      · rw [if_pos h1, if_neg (fun h2 ↦ hac' ⟨h1.1, h2.2⟩), mul_zero]
      · rw [if_neg h1, zero_mul]
  · rw [IncidenceAlgebra.zero_apply]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    by_cases h1 : a = x ∧ b = y
    · rw [if_pos h1, if_neg (fun h2 ↦ hy (h1.2.symm.trans h2.1)), mul_zero]
    · rw [if_neg h1, zero_mul]

variable (M) in
/-- The action of an incidence function, as an endomorphism of the carrier. -/
def actE (a : IncidenceAlgebra k P) : Module.End k (∀ v, Sp k d v) where
  toFun := act d hex M a
  map_add' v w := by
    funext y
    simp only [act, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    change _ • T d hex M x y (v x + w x) = _
    rw [map_add, smul_add]
  map_smul' c w := by
    funext y
    simp only [act, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    change _ • T d hex M x y (c • w x) = _
    rw [map_smul, smul_comm]

theorem actE_apply (a : IncidenceAlgebra k P) (w : ∀ v, Sp k d v) :
    actE d hex M a w = act d hex M a w := rfl

variable (M) in
/-- The action is linear in the incidence function. -/
def actA : IncidenceAlgebra k P →ₗ[k] Module.End k (∀ v, Sp k d v) where
  toFun := actE d hex M
  map_add' a b := by
    ext w y; simp [actE_apply, act, add_smul, Finset.sum_add_distrib, IncidenceAlgebra.add_apply]
  map_smul' c a := by
    ext w y
    simp [actE_apply, act, Finset.smul_sum, mul_smul, IncidenceAlgebra.constSMul_apply,
      Finset.mul_sum]

variable (k) in
/-- The bound algebra of the relation. -/
abbrev BAlg := (RaySys.incZ (zr_zeroSet hE hpm hmr)).Lin k

/-- Matrix units of the bound algebra in the incidence algebra. -/
def ιB : BAlg k hE hpm hmr →ₗ[k] IncidenceAlgebra k P :=
  ((RaySys.incZ (zr_zeroSet hE hpm hmr)).basis k).constr k fun q ↦ sgl q.1.1 q.1.2 q.2.1

theorem ιB_b (q : RaySys.IPZ P (Zr p r)) :
    ιB hE hpm hmr ((RaySys.incZ (zr_zeroSet hE hpm hmr)).b k q) = sgl q.1.1 q.1.2 q.2.1 := by
  rw [ιB, ← RaySys.Mult.basis_apply, Module.Basis.constr_basis]

theorem ιB_one : ιB (k := k) hE hpm hmr 1 = 1 := by
  rw [← (RaySys.incZ (zr_zeroSet hE hpm hmr)).sum_b_e k, map_sum]
  simp only [ιB_b]
  ext a c hac
  rw [IncidenceAlgebra.one_apply, RaySys.sum_apply']
  simp only [sgl, IncidenceAlgebra.coe_mk]
  by_cases h : a = c
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single a]
    · exact if_pos ⟨rfl, rfl⟩
    · intro b _ hb; rw [if_neg (fun h ↦ hb h.1.symm)]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    rw [if_neg]; rintro ⟨rfl, rfl⟩; exact h rfl

variable (M) in
/-- The action of the bound algebra. -/
def ψ0 : BAlg k hE hpm hmr →ₗ[k] Module.End k (∀ v, Sp k d v) := actA d hex M ∘ₗ ιB hE hpm hmr

include huniq in
theorem ψ0_mul (hM : M m r hmr ∘ₗ M p m hpm = 0) (b b' : BAlg k hE hpm hmr) :
    ψ0 d hE hex hpm hmr M (b * b') = ψ0 d hE hex hpm hmr M b' * ψ0 d hE hex hpm hmr M b := by
  have h : (LinearMap.mul k _).compr₂ (ψ0 d hE hex hpm hmr M) =
      ((LinearMap.mul k _).flip.compl₁₂ (ψ0 d hE hex hpm hmr M) (ψ0 d hE hex hpm hmr M)) := by
    refine LinearMap.ext_basis ((RaySys.incZ (zr_zeroSet hE hpm hmr)).basis k)
      ((RaySys.incZ (zr_zeroSet hE hpm hmr)).basis k) fun q q' ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
      LinearMap.flip_apply, RaySys.Mult.basis_apply, RaySys.Mult.b_mul]
    apply LinearMap.ext; intro w
    rw [Module.End.mul_apply]
    simp only [ψ0, LinearMap.coe_comp, Function.comp_apply, ιB_b]
    change _ = act d hex M (sgl q'.1.1 q'.1.2 q'.2.1) (act d hex M (sgl q.1.1 q.1.2 q.2.1) w)
    rw [← act_mul d hE huniq hex M, sgl_mul]
    by_cases hc : q.1.2 = q'.1.1 ∧ ¬ Zr p r q.1.1 q'.1.2
    · rw [RaySys.incZ_mul_of _ q q' hc.1 hc.2, dif_pos hc.1]
      simp only [Option.elim_some]
      change act d hex M (ιB hE hpm hmr _) w = _
      rw [ιB_b]
    · rw [RaySys.incZ_mul_none _ q q' hc]
      simp only [Option.elim_none, map_zero, LinearMap.zero_apply]
      split_ifs with hy
      · have hz : Zr p r q.1.1 q'.1.2 := by
          by_contra hz; exact hc ⟨hy, hz⟩
        exact (act_sgl_zero d hE huniq hex hpm hmr hM _ hz w).symm
      · funext v; simp [act]
  exact congrArg (fun B ↦ B b b') h

include huniq in
theorem ψ0_one' : ψ0 d hE hex hpm hmr M 1 = 1 := by
  apply LinearMap.ext; intro w
  simp only [ψ0, LinearMap.coe_comp, Function.comp_apply, ιB_one]
  exact act_one d hE huniq hex M w

/-- **The bound algebra acting on a point of the zero set** (a right module). -/
def ψ (hM : M m r hmr ∘ₗ M p m hpm = 0) :
    (BAlg k hE hpm hmr)ᵐᵒᵖ →+* Module.End k (∀ v, Sp k d v) where
  toFun b := ψ0 d hE hex hpm hmr M b.unop
  map_one' := ψ0_one' d hE huniq hex hpm hmr
  map_mul' a b := ψ0_mul d hE huniq hex hpm hmr hM b.unop a.unop
  map_zero' := map_zero _
  map_add' _ _ := map_add _ _ _

/-- **The module of a point of the zero set** over the bound algebra. -/
def repObjB (hM : M m r hmr ∘ₗ M p m hpm = 0) : RightModuleCat (BAlg k hE hpm hmr) :=
  @ModuleCat.of _ _ (∀ v, Sp k d v) _ (Module.compHom _ (ψ d hE huniq hex hpm hmr hM))

theorem repObjB_smul (hM : M m r hmr ∘ₗ M p m hpm = 0) (b : (BAlg k hE hpm hmr)ᵐᵒᵖ)
    (w : repObjB d hE huniq hex hpm hmr hM) :
    (b • w : repObjB d hE huniq hex hpm hmr hM) =
      act d hex M (ιB hE hpm hmr b.unop) (w : ∀ v, Sp k d v) := rfl

/-- Elements of the module of a point as tuples of vectors. -/
def toP {hM : M m r hmr ∘ₗ M p m hpm = 0} (w : repObjB d hE huniq hex hpm hmr hM) :
    ∀ v, Sp k d v := w

theorem toP_smul {hM : M m r hmr ∘ₗ M p m hpm = 0} (c : k)
    (w : repObjB d hE huniq hex hpm hmr hM) :
    toP d hE huniq hex hpm hmr (c • w) = c • toP d hE huniq hex hpm hmr w := by
  show act d hex M (ιB hE hpm hmr (algebraMap k (BAlg k hE hpm hmr) c)) (toP d hE huniq hex hpm hmr w) = _
  rw [Algebra.algebraMap_eq_smul_one, map_smul, ιB_one]
  change actA d hex M (c • 1) _ = _
  rw [map_smul, LinearMap.smul_apply]
  change c • act d hex M 1 _ = _
  rw [act_one d hE huniq hex M]

/-- The identification with `∏ k^{d v}` is `k`-linear. -/
def toPiB (hM : M m r hmr ∘ₗ M p m hpm = 0) :
    repObjB d hE huniq hex hpm hmr hM →ₗ[k] (∀ v, Sp k d v) where
  toFun := toP d hE huniq hex hpm hmr
  map_add' _ _ := rfl
  map_smul' c w := toP_smul d hE huniq hex hpm hmr c w

theorem repObjB_finite (hM : M m r hmr ∘ₗ M p m hpm = 0) :
    Module.Finite k (repObjB d hE huniq hex hpm hmr hM) :=
  Module.Finite.of_injective (toPiB d hE huniq hex hpm hmr hM) fun _ _ h ↦ h

theorem finrank_repObjB_le (hM : M m r hmr ∘ₗ M p m hpm = 0) :
    Module.finrank k (repObjB d hE huniq hex hpm hmr hM) ≤ ∑ v, d v := by
  have := LinearMap.finrank_le_finrank_of_injective
    (f := toPiB d hE huniq hex hpm hmr hM) fun _ _ h ↦ h
  refine this.trans (le_of_eq ?_)
  rw [Module.finrank_pi_fintype]
  simp

/-- An incidence function as a combination of matrix units. -/
theorem incidence_eq_sum (a : IncidenceAlgebra k P) :
    a = ∑ q : {x : P × P // x.1 ≤ x.2}, a q.1.1 q.1.2 • sgl q.1.1 q.1.2 q.2 := by
  ext x z hxz
  rw [RaySys.sum_apply']
  simp only [IncidenceAlgebra.constSMul_apply, sgl, IncidenceAlgebra.coe_mk, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single ⟨(x, z), hxz⟩]
  · simp
  · rintro ⟨⟨x', z'⟩, h'⟩ _ hne
    rw [if_neg]
    rintro ⟨rfl, rfl⟩; exact hne rfl
  · simp

/-- Tuples of vectors as elements of the module of a point. -/
def ofP {hM : M m r hmr ∘ₗ M p m hpm = 0} (w : ∀ v, Sp k d v) :
    repObjB d hE huniq hex hpm hmr hM := w

theorem act_eq_sum (a : IncidenceAlgebra k P) (w : ∀ v, Sp k d v) :
    act d hex M a w = ∑ q : {x : P × P // x.1 ≤ x.2}, a q.1.1 q.1.2 • act d hex M (sgl q.1.1 q.1.2 q.2) w := by
  conv_lhs => rw [incidence_eq_sum a]
  change actA d hex M _ w = _
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [map_smul, LinearMap.smul_apply]; rfl

section Points

variable [DecidableRel E]

/-- The zero condition for a point. -/
abbrev ZC (y : OrbitDim.Coord d (src (E := E)) tgt → k) : Prop :=
  Mpt d y m r hmr ∘ₗ Mpt d y p m hpm = 0

include hE huniq in
/-- A module map between points of the zero set commutes with the incidence algebra. -/
theorem hom_act (x y : OrbitDim.Coord d (src (E := E)) tgt → k)
    (hx : ZC d hpm hmr x) (hy : ZC d hpm hmr y)
    (φ : repObjB d hE huniq hex hpm hmr hx ⟶ repObjB d hE huniq hex hpm hmr hy)
    (a : IncidenceAlgebra k P) (w : ∀ v, Sp k d v) :
    toP d hE huniq hex hpm hmr (φ (ofP d hE huniq hex hpm hmr (act d hex (Mpt d x) a w))) =
      act d hex (Mpt d y) a (toP d hE huniq hex hpm hmr (φ (ofP d hE huniq hex hpm hmr w))) := by
  set F : (∀ v, Sp k d v) →+ (∀ v, Sp k d v) :=
    { toFun := fun w ↦ toP d hE huniq hex hpm hmr (φ (ofP d hE huniq hex hpm hmr w))
      map_zero' := map_zero φ.hom
      map_add' := fun w w' ↦ map_add φ.hom _ _ }
  have hFsmul : ∀ (c : k) w, F (c • w) = c • F w := fun c w ↦ by
    change toP d hE huniq hex hpm hmr (φ (ofP d hE huniq hex hpm hmr (c • w))) = _
    rw [show ofP d hE huniq hex hpm hmr (hM := hx) (c • w) = c • ofP d hE huniq hex hpm hmr w from
      (toP_smul d hE huniq hex hpm hmr (hM := hx) c (ofP d hE huniq hex hpm hmr w)).symm]
    rw [show φ (c • ofP d hE huniq hex hpm hmr w) = c • φ (ofP d hE huniq hex hpm hmr w) from
      φ.hom.map_smul (algebraMap k (BAlg k hE hpm hmr)ᵐᵒᵖ c) _, toP_smul]
    rfl
  have hsgl : ∀ (q : {z : P × P // z.1 ≤ z.2}) w,
      F (act d hex (Mpt d x) (sgl q.1.1 q.1.2 q.2) w) =
        act d hex (Mpt d y) (sgl q.1.1 q.1.2 q.2) (F w) := by
    intro q w
    by_cases hz : Zr p r q.1.1 q.1.2
    · rw [act_sgl_zero d hE huniq hex hpm hmr hx q.2 hz, act_sgl_zero d hE huniq hex hpm hmr hy q.2 hz,
        map_zero]
    · set b := (RaySys.incZ (zr_zeroSet hE hpm hmr)).b k ⟨q.1, q.2, hz⟩
      have e1 : act d hex (Mpt d x) (sgl q.1.1 q.1.2 q.2) w =
          toP d hE huniq hex hpm hmr (MulOpposite.op b • ofP d hE huniq hex hpm hmr (hM := hx) w) := by
        change _ = act d hex (Mpt d x) (ιB hE hpm hmr b) w
        rw [ιB_b]
      have e2 : act d hex (Mpt d y) (sgl q.1.1 q.1.2 q.2) (F w) =
          toP d hE huniq hex hpm hmr (MulOpposite.op b • φ (ofP d hE huniq hex hpm hmr w)) := by
        change _ = act d hex (Mpt d y) (ιB hE hpm hmr b) _
        rw [ιB_b]; rfl
      rw [e1, e2]
      change toP d hE huniq hex hpm hmr (φ (MulOpposite.op b • ofP d hE huniq hex hpm hmr w)) = _
      rw [φ.hom.map_smul]
  change F (act d hex (Mpt d x) a w) = act d hex (Mpt d y) a (F w)
  rw [act_eq_sum, act_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [hFsmul, hsgl]

include hE huniq in
/-- **Isomorphic modules over the bound algebra are conjugate points.** -/
theorem conj_of_isoB (x y : OrbitDim.Coord d (src (E := E)) tgt → k)
    (hx : ZC d hpm hmr x) (hy : ZC d hpm hmr y)
    (L : repObjB d hE huniq hex hpm hmr hx ≅ repObjB d hE huniq hex hpm hmr hy) :
    ∃ g : ∀ v, GL (Fin (d v)) k, y = OrbitDim.act g x := by
  set Lf : (∀ v, Sp k d v) → (∀ v, Sp k d v) := fun w ↦ toP d hE huniq hex hpm hmr (L.hom (ofP d hE huniq hex hpm hmr w))
  set Lg : (∀ v, Sp k d v) → (∀ v, Sp k d v) := fun w ↦ toP d hE huniq hex hpm hmr (L.inv (ofP d hE huniq hex hpm hmr w))
  have hLf_add : ∀ w w', Lf (w + w') = Lf w + Lf w' := fun w w' ↦ map_add L.hom.hom _ _
  have hLsmul : ∀ (c : k) (z : repObjB d hE huniq hex hpm hmr hx), L.hom (c • z) = c • L.hom z :=
    fun c z ↦ L.hom.hom.map_smul (algebraMap k (BAlg k hE hpm hmr)ᵐᵒᵖ c) z
  have hofP : ∀ (c : k) w, ofP d hE huniq hex hpm hmr (hM := hx) (c • w) =
      c • ofP d hE huniq hex hpm hmr w := fun c w ↦
    (toP_smul d hE huniq hex hpm hmr (hM := hx) c (ofP d hE huniq hex hpm hmr w)).symm
  have hLf_smul : ∀ (c : k) w, Lf (c • w) = c • Lf w := fun c w ↦ by
    change toP d hE huniq hex hpm hmr (L.hom (ofP d hE huniq hex hpm hmr (c • w))) = _
    rw [hofP, hLsmul, toP_smul]
  let e : repObj d hE huniq hex (Mpt d x) ≃ₗ[(IncidenceAlgebra k P)ᵐᵒᵖ]
      repObj d hE huniq hex (Mpt d y) :=
    { toFun := Lf
      invFun := Lg
      map_add' := hLf_add
      map_smul' := fun a w ↦ hom_act d hE huniq hex hpm hmr x y hx hy L.hom a.unop w
      left_inv := fun w ↦ by
        change toP d hE huniq hex hpm hmr ((L.hom ≫ L.inv) (ofP d hE huniq hex hpm hmr w)) = w
        rw [L.hom_inv_id]; rfl
      right_inv := fun w ↦ by
        change toP d hE huniq hex hpm hmr ((L.inv ≫ L.hom) (ofP d hE huniq hex hpm hmr w)) = w
        rw [L.inv_hom_id]; rfl }
  exact conj_of_iso d hE huniq hex x y e

/-- The arrow `m → r`. -/
abbrev amr : Arr E := ⟨(m, r), hmr⟩

/-- The arrow `p → m`. -/
abbrev apm : Arr E := ⟨(p, m), hpm⟩

/-- The entries of the composite along the relation, as polynomials. -/
def relPoly (ij : Fin (d r * d p)) : MvPolynomial (OrbitDim.Coord d (src (E := E)) tgt) k :=
  ∑ l : Fin (d m), MvPolynomial.X ⟨amr hmr, (finProdFinEquiv.symm ij).1, l⟩ *
    MvPolynomial.X ⟨apm hpm, l, (finProdFinEquiv.symm ij).2⟩

theorem eval_relPoly (y : OrbitDim.Coord d (src (E := E)) tgt → k) (ij : Fin (d r * d p)) :
    MvPolynomial.eval y (relPoly d hpm hmr ij) =
      (OrbitDim.mat y (amr hmr) * OrbitDim.mat y (apm hpm))
        (finProdFinEquiv.symm ij).1 (finProdFinEquiv.symm ij).2 := by
  simp [relPoly, Matrix.mul_apply, OrbitDim.mat]

theorem zc_iff (y : OrbitDim.Coord d (src (E := E)) tgt → k) :
    ZC d hpm hmr y ↔ ∀ ij, MvPolynomial.eval y (relPoly d hpm hmr ij) = 0 := by
  have e : Mpt d y m r hmr ∘ₗ Mpt d y p m hpm =
      Matrix.toLin' (OrbitDim.mat y (amr hmr) * OrbitDim.mat y (apm hpm)) := by
    simp only [Mpt, Matrix.toLin'_mul]
  rw [ZC, e, show (0 : (Fin (d p) → k) →ₗ[k] (Fin (d r) → k)) = Matrix.toLin' 0 by simp,
    Matrix.toLin'.injective.eq_iff]
  constructor
  · intro h ij; rw [eval_relPoly, h]; rfl
  · intro h; ext i j
    have := h (finProdFinEquiv (i, j))
    rw [eval_relPoly, Equiv.symm_apply_apply] at this
    exact this

theorem relPoly_stab (g : ∀ v, GL (Fin (d v)) k) (y : OrbitDim.Coord d (src (E := E)) tgt → k)
    (hy : ∀ ij, MvPolynomial.eval y (relPoly d hpm hmr ij) = 0) (ij : Fin (d r * d p)) :
    MvPolynomial.eval (OrbitDim.act g y) (relPoly d hpm hmr ij) = 0 := by
  have h0 : OrbitDim.mat y (amr hmr) * OrbitDim.mat y (apm hpm) = 0 := by
    ext i j
    have := hy (finProdFinEquiv (i, j))
    rw [eval_relPoly, Equiv.symm_apply_apply] at this
    exact this
  rw [eval_relPoly, OrbitDim.mat_act, OrbitDim.mat_act]
  change ((g r).val * OrbitDim.mat y (amr hmr) * ((g m)⁻¹).val *
    ((g m).val * OrbitDim.mat y (apm hpm) * ((g p)⁻¹).val)) _ _ = 0
  rw [show (g r).val * OrbitDim.mat y (amr hmr) * ((g m)⁻¹).val *
      ((g m).val * OrbitDim.mat y (apm hpm) * ((g p)⁻¹).val) =
      (g r).val * (OrbitDim.mat y (amr hmr) * OrbitDim.mat y (apm hpm)) * ((g p)⁻¹).val by
    simp only [Matrix.mul_assoc]
    congr 2
    rw [← Matrix.mul_assoc ((g m)⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul]]
  rw [h0]; simp

/-- The labelled biproducts of the bound algebra. -/
def ObjB {N : ℕ} (X : Fin N → RightModuleCat (BAlg k hE hpm hmr)) (B : ℕ)
    (τ : Σ m : Fin (B + 1), (Fin m → Fin N)) : RightModuleCat (BAlg k hE hpm hmr) :=
  ⨁ fun j : Fin τ.1 ↦ X (τ.2 j)

include huniq hex in
/-- **Lemma 8.8 with one zero relation**: if `d ≠ 0` and
`∑ d_v² + d_p d_r ≤ ∑_{x → y} d_x d_y`, the bound incidence algebra is
representation-infinite. -/
theorem not_isRepresentationFinite_bound [IsAlgClosed k] (hd : ∃ v, 0 < d v)
    (hN : ∑ v, d v ^ 2 + d r * d p ≤ ∑ a : Arr E, d (tgt a) * d (src a)) :
    ¬ IsRepresentationFinite k (BAlg k hE hpm hmr) := by
  classical
  intro hA
  obtain ⟨N, X, -, hX⟩ := exists_labels_iso hA
  set B := ∑ v, d v
  have hfin : ∀ (y : OrbitDim.Coord d (src (E := E)) tgt → k) (hy : ZC d hpm hmr y),
      Module.Finite k (repObjB d hE huniq hex hpm hmr hy) := fun y hy ↦
    repObjB_finite d hE huniq hex hpm hmr hy
  have hlab : ∀ (y : OrbitDim.Coord d (src (E := E)) tgt → k) (hy : ZC d hpm hmr y),
      ∃ τ : Σ m : Fin (B + 1), (Fin m → Fin N),
        Nonempty (repObjB d hE huniq hex hpm hmr hy ≅ ObjB hE hpm hmr X B τ) := by
    intro y hy
    obtain ⟨n, l, hn, hiso⟩ := hX _ (hfin y hy)
    exact ⟨⟨⟨n, Nat.lt_succ_of_le (hn.trans (finrank_repObjB_le d hE huniq hex hpm hmr hy))⟩, l⟩,
      hiso⟩
  let lab : (OrbitDim.Coord d (src (E := E)) tgt → k) → Σ m : Fin (B + 1), (Fin m → Fin N) :=
    fun y ↦ if hy : ZC d hpm hmr y then (hlab y hy).choose else ⟨0, Fin.elim0⟩
  let rep : (Σ m : Fin (B + 1), (Fin m → Fin N)) → (OrbitDim.Coord d (src (E := E)) tgt → k) :=
    fun τ ↦ if h : ∃ y, ZC d hpm hmr y ∧ lab y = τ then h.choose else 0
  refine OrbitDim.orbits_not_finite (k := k) (d r * d p) (relPoly d hpm hmr) (fun ij ↦ ?_)
    (fun g y hy ij ↦ relPoly_stab d hpm hmr g y hy ij) hd ?_ (Finset.univ.image rep)
    fun y hy ↦ ?_
  · simp [relPoly]
  · simp only [OrbitDim.Coord, OrbitDim.GC, Fintype.card_sigma, Fintype.card_prod,
      Fintype.card_fin]
    simpa [sq] using hN
  · have hzy : ZC d hpm hmr y := (zc_iff d hpm hmr y).2 hy
    have hex' : ∃ y', ZC d hpm hmr y' ∧ lab y' = lab y := ⟨y, hzy, rfl⟩
    have hrep : rep (lab y) = hex'.choose := dif_pos hex'
    obtain ⟨hz', hl'⟩ := hex'.choose_spec
    refine ⟨rep (lab y), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    rw [hrep]
    have e1 : lab hex'.choose = (hlab _ hz').choose := dif_pos hz'
    have e2 : lab y = (hlab y hzy).choose := dif_pos hzy
    have i1 := (hlab _ hz').choose_spec.some
    have i2 := (hlab y hzy).choose_spec.some
    exact conj_of_isoB d hE huniq hex hpm hmr _ y hz' hzy
      (i1 ≪≫ eqToIso (congrArg (ObjB hE hpm hmr X B) (e1.symm.trans (hl'.trans e2))) ≪≫ i2.symm)

end Points

end PosetRep

end MultiplicativeBasisDeformations
