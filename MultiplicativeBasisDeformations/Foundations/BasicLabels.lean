module

public import MultiplicativeBasisDeformations.Foundations.Peirce
public import MultiplicativeBasisDeformations.Foundations.EndpointChains
public import MultiplicativeBasisDeformations.Foundations.Exchange
public import MultiplicativeBasisDeformations.Foundations.ProjectiveIdempotents

/-!
# Indecomposable projectives of a basic algebra

For Corollary 5.5 (`mesh-deformations.tex`) we identify a basic algebra
`A` with the algebra `A₀` of its projective labels. Here: the right ideal `eA` of
a primitive idempotent is isomorphic to `e_i A` for one idempotent of a complete
set (`exists_iso_ideal`: some `e e_i e` is a unit of the local corner `eAe`, so
`eA` is a retract of `e_i A`), and for a basic algebra distinct `e_i A` are not
isomorphic (`eq_of_iso_ideal`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.Magnitude.RightModule

namespace MultiplicativeBasisDeformations

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]

/-! ### The corner ring of a primitive idempotent is local -/

variable (k) in
theorem corner_isLocalRing_of_primitive {R : Type*} [Ring R] [Algebra k R] [FiniteDimensional k R]
    {e : R} (hp : IsPrimitiveIdempotent e) : IsLocalRing hp.1.Corner := by
  have he := hp.1
  haveI : Nontrivial he.Corner := ⟨⟨1, 0, fun h ↦ hp.2.1 (by
    have := congrArg (cornerVal he) h
    simpa using this)⟩⟩
  haveI : FiniteDimensional k he.Corner := corner_finite he
  apply MBDVendor.Magnitude.finiteDimensional_isLocalRing_of_idempotents (k := k)
  intro c hc
  have hcA : IsIdempotentElem (cornerVal he c) := by
    change cornerVal he c * cornerVal he c = cornerVal he c
    rw [← corner_mul_val, hc.eq]
  rcases hp.2.2 _ hcA (corner_mul_left he c) (corner_mul_right he c) with h | h
  · left; exact corner_ext he (by simpa using h)
  · right; exact corner_ext he (by simpa using h)

/-! ### Endomorphisms of `eA` -/

/-- The generator of `eA`. -/
def genOf {a : A} (ha : IsIdempotentElem a) : rightIdeal a := ⟨a, ⟨a, ha.eq⟩⟩

theorem hom_gen_val {a b : A} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (f : idealMod a ⟶ idealMod b) : b * (f.hom (genOf ha)).1 * a = (f.hom (genOf ha)).1 := by
  have h1 : b * (f.hom (genOf ha)).1 = (f.hom (genOf ha)).1 := ideal_fixed hb _
  have h2 : (f.hom (genOf ha)).1 * a = (f.hom (genOf ha)).1 := by
    have := f.hom.map_smul (MulOpposite.op a) (genOf ha)
    have h := congrArg Subtype.val this
    have hg : MulOpposite.op a • genOf ha = genOf ha := Subtype.ext ha.eq
    rw [hg] at h
    exact h.symm
  rw [h1, h2]

theorem hom_apply_eq {a b : A} (ha : IsIdempotentElem a) (f : idealMod a ⟶ idealMod b)
    (m : rightIdeal a) : (f.hom m).1 = (f.hom (genOf ha)).1 * m.1 := by
  have hm : m = MulOpposite.op m.1 • genOf ha := Subtype.ext (ideal_fixed ha m).symm
  conv_lhs => rw [hm, LinearMap.map_smul]
  rfl

/-- **`End(eA) ≅ eAe`.** -/
def endEquivCorner {a : A} (ha : IsIdempotentElem a) : End (idealMod a) ≃+* ha.Corner where
  toFun f := cornerMk ha (f.hom (genOf ha)).1 ⟨(f.hom (genOf ha)).1, hom_gen_val ha ha f⟩
  invFun c := ModuleCat.ofHom (lmul ha (cornerVal ha c) (corner_mul_left ha c))
  left_inv f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ Subtype.ext ?_)
    change (f.hom (genOf ha)).1 * m.1 = (f.hom m).1
    rw [hom_apply_eq ha f m]
  right_inv c := by
    apply corner_ext ha
    change cornerVal ha c * a = cornerVal ha c
    exact corner_mul_right ha c
  map_mul' f g := by
    apply corner_ext ha
    rw [corner_mul_val]
    change ((f.hom (g.hom (genOf ha))).1) = (f.hom (genOf ha)).1 * (g.hom (genOf ha)).1
    rw [hom_apply_eq ha f]
  map_add' f g := by
    apply corner_ext ha
    rw [corner_add_val]
    rfl

variable [FiniteDimensional k A]

variable (k) in
include k in
theorem idealMod_end_isLocalRing {a : A} (hp : IsPrimitiveIdempotent a) :
    IsLocalRing (End (idealMod a)) := by
  haveI := corner_isLocalRing_of_primitive k hp
  exact MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm (endEquivCorner hp.1).symm

theorem idealMod_not_isZero {a : A} (hp : IsPrimitiveIdempotent a) : ¬ IsZero (idealMod a) := by
  intro h
  have hs : Subsingleton (rightIdeal a) := ModuleCat.subsingleton_of_isZero h
  apply hp.2.1
  have := Subsingleton.elim (genOf hp.1) 0
  exact congrArg Subtype.val this

/-! ### `eA ≅ e_i A` -/

theorem cornerVal_sum {a : A} (ha : IsIdempotentElem a) {ι : Type*} (s : Finset ι)
    (f : ι → ha.Corner) : cornerVal ha (∑ i ∈ s, f i) = ∑ i ∈ s, cornerVal ha (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [corner_zero_val]
  | insert i s hi ih => rw [Finset.sum_insert hi, corner_add_val, ih, Finset.sum_insert hi]

variable (k) in
include k in
/-- **The right ideal of a primitive idempotent is one of the `e_i A`.** -/
theorem exists_iso_ideal {e : A} (hp : IsPrimitiveIdempotent e) {ι : Type*} [Fintype ι]
    {e' : ι → A} (he' : CompleteOrthogonalIdempotents e') (hp' : ∀ i, IsPrimitiveIdempotent (e' i)) :
    ∃ i, Nonempty (idealMod e ≅ idealMod (e' i)) := by
  have he := hp.1
  haveI := corner_isLocalRing_of_primitive k hp
  let u : ι → he.Corner := fun i ↦ cornerMk he (e * e' i * e) ⟨e' i, rfl⟩
  have hsum : ∑ i, u i = 1 := by
    apply corner_ext he
    rw [cornerVal_sum, corner_one_val]
    change ∑ i, e * e' i * e = e
    rw [← Finset.sum_mul, ← Finset.mul_sum, he'.complete, mul_one, he.eq]
  obtain ⟨i, -, hu⟩ := exists_isUnit_of_sum Finset.univ u (by rw [hsum]; exact isUnit_one)
  obtain ⟨v, hv⟩ := hu
  set W := cornerVal he (v⁻¹ : he.Cornerˣ).1
  have hWu : W * (e * e' i * e) = e := by
    have := congrArg (cornerVal he) v.inv_mul
    rw [corner_mul_val, hv, corner_one_val] at this
    exact this
  have hWl : e * W = W := corner_mul_left he _
  have hWr : W * e = W := corner_mul_right he _
  let φ : idealMod e ⟶ idealMod (e' i) :=
    ModuleCat.ofHom (lmul (hp' i).1 (e' i * e) (by rw [← mul_assoc, (hp' i).1.eq]))
  let ψ : idealMod (e' i) ⟶ idealMod e :=
    ModuleCat.ofHom (lmul he (W * e' i) (by rw [← mul_assoc, hWl]))
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ Subtype.ext ?_)
    change W * e' i * (e' i * e * m.1) = m.1
    calc W * e' i * (e' i * e * m.1) = W * (e' i * e' i) * e * m.1 := by simp only [mul_assoc]
      _ = (W * e) * e' i * e * m.1 := by rw [(hp' i).1.eq, hWr]
      _ = W * (e * e' i * e) * m.1 := by simp only [mul_assoc]
      _ = m.1 := by rw [hWu, ideal_fixed he]
  haveI := idealMod_end_isLocalRing k (hp' i)
  haveI := isIso_of_retract (idealMod_not_isZero hp) φ ψ hφψ
  exact ⟨i, ⟨asIso φ⟩⟩

/-- **Isomorphic `e_i A`, `e_j A` give the data of the basic condition.** -/
theorem basic_data_of_iso {a b : A} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (φ : idealMod a ≅ idealMod b) :
    ∃ x y : A, a * x * b = x ∧ b * y * a = y ∧ x * y = a ∧ y * x = b := by
  refine ⟨(φ.inv.hom (genOf hb)).1, (φ.hom.hom (genOf ha)).1, hom_gen_val hb ha φ.inv,
    hom_gen_val ha hb φ.hom, ?_, ?_⟩
  · have h := hom_apply_eq hb φ.inv (φ.hom.hom (genOf ha))
    rw [← h]
    change ((φ.hom ≫ φ.inv).hom (genOf ha)).1 = a
    rw [Iso.hom_inv_id]; rfl
  · have h := hom_apply_eq ha φ.hom (φ.inv.hom (genOf hb))
    rw [← h]
    change ((φ.inv ≫ φ.hom).hom (genOf hb)).1 = b
    rw [Iso.inv_hom_id]; rfl

end MultiplicativeBasisDeformations
