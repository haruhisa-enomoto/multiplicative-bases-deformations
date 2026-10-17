import MultiplicativeBasisDeformations.Foundations.CornerRepFinite

/-!
# Full idempotents: Morita equivalence for representation-finiteness

For Lemma 4.7 (`lem:homogeneous-projection`, `scalar-normalization.tex`):
"Repeated labels give matrix multiplicities, and the distinct labels give an
idempotent corner of `B`. Thus `B'` is representation-finite by Morita
equivalence and Lemma 3.1(1)."

The Morita equivalence used is the one of a full idempotent `e` (`AeA = A`):
every right `A`-module `N` is the coinduced module `Hom_C(Ae, Ne)` of its
`C = eAe`-module `Ne` (`theta_bijective`). Hence if `eAe` is
representation-finite, so is `A` (`isRepresentationFinite_of_full`). Repeated
labels are handled by placing them, together with the distinct labels, in one
category algebra in which the distinct labels form a full idempotent
(`CategoryAlgebraCorners.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

universe u v

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A] {e : A} (he : IsIdempotentElem e)

/-- A full idempotent, as a finite sum `∑ pᵢ e qᵢ = 1`. -/
theorem exists_sum_eq_one
    (hfull : ∀ a : A, a ∈ Submodule.span k {x | ∃ p q : A, x = p * e * q}) :
    ∃ (m : ℕ) (p q : Fin m → A), ∑ i, p i * e * q i = 1 := by
  let P : A → Prop := fun x ↦ ∃ (m : ℕ) (p q : Fin m → A), ∑ i, p i * e * q i = x
  suffices h : ∀ x ∈ Submodule.span k {x | ∃ p q : A, x = p * e * q}, P x from h 1 (hfull 1)
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨p, q, rfl⟩ := hx
      exact ⟨1, fun _ ↦ p, fun _ ↦ q, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨m, p, q, rfl⟩ := hx
      obtain ⟨m', p', q', rfl⟩ := hy
      refine ⟨m + m', Fin.append p p', Fin.append q q', ?_⟩
      rw [Fin.sum_univ_add]
      simp
  | smul c x _ hx =>
      obtain ⟨m, p, q, rfl⟩ := hx
      refine ⟨m, fun i ↦ c • p i, q, ?_⟩
      rw [Finset.smul_sum]
      simp [smul_mul_assoc]

namespace Coind

variable {he}

/-- `Ne`, for a right `A`-module `N`. -/
def resSub (N : RightModuleCat A) : Submodule k N where
  carrier := {n | MulOpposite.op e • n = n}
  add_mem' {x y} hx hy := by
    change MulOpposite.op e • (x + y) = x + y
    rw [smul_add, hx, hy]
  zero_mem' := smul_zero _
  smul_mem' c x hx := by
    change MulOpposite.op e • (c • x) = c • x
    rw [smul_comm, hx]

theorem mem_resSub {N : RightModuleCat A} {n : N} :
    n ∈ resSub (k := k) (e := e) N ↔ MulOpposite.op e • n = n := Iff.rfl

theorem corner_smul_mem {N : RightModuleCat A} (c : he.Corner) (n : N) :
    MulOpposite.op (cornerVal he c) • n ∈ resSub (k := k) (e := e) N := by
  change MulOpposite.op e • MulOpposite.op (cornerVal he c) • n = _
  rw [smul_smul, ← MulOpposite.op_mul, corner_mul_right]

instance (N : RightModuleCat A) : SMul he.Cornerᵐᵒᵖ (resSub (k := k) (e := e) N) where
  smul c n := ⟨MulOpposite.op (cornerVal he c.unop) • n.1, corner_smul_mem c.unop n.1⟩

theorem res_smul_val {N : RightModuleCat A} (c : he.Cornerᵐᵒᵖ) (n : resSub (k := k) (e := e) N) :
    ((c • n : resSub (k := k) (e := e) N) : N) = MulOpposite.op (cornerVal he c.unop) • n.1 := rfl

instance (N : RightModuleCat A) : Module he.Cornerᵐᵒᵖ (resSub (k := k) (e := e) N) where
  one_smul n := Subtype.ext (by
    rw [res_smul_val, MulOpposite.unop_one, corner_one_val]; exact n.2)
  mul_smul c d n := Subtype.ext (by
    simp only [res_smul_val, MulOpposite.unop_mul, corner_mul_val, MulOpposite.op_mul, mul_smul])
  smul_zero c := Subtype.ext (by simp [res_smul_val])
  smul_add c x y := Subtype.ext (by simp [res_smul_val])
  add_smul c d x := Subtype.ext (by
    simp [res_smul_val, corner_add_val, add_smul])
  zero_smul x := Subtype.ext (by
    simp only [res_smul_val, MulOpposite.unop_zero]
    rw [corner_zero_val]
    simp)

variable (he) in
/-- The restriction `N ↦ Ne` to the corner. -/
def res (N : RightModuleCat A) : RightModuleCat he.Corner := ModuleCat.of _ (resSub (k := k) (e := e) N)

variable (k) in
/-- `res` with the field explicit. -/
abbrev resK (N : RightModuleCat A) : RightModuleCat he.Corner := res (k := k) he N

/-- The underlying element of `N` of an element of `Ne`. -/
def rv {N : RightModuleCat A} (m : resK k (he := he) N) : N := (show resSub (k := k) (e := e) N from m).1

/-- An element of `Ne`. -/
def rmk {N : RightModuleCat A} (n : N) (hn : n ∈ resSub (k := k) (e := e) N) : resK k (he := he) N :=
  show resSub (k := k) (e := e) N from ⟨n, hn⟩

@[simp] theorem rv_rmk {N : RightModuleCat A} (n : N) (hn : n ∈ resSub (k := k) (e := e) N) :
    rv (rmk (k := k) (he := he) n hn) = n := rfl

theorem rv_injective {N : RightModuleCat A} : Function.Injective (rv (k := k) (he := he) (N := N)) :=
  fun _ _ h ↦ Subtype.ext h

@[simp] theorem rv_add {N : RightModuleCat A} (m m' : resK k (he := he) N) : rv (m + m') = rv m + rv m' := rfl

@[simp] theorem rv_smul {N : RightModuleCat A} (c : he.Cornerᵐᵒᵖ) (m : resK k (he := he) N) :
    rv (c • m) = MulOpposite.op (cornerVal he c.unop) • rv m := rfl

theorem rv_sum {N : RightModuleCat A} {ι : Type*} (s : Finset ι) (f : ι → resK k (he := he) N) :
    rv (∑ i ∈ s, f i) = ∑ i ∈ s, rv (f i) :=
  map_sum (AddSubmonoidClass.subtype (resSub (k := k) (e := e) N)) f s

/-- `n y ∈ Ne` for `y ∈ Ae`. -/
theorem smul_mem_res {N : RightModuleCat A} (n : N) (y : leftIdeal (e := e)) :
    MulOpposite.op y.1 • n ∈ resSub (k := k) (e := e) N := by
  change MulOpposite.op e • MulOpposite.op y.1 • n = _
  rw [smul_smul, ← MulOpposite.op_mul, show y.1 * e = y.1 from y.2]

variable (he) in
/-- The comparison map `N → Hom_C(Ae, Ne)`, `n ↦ (y ↦ n y)`. -/
def thetaFun (N : RightModuleCat A) (n : N) : Obj he (resK k (he := he) N) where
  toFun y := rmk (k := k) (MulOpposite.op y.1 • n) (smul_mem_res n y)
  map_add' y z := rv_injective (by
    change MulOpposite.op (y.1 + z.1) • n = _
    rw [MulOpposite.op_add, add_smul]; rfl)
  map_smul' c y := rv_injective (by
    change MulOpposite.op (y.1 * cornerVal he c.unop) • n =
      MulOpposite.op (cornerVal he c.unop) • MulOpposite.op y.1 • n
    rw [MulOpposite.op_mul, mul_smul])

theorem thetaFun_apply (N : RightModuleCat A) (n : N) (y : leftIdeal (e := e)) :
    rv (thetaFun (k := k) he N n y) = MulOpposite.op y.1 • n := rfl

variable (he) in
/-- The comparison map, as a map of right `A`-modules. -/
def theta (N : RightModuleCat A) : N →ₗ[Aᵐᵒᵖ] Obj he (resK k (he := he) N) where
  toFun := thetaFun (k := k) he N
  map_add' n m := Obj.ext fun y ↦ rv_injective (by
    change MulOpposite.op y.1 • (n + m) = MulOpposite.op y.1 • n + MulOpposite.op y.1 • m
    rw [smul_add])
  map_smul' a n := Obj.ext fun y ↦ rv_injective (by
    change MulOpposite.op y.1 • a • n = MulOpposite.op (a.unop * y.1) • n
    rw [smul_smul, MulOpposite.op_mul, MulOpposite.op_unop])

/-- **Morita for a full idempotent**: `N ≅ Hom_C(Ae, Ne)`. -/
theorem theta_bijective
    (hfull : ∀ a : A, a ∈ Submodule.span k {x | ∃ p q : A, x = p * e * q})
    (N : RightModuleCat A) : Function.Bijective (theta (k := k) he N) := by
  obtain ⟨m, p, q, hpq⟩ := exists_sum_eq_one (k := k) hfull
  constructor
  · intro n n' h
    have key : ∀ x : A, MulOpposite.op (x * e) • n = MulOpposite.op (x * e) • n' := by
      intro x
      have := congrArg (fun φ : Obj he (resK k (he := he) N) ↦ rv (φ (xe (he := he) x))) h
      exact this
    calc n = MulOpposite.op (1 : A) • n := (one_smul _ _).symm
      _ = ∑ i, MulOpposite.op (q i) • MulOpposite.op (p i * e) • n := by
          rw [← hpq, Finset.op_sum, Finset.sum_smul]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [smul_smul, ← MulOpposite.op_mul]
      _ = ∑ i, MulOpposite.op (q i) • MulOpposite.op (p i * e) • n' := by
          simp only [key]
      _ = MulOpposite.op (1 : A) • n' := by
          rw [← hpq, Finset.op_sum, Finset.sum_smul]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [smul_smul, ← MulOpposite.op_mul]
      _ = n' := one_smul _ _
  · intro φ
    refine ⟨∑ i, MulOpposite.op (q i) • rv (φ (xe (he := he) (p i))), ?_⟩
    refine Obj.ext fun y ↦ rv_injective ?_
    change MulOpposite.op y.1 • ∑ i, MulOpposite.op (q i) • rv (φ (xe (he := he) (p i))) = _
    rw [Finset.smul_sum]
    have hc : ∀ i, e * q i * y.1 ∈ Subsemigroup.corner e := fun i ↦ by
      refine (Subsemigroup.mem_corner_iff he).2 ⟨?_, ?_⟩
      · rw [← mul_assoc, ← mul_assoc, he.eq]
      · rw [mul_assoc, show y.1 * e = y.1 from y.2]
    have hterm : ∀ i, MulOpposite.op y.1 • MulOpposite.op (q i) • rv (φ (xe (he := he) (p i))) =
        rv (φ (lmul (he := he) (p i * e * q i) y)) := by
      intro i
      have hmem : MulOpposite.op e • rv (φ (xe (he := he) (p i))) = rv (φ (xe (he := he) (p i))) :=
        (show resSub (k := k) (e := e) N from φ (xe (he := he) (p i))).2
      rw [smul_smul, ← MulOpposite.op_mul, ← hmem, smul_smul, ← MulOpposite.op_mul]
      have hlin := map_smul φ (MulOpposite.op (cornerMk he (e * q i * y.1) (hc i)))
        (xe (he := he) (p i))
      have hx : (MulOpposite.op (cornerMk he (e * q i * y.1) (hc i))) • xe (he := he) (p i) =
          lmul (he := he) (p i * e * q i) y := Subtype.ext (by
        simp only [smul_val, MulOpposite.unop_op, cornerVal_mk, lmul_val, xe]
        simp only [mul_assoc]
        rw [← mul_assoc e e, he.eq])
      rw [hx] at hlin
      rw [hlin, rv_smul, MulOpposite.unop_op, cornerVal_mk]
      simp only [mul_assoc]
    simp only [hterm]
    rw [← rv_sum, ← map_sum]
    congr 2
    apply Subtype.ext
    simp only [lmul_val, AddSubmonoid.coe_finset_sum, AddSubgroup.val_finset_sum]
    rw [← Finset.sum_mul, hpq, one_mul]

/-- `Ne → N` is `k`-linear for the module structure through the corner. -/
def rvK (N : RightModuleCat A) : resK k (he := he) N →ₗ[k] N where
  toFun := rv
  map_add' := rv_add
  map_smul' c m := by
    change rv (MulOpposite.op (algebraMap k he.Corner c) • m) = c • rv m
    rw [rv_smul, MulOpposite.unop_op]
    change MulOpposite.op (c • e) • rv m = c • rv m
    have hm : MulOpposite.op e • rv m = rv m := (show resSub (k := k) (e := e) N from m).2
    rw [MulOpposite.op_smul, smul_assoc, hm]

theorem res_finite (N : RightModuleCat A) [Module.Finite k N] :
    Module.Finite k (resK k (he := he) N) :=
  Module.Finite.of_injective (rvK (he := he) N) rv_injective

/-- A ring isomorphism of endomorphism rings from an isomorphism. -/
def endRingEquivOfIso {C : Type*} [Category C] [Preadditive C] {X Y : C} (i : X ≅ Y) :
    End X ≃+* End Y :=
  { i.conj with
    map_add' := fun f g ↦ by
      simp only [Iso.conj_apply, MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe]
      rw [Preadditive.add_comp, Preadditive.comp_add] }

end Coind

open Coind in
/-- **Morita for a full idempotent**: if `AeA = A` and `eAe` is
representation-finite, so is `A`. -/
theorem isRepresentationFinite_of_full [FiniteDimensional k A]
    (hfull : ∀ a : A, a ∈ Submodule.span k {x | ∃ p q : A, x = p * e * q})
    (hC : IsRepresentationFinite k he.Corner) : IsRepresentationFinite k A := by
  classical
  obtain ⟨n, V, hV, hcov⟩ := hC
  haveI : Module.Finite k he.Corner := corner_finite he
  haveI : Module.Finite k he.Cornerᵐᵒᵖ := inferInstance
  have hloc : ∀ (W : RightModuleCat he.Corner), IsFiniteIndecomposable k he.Corner W →
      IsFiniteIndecomposable k A ((functor he).obj W) := by
    intro W hW
    haveI := hW.1
    haveI : IsLocalRing (End W) :=
      MBDVendor.Magnitude.moduleCat_end_isLocalRing (k := k) (A := he.Cornerᵐᵒᵖ) W hW.2
    haveI : IsLocalRing (End ((functor he).obj W)) :=
      MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm
        (MBDVendor.Magnitude.CategoryTheory.Functor.endRingEquivOfFullyFaithful (functor he) W)
    exact ⟨coind_finite W, MBDVendor.Magnitude.CategoryTheory.indecomposable_of_local_end _⟩
  refine ⟨n, fun i ↦ (functor he).obj (V i), fun i ↦ hloc _ (hV i), fun N hN ↦ ?_⟩
  haveI := hN.1
  -- `N ≅ Hom_C(Ae, Ne)`
  let iN : N ≅ (functor he).obj (resK k (he := he) N) :=
    (LinearEquiv.ofBijective (theta (k := k) he N) (theta_bijective (k := k) (he := he) hfull N)).toModuleIso
  haveI : Module.Finite k (resK k (he := he) N) := res_finite N
  haveI : IsLocalRing (End N) :=
    MBDVendor.Magnitude.moduleCat_end_isLocalRing (k := k) (A := Aᵐᵒᵖ) N hN.2
  haveI : IsLocalRing (End ((functor he).obj (resK k (he := he) N))) :=
    MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm (endRingEquivOfIso iN)
  haveI : IsLocalRing (End (resK k (he := he) N)) :=
    MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm
      (MBDVendor.Magnitude.CategoryTheory.Functor.endRingEquivOfFullyFaithful (functor he)
        (resK k (he := he) N)).symm
  obtain ⟨i, ⟨j⟩⟩ := hcov _ ⟨res_finite N,
    MBDVendor.Magnitude.CategoryTheory.indecomposable_of_local_end _⟩
  exact ⟨i, ⟨iN ≪≫ (functor he).mapIso j⟩⟩

end MultiplicativeBasisDeformations
