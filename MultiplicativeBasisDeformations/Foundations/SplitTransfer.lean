import MultiplicativeBasisDeformations.Foundations.Exchange
import MultiplicativeBasisDeformations.Foundations.RepFinite
import MBDVendor.Magnitude.Algebra.IndecomposableLocalEnd
import MBDVendor.Magnitude.CategoryTheory.IndecomposableOfLocalEnd

/-!
# Lemma 4.6: split representation transfer

`lem:split-representation-transfer` (`scalar-normalization.tex`): let
`C ⊆ B` be a unital inclusion of finite-dimensional algebras, `q : C ↠ D` a
quotient and `π : B → D` a `C`-bimodule map with `π|_C = q`. If `B` is
representation-finite, so is `D`.

The source proves that a right `D`-module `M`, inflated to `C`, is a summand
of `(M ⊗_C B)|_C` (map `m ↦ m ⊗ 1`, retraction `m ⊗ b ↦ m π(b)`). We use the
adjoint form: `M` is a summand of `Hom_C(B, M)|_C`, with map
`m ↦ (b ↦ m π(b))` and retraction `φ ↦ φ(1)`; the rest of the argument
(decomposition over the finitely many indecomposable `B`-modules, exchange,
inflation fully faithful) is the source's.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

universe u v

variable {k : Type u} [Field k] {B D : Type v} [Ring B] [Algebra k B] [Ring D] [Algebra k D]
  (C : Subalgebra k B) (q : C →ₐ[k] D)

/-- The inclusion `Cᵐᵒᵖ → Bᵐᵒᵖ`. -/
abbrev inclOp : Cᵐᵒᵖ →+* Bᵐᵒᵖ := RingHom.op (C.val : C →+* B)

/-- The quotient `Cᵐᵒᵖ → Dᵐᵒᵖ`. -/
abbrev qOp : Cᵐᵒᵖ →+* Dᵐᵒᵖ := RingHom.op (q : C →+* D)

variable {C q} (π : B →ₗ[k] D)
  (hbimod : ∀ (c c' : C) (b : B), π (c * b * c') = q c * π b * q c')

include hbimod in
theorem pi_mul_right (b : B) (c : C) : π (b * c) = π b * q c := by
  have := hbimod 1 c b
  rwa [Subalgebra.coe_one, one_mul, map_one, one_mul] at this

include hbimod in
theorem pi_mul_left (c : C) (b : B) : π (c * b) = q c * π b := by
  have := hbimod c 1 b
  rwa [Subalgebra.coe_one, mul_one, map_one, mul_one] at this

namespace SplitCoind

/-- `B` as a right `C`-module. -/
@[nolint unusedArguments]
def RC (_C : Subalgebra k B) : Type v := B

instance : AddCommGroup (RC C) := inferInstanceAs (AddCommGroup B)

/-- The identification `B = RC`. -/
def toRC {C : Subalgebra k B} : B ≃+ RC C := AddEquiv.refl B

instance : Module Cᵐᵒᵖ (RC C) where
  smul c x := toRC (toRC.symm x * (c.unop : B))
  one_smul x := by change toRC (toRC.symm x * 1) = x; rw [mul_one]; rfl
  mul_smul c d x := by
    change toRC (toRC.symm x * ((d.unop * c.unop : C) : B)) =
      toRC (toRC.symm x * (d.unop : B) * (c.unop : B))
    rw [Subalgebra.coe_mul, mul_assoc]
  smul_zero c := by change toRC (0 * _) = _; rw [zero_mul]; rfl
  smul_add c x y := by change toRC ((toRC.symm x + toRC.symm y) * _) = _; rw [add_mul]; rfl
  add_smul c d x := by
    change toRC (toRC.symm x * ((c.unop + d.unop : C) : B)) = _
    rw [Subalgebra.coe_add, mul_add]; rfl
  zero_smul x := by change toRC (toRC.symm x * ((0 : C) : B)) = _; rw [Subalgebra.coe_zero, mul_zero]; rfl

theorem smul_def (c : Cᵐᵒᵖ) (x : B) : c • toRC (C := C) x = toRC (x * (c.unop : B)) := rfl

/-- Left multiplication by `b` on `RC`. -/
def lmul (b : B) : RC C →ₗ[Cᵐᵒᵖ] RC C where
  toFun x := toRC (b * toRC.symm x)
  map_add' x y := by change toRC (b * (toRC.symm x + toRC.symm y)) = _; rw [mul_add]; rfl
  map_smul' c x := by
    change toRC (b * (toRC.symm x * (c.unop : B))) = toRC (b * toRC.symm x * (c.unop : B))
    rw [mul_assoc]

variable (C) in
/-- The carrier `Hom_C(B, V)` of the coinduced module. -/
def Obj (V : ModuleCat.{v} Cᵐᵒᵖ) := RC C →ₗ[Cᵐᵒᵖ] V

instance (V : ModuleCat.{v} Cᵐᵒᵖ) : AddCommGroup (Obj C V) :=
  inferInstanceAs (AddCommGroup (RC C →ₗ[Cᵐᵒᵖ] V))

instance (V : ModuleCat.{v} Cᵐᵒᵖ) : FunLike (Obj C V) (RC C) V :=
  inferInstanceAs (FunLike (RC C →ₗ[Cᵐᵒᵖ] V) _ _)

instance (V : ModuleCat.{v} Cᵐᵒᵖ) : LinearMapClass (Obj C V) Cᵐᵒᵖ (RC C) V :=
  inferInstanceAs (LinearMapClass (RC C →ₗ[Cᵐᵒᵖ] V) _ _ _)

@[ext] theorem Obj.ext {V : ModuleCat.{v} Cᵐᵒᵖ} {φ ψ : Obj C V} (h : ∀ x, φ x = ψ x) : φ = ψ :=
  LinearMap.ext h

instance (V : ModuleCat.{v} Cᵐᵒᵖ) : SMul Bᵐᵒᵖ (Obj C V) where
  smul b φ := LinearMap.comp (show RC C →ₗ[Cᵐᵒᵖ] V from φ) (lmul b.unop)

theorem smul_apply' {V : ModuleCat.{v} Cᵐᵒᵖ} (b : Bᵐᵒᵖ) (φ : Obj C V) (x : B) :
    (b • φ) (toRC x) = φ (toRC (b.unop * x)) := rfl

instance (V : ModuleCat.{v} Cᵐᵒᵖ) : Module Bᵐᵒᵖ (Obj C V) where
  one_smul φ := Obj.ext fun x ↦ by
    change φ (toRC (1 * toRC.symm x)) = φ x; rw [one_mul]; rfl
  mul_smul a b φ := Obj.ext fun x ↦ by
    change φ (toRC ((a * b).unop * toRC.symm x)) = φ (toRC (b.unop * (a.unop * toRC.symm x)))
    rw [MulOpposite.unop_mul, mul_assoc]
  smul_zero a := Obj.ext fun x ↦ rfl
  smul_add a φ ψ := Obj.ext fun x ↦ rfl
  add_smul a b φ := Obj.ext fun x ↦ by
    change φ (toRC ((a + b).unop * toRC.symm x)) = φ (toRC (a.unop * toRC.symm x)) +
      φ (toRC (b.unop * toRC.symm x))
    rw [MulOpposite.unop_add, add_mul, map_add (toRC (C := C)), map_add]
  zero_smul φ := Obj.ext fun x ↦ by
    change φ (toRC ((0 : Bᵐᵒᵖ).unop * toRC.symm x)) = 0
    rw [MulOpposite.unop_zero, zero_mul, map_zero, map_zero]

/-- The coinduced right `B`-module. -/
def coind (V : ModuleCat.{v} Cᵐᵒᵖ) : ModuleCat.{v} Bᵐᵒᵖ := ModuleCat.of Bᵐᵒᵖ (Obj C V)

/-- Evaluation of `Hom_C(B, V)` on `B`, a `k`-linear injection into
`Hom_k(B, V)`. -/
def evalK (V : ModuleCat.{v} Cᵐᵒᵖ) : coind (C := C) V →ₗ[k] (B →ₗ[k] V) where
  toFun φ :=
    { toFun x := (show Obj C V from φ) (toRC x)
      map_add' x y := by rw [map_add, map_add]
      map_smul' c x := by
        have h : toRC (C := C) (c • x) = MulOpposite.op (algebraMap k C c) • toRC x := by
          rw [smul_def]
          change toRC (c • x) = toRC (x * algebraMap k B c)
          rw [Algebra.smul_def, Algebra.commutes]
        rw [h, map_smul]; rfl }
  map_add' φ ψ := LinearMap.ext fun x ↦ rfl
  map_smul' c φ := LinearMap.ext fun x ↦ by
    change (show Obj C V from φ) (toRC ((algebraMap k B c) * x)) =
      c • (show Obj C V from φ) (toRC x)
    rw [← Algebra.smul_def]
    have h : toRC (C := C) (c • x) = MulOpposite.op (algebraMap k C c) • toRC x := by
      rw [smul_def]
      change toRC (c • x) = toRC (x * algebraMap k B c)
      rw [Algebra.smul_def, Algebra.commutes]
    rw [h, map_smul]; rfl

theorem evalK_injective (V : ModuleCat.{v} Cᵐᵒᵖ) : Function.Injective (evalK (C := C) V) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro φ hφ
  rw [LinearMap.mem_ker] at hφ
  rw [Submodule.mem_bot]
  change (show Obj C V from φ) = 0
  exact Obj.ext fun x ↦ LinearMap.congr_fun hφ (toRC.symm x)

theorem coind_finite [FiniteDimensional k B] (V : ModuleCat.{v} Cᵐᵒᵖ) [Module.Finite k V] :
    Module.Finite k (coind (C := C) V) :=
  Module.Finite.of_injective (evalK V) (evalK_injective V)

variable (q) in
/-- Inflation of a right `D`-module to `C`. -/
abbrev Infl (M : ModuleCat.{v} Dᵐᵒᵖ) : ModuleCat.{v} Cᵐᵒᵖ :=
  (ModuleCat.restrictScalars (qOp C q)).obj M

variable (C) in
/-- Restriction of a right `B`-module to `C`. -/
abbrev Res (N : ModuleCat.{v} Bᵐᵒᵖ) : ModuleCat.{v} Cᵐᵒᵖ :=
  (ModuleCat.restrictScalars (inclOp C)).obj N

include hbimod in
/-- `ψ_m : b ↦ m π(b)`. -/
def gm (M : ModuleCat.{v} Dᵐᵒᵖ) (m : M) : Obj C (Infl q M) where
  toFun x := (MulOpposite.op (π (toRC.symm x)) • m : M)
  map_add' x y := by
    change MulOpposite.op (π (toRC.symm x + toRC.symm y)) • m =
      MulOpposite.op (π (toRC.symm x)) • m + MulOpposite.op (π (toRC.symm y)) • m
    rw [map_add, MulOpposite.op_add, add_smul]
  map_smul' c x := by
    change MulOpposite.op (π (toRC.symm x * (c.unop : B))) • m =
      (qOp C q c) • (MulOpposite.op (π (toRC.symm x)) • m)
    rw [pi_mul_right π hbimod, MulOpposite.op_mul, mul_smul]
    rfl

theorem gm_apply (M : ModuleCat.{v} Dᵐᵒᵖ) (m : M) (x : B) :
    gm π hbimod M m (toRC x) = (MulOpposite.op (π x) • m : M) := rfl

/-- The split mono `M → Hom_C(B, M)|_C`. -/
def jmap (M : ModuleCat.{v} Dᵐᵒᵖ) : Infl q M ⟶ Res C (coind (Infl q M)) :=
  ModuleCat.ofHom (X := Infl q M) (Y := Res C (coind (Infl q M)))
    { toFun m := gm π hbimod M m
      map_add' m m' := Obj.ext fun x ↦ by
        change MulOpposite.op (π (toRC.symm x)) • (m + m' : M) =
          MulOpposite.op (π (toRC.symm x)) • m + MulOpposite.op (π (toRC.symm x)) • m'
        rw [smul_add]
      map_smul' c m := Obj.ext fun x ↦ by
        change MulOpposite.op (π (toRC.symm x)) • ((qOp C q c) • m : M) =
          MulOpposite.op (π ((c.unop : B) * toRC.symm x)) • m
        rw [pi_mul_left π hbimod, smul_smul, MulOpposite.op_mul]
        rfl }

/-- The retraction `φ ↦ φ(1)`. -/
def rmap (M : ModuleCat.{v} Dᵐᵒᵖ) : Res C (coind (Infl q M)) ⟶ Infl q M :=
  ModuleCat.ofHom (X := Res C (coind (Infl q M))) (Y := Infl q M)
    { toFun φ := (show Obj C (Infl q M) from φ) (toRC 1)
      map_add' φ ψ := rfl
      map_smul' c φ := by
        change (show Obj C (Infl q M) from φ) (toRC ((c.unop : B) * 1)) =
          c • (show Obj C (Infl q M) from φ) (toRC 1)
        rw [← map_smul, smul_def, one_mul, mul_one] }

variable (hπ : ∀ c : C, π c = q c)

include hπ in
theorem jmap_rmap (M : ModuleCat.{v} Dᵐᵒᵖ) : jmap π hbimod M ≫ rmap M = 𝟙 _ := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
  change MulOpposite.op (π (toRC.symm (toRC (1 : B)))) • (m : M) = m
  have h1 : π (toRC.symm (toRC (C := C) (1 : B))) = 1 := by
    change π ((1 : C) : B) = 1
    rw [hπ, map_one]
  rw [h1, MulOpposite.op_one, one_smul]

end SplitCoind

/-- Restriction of scalars along a `k`-algebra map preserves finite dimension
over `k`. -/
theorem finite_restrict {R S : Type v} [Ring R] [Ring S] [Algebra k R] [Algebra k S]
    (φ : R →+* S) (hφ : ∀ c : k, φ (algebraMap k R c) = algebraMap k S c) (M : ModuleCat.{v} S)
    [Module.Finite k M] : Module.Finite k ((ModuleCat.restrictScalars φ).obj M) := by
  let f : M →ₗ[k] (ModuleCat.restrictScalars φ).obj M :=
    { toFun m := m
      map_add' _ _ := rfl
      map_smul' c m := by
        change algebraMap k S c • m = φ (algebraMap k R c) • m
        rw [hφ] }
  exact Module.Finite.of_surjective f fun m ↦ ⟨m, rfl⟩

/-- Restriction of scalars along a surjective ring map is full. -/
theorem restrict_full {R S : Type v} [Ring R] [Ring S] (φ : R →+* S)
    (hφ : Function.Surjective φ) : (ModuleCat.restrictScalars.{v} φ).Full where
  map_surjective {M M'} g := by
    refine ⟨ModuleCat.ofHom
      { toFun := g.hom
        map_add' := g.hom.map_add
        map_smul' := fun s m ↦ by
          obtain ⟨r, rfl⟩ := hφ s
          exact g.hom.map_smul r m }, ?_⟩
    rfl

theorem not_isZero_of_local {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {X : 𝒞}
    [IsLocalRing (End X)] : ¬ IsZero X := by
  intro h
  exact one_ne_zero (show (1 : End X) = 0 from h.eq_of_src _ _)

open SplitCoind in
include hbimod in
/-- **Lemma 4.6** (`lem:split-representation-transfer`). -/
theorem splitRepresentationTransfer_of [FiniteDimensional k B] [FiniteDimensional k D]
    (hq : Function.Surjective q) (hπ : ∀ c : C, π c = q c)
    (hB : IsRepresentationFinite k B) : IsRepresentationFinite k D := by
  classical
  obtain ⟨N, X, hX, hdec⟩ := exists_labels_iso hB
  haveI : Module.Finite k Cᵐᵒᵖ := inferInstance
  have hRes : ∀ l, Module.Finite k (Res C (X l)) := fun l ↦ by
    haveI := (hX l).1
    exact finite_restrict (inclOp C) (fun c ↦ rfl) (X l)
  let dl : ∀ l, MBDVendor.Magnitude.CategoryTheory.FiniteIndecomposableDecomposition
      (Res C (X l)) := fun l ↦ by
    haveI := hRes l
    exact (MBDVendor.Magnitude.finiteIndecomposableDecomposition_module_exists
      (k := k) (A := Cᵐᵒᵖ) (Res C (X l))).some
  let Z : (Σ l, Fin (dl l).n) → ModuleCat.{v} Cᵐᵒᵖ := fun t ↦ (dl t.1).summand t.2
  let P : (Σ l, Fin (dl l).n) → Prop := fun t ↦ ∃ M : ModuleCat.{v} Dᵐᵒᵖ,
    IsFiniteIndecomposable k D M ∧ Nonempty (Infl q M ≅ Z t)
  let T := {t // P t}
  let eT := Fintype.equivFin T
  refine ⟨Fintype.card T, fun j ↦ (eT.symm j).2.choose, fun j ↦ (eT.symm j).2.choose_spec.1, ?_⟩
  intro M hM
  haveI := hM.1
  have hqo : Function.Surjective (qOp C q) := fun d ↦ by
    obtain ⟨c, hc⟩ := hq d.unop
    refine ⟨MulOpposite.op c, ?_⟩
    apply MulOpposite.unop_injective
    exact hc
  haveI := restrict_full (qOp C q) hqo
  haveI : IsLocalRing (End M) :=
    MBDVendor.Magnitude.moduleCat_end_isLocalRing (k := k) (A := Dᵐᵒᵖ) M hM.2
  haveI : IsLocalRing (End (Infl q M)) :=
    MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm
      (MBDVendor.Magnitude.CategoryTheory.Functor.endRingEquivOfFullyFaithful
        (ModuleCat.restrictScalars (qOp C q)) M)
  haveI : Module.Finite k (Infl q M) := finite_restrict (qOp C q) (fun c ↦ by
    change MulOpposite.op (q (algebraMap k C c)) = _
    rw [AlgHom.commutes]; rfl) M
  haveI := coind_finite (C := C) (Infl q M)
  obtain ⟨n, l, -, ⟨eN⟩⟩ := hdec (coind (C := C) (Infl q M)) inferInstance
  let R := ModuleCat.restrictScalars.{v} (inclOp C)
  let e2 : R.obj (coind (C := C) (Infl q M)) ≅ ⨁ fun j ↦ R.obj (X (l j)) :=
    R.mapIso eN ≪≫ R.mapBiproduct _
  obtain ⟨j, i1, p1, h1⟩ := exists_retract_summand (fun j ↦ R.obj (X (l j)))
    (jmap π hbimod M ≫ e2.hom) (e2.inv ≫ rmap M) (by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact jmap_rmap π hbimod hπ M)
  let dd := dl (l j)
  obtain ⟨m, i2, p2, h2⟩ := exists_retract_summand dd.summand (i1 ≫ dd.isoBiproduct.hom)
    (dd.isoBiproduct.inv ≫ p1) (by simp only [Category.assoc, Iso.hom_inv_id_assoc]; exact h1)
  haveI : Module.Finite k (dd.summand m) := dd.summand_finite (hRes (l j)) m
  haveI : IsLocalRing (End (dd.summand m)) :=
    MBDVendor.Magnitude.moduleCat_end_isLocalRing (k := k) (A := Cᵐᵒᵖ) _ (dd.indecomposable m)
  haveI := isIso_of_retract not_isZero_of_local i2 p2 h2
  let t : T := ⟨⟨l j, m⟩, M, hM, ⟨asIso i2⟩⟩
  refine ⟨eT t, ?_⟩
  have ht : eT.symm (eT t) = t := eT.symm_apply_apply t
  show Nonempty (M ≅ (eT.symm (eT t)).2.choose)
  rw [ht]
  exact ⟨(ModuleCat.restrictScalars (qOp C q)).preimageIso
    (asIso i2 ≪≫ t.2.choose_spec.2.some.symm)⟩

end MultiplicativeBasisDeformations
