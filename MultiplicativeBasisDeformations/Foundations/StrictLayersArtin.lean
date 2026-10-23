module

public import MultiplicativeBasisDeformations.Foundations.KrullSchmidtForm
public import MBDVendor.Magnitude.Algebra.FiniteModuleDecomposition
public import MBDVendor.Magnitude.Algebra.IndecomposableLocalEnd
public import Mathlib.RingTheory.Length

/-!
# Lemma 2.5 for an Artin algebra

`lem:strict-radical-layers` (`graded-category.tex`): "Let `A` be any Artin algebra, let `J` be
the radical of its category of finite-length modules […]". The manuscript assumes ordinary
Auslander–Reiten theory (`main.tex`): every indecomposable module `Y` has a right almost split
map `E → Y`, with kernel `0` (`rad P → P` at projectives) or a left almost split map out of the
indecomposable `τY` (the almost split sequence). With this input (`ARData`), Lemma 2.5 holds in
the category of finitely generated modules over an Artin algebra (`strict_radical_layers_artin`).

The Krull–Schmidt input is proved: finitely generated modules are finite biproducts of
indecomposables (induction on the length, `decomp_module`), whose endomorphism rings are local
(Fitting, `end_isLocalRing`); the split–radical normal form and the right radical approximations
then come from `KrullSchmidtForm`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.Magnitude MBDVendor.Magnitude.CategoryTheory

namespace MultiplicativeBasisDeformations.StrictLayers

universe u

variable {A : Type u} [Ring A]

/-- **Fitting**: the endomorphism ring of an indecomposable finite-length module is local. -/
theorem end_isLocalRing (M : ModuleCat.{u} A) [IsArtinian A M] [IsNoetherian A M]
    (hM : Indecomposable M) : IsLocalRing (End M) := by
  have hnsub : ¬ Subsingleton M := (not_iff_not.2 ModuleCat.isZero_iff_subsingleton).1 hM.1
  letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hnsub
  letI : Nontrivial (End M) := (ModuleCat.endRingEquiv M).symm.injective.nontrivial
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  let φ : Module.End A M := f.hom
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp φ.eventually_isCompl_ker_pow_range_pow
  let n := N + 1
  have hcompl : IsCompl (LinearMap.ker (φ ^ n)) (LinearMap.range (φ ^ n)) := hN n (Nat.le_succ N)
  let K : ModuleCat.{u} A := ModuleCat.of A (LinearMap.ker (φ ^ n))
  let R : ModuleCat.{u} A := ModuleCat.of A (LinearMap.range (φ ^ n))
  let eProd : ModuleCat.of A (LinearMap.ker (φ ^ n) × LinearMap.range (φ ^ n)) ≅ M :=
    (Submodule.prodEquivOfIsCompl _ _ hcompl).toModuleIso
  let e : M ≅ K ⊞ R := eProd.symm.trans (ModuleCat.biprodIsoProd K R).symm
  rcases hM.2 K R e with hK | hR
  · left
    have hker : LinearMap.ker (φ ^ n) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      haveI : Subsingleton K := ModuleCat.subsingleton_of_isZero hK
      exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : K) 0)
    have hkerle : LinearMap.ker φ ≤ LinearMap.ker (φ ^ n) := by
      simpa using φ.iterateKer.monotone (show 0 < n by simp [n])
    have hfinj : Function.Injective φ :=
      LinearMap.ker_eq_bot.mp (le_antisymm (hkerle.trans_eq hker) bot_le)
    have hfsurj : Function.Surjective φ := IsArtinian.surjective_of_injective_endomorphism φ hfinj
    apply (isUnit_map_iff (ModuleCat.endRingEquiv M) f).mp
    exact (Module.End.isUnit_iff φ).2 ⟨hfinj, hfsurj⟩
  · right
    have hrange : LinearMap.range (φ ^ n) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      haveI : Subsingleton R := ModuleCat.subsingleton_of_isZero hR
      exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : R) 0)
    refine IsNilpotent.isUnit_one_sub ⟨n, ?_⟩
    apply (ModuleCat.endRingEquiv M).injective
    rw [map_pow, map_zero]
    exact LinearMap.range_eq_bot.mp hrange

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- A split summand of a finite-length module has finite length. -/
theorem fl_of_split {M X : ModuleCat.{u} A} [IsArtinian A M] [IsNoetherian A M] (i : X ⟶ M)
    (q : M ⟶ X) (hiq : i ≫ q = 𝟙 X) : IsArtinian A X ∧ IsNoetherian A X := by
  have hinj : Function.Injective i.hom := fun x y h ↦ by
    have := congrArg q.hom h
    simpa [← ModuleCat.comp_apply, hiq] using this
  exact ⟨isArtinian_of_injective i.hom hinj, isNoetherian_of_injective i.hom hinj⟩

/-- **Krull–Schmidt existence**: a finite-length module is a finite biproduct of indecomposables,
by induction on the length. -/
theorem decomp_module : ∀ (d : ℕ) (M : ModuleCat.{u} A) [IsArtinian A M] [IsNoetherian A M],
    (Module.length A M).toNat = d → Nonempty (FiniteIndecomposableDecomposition M) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ hd
  by_cases hMzero : IsZero M
  · exact ⟨{ n := 0
             summand := fun i ↦ Fin.elim0 i
             indecomposable := fun i ↦ Fin.elim0 i
             isoBiproduct := zeroIsoEmptyBiproduct M hMzero }⟩
  by_cases hMind : Indecomposable M
  · exact ⟨FiniteIndecomposableDecomposition.singleton M hMind⟩
  have hsplit : ∃ X Y : ModuleCat.{u} A, ∃ e : M ≅ X ⊞ Y, ¬ IsZero X ∧ ¬ IsZero Y := by
    rw [Indecomposable] at hMind
    push Not at hMind
    exact hMind hMzero
  obtain ⟨X, Y, e, hX0, hY0⟩ := hsplit
  obtain ⟨hXa, hXn⟩ := fl_of_split (biprod.inl ≫ e.inv) (e.hom ≫ biprod.fst) (by simp)
  obtain ⟨hYa, hYn⟩ := fl_of_split (biprod.inr ≫ e.inv) (e.hom ≫ biprod.snd) (by simp)
  let eLin : M ≃ₗ[A] X × Y := (e.trans (ModuleCat.biprodIsoProd X Y)).toLinearEquiv
  have hlen : Module.length A M = Module.length A X + Module.length A Y := by
    rw [eLin.length_eq, Module.length_prod]
  have hXnt : Nontrivial X := not_subsingleton_iff_nontrivial.mp
    ((not_iff_not.mpr ModuleCat.isZero_iff_subsingleton).mp hX0)
  have hYnt : Nontrivial Y := not_subsingleton_iff_nontrivial.mp
    ((not_iff_not.mpr ModuleCat.isZero_iff_subsingleton).mp hY0)
  have hXf : Module.length A X ≠ ⊤ := Module.length_ne_top
  have hYf : Module.length A Y ≠ ⊤ := Module.length_ne_top
  have hXp : 0 < (Module.length A X).toNat := by
    exact ENat.toNat_pos (Module.length_pos (R := A) (M := X)).ne' hXf
  have hYp : 0 < (Module.length A Y).toNat := by
    exact ENat.toNat_pos (Module.length_pos (R := A) (M := Y)).ne' hYf
  have hdsum : d = (Module.length A X).toNat + (Module.length A Y).toNat := by
    rw [← hd, hlen, ENat.toNat_add hXf hYf]
  obtain ⟨dX⟩ := ih _ (by omega) X rfl
  obtain ⟨dY⟩ := ih _ (by omega) Y rfl
  exact ⟨(dX.biprod dY).ofIso e⟩

/-! ### Finitely generated modules over an Artin algebra -/

section Artin

variable (R : Type u) [CommRing R] [IsArtinianRing R] [Algebra R A] [Module.Finite R A]

include R in
theorem artin_isArtinianRing : IsArtinianRing A := IsArtinianRing.of_finite R A

include R in
theorem artin_isNoetherianRing : IsNoetherianRing A := isNoetherian_of_tower R inferInstance

include R in
/-- **Krull–Schmidt for an Artin algebra**: every finitely generated module is a finite biproduct
of nonzero modules with local endomorphism rings. -/
theorem decomp_artin [IsNoetherianRing A] (X : FGModuleCat.{u} A) : ∃ (n : ℕ) (F : Fin n → FGModuleCat.{u} A),
    (∀ i, ¬ IsZero (F i) ∧ IsLocalRing (End (F i))) ∧ Nonempty (X ≅ ⨁ F) := by
  have := artin_isArtinianRing (A := A) R
  let U := forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)
  letI : U.Additive := ⟨by intros; rfl⟩
  obtain ⟨d⟩ := decomp_module _ X.obj rfl
  have hfl : ∀ j, IsArtinian A (d.summand j) ∧ IsNoetherian A (d.summand j) := fun j ↦
    fl_of_split (biproduct.ι d.summand j ≫ d.isoBiproduct.inv)
      (d.isoBiproduct.hom ≫ biproduct.π d.summand j) (by simp)
  let F : Fin d.n → FGModuleCat.{u} A := fun j ↦ by
    haveI := (hfl j).2
    exact FGModuleCat.of A (d.summand j)
  have hInd : ∀ j, Indecomposable (F j) := fun j ↦
    indecomposable_of_fully_faithful_additive U (F j) (d.indecomposable j)
  refine ⟨d.n, F, fun j ↦ ⟨(hInd j).1, ?_⟩,
    ⟨U.preimageIso (d.isoBiproduct.trans (U.mapBiproduct F).symm)⟩⟩
  have := (hfl j).1
  have := (hfl j).2
  have : IsLocalRing (End (U.obj (F j))) := by
    change IsLocalRing (End (d.summand j))
    exact end_isLocalRing _ (d.indecomposable j)
  exact RingEquiv.isLocalRing_noncomm (U.endRingEquivOfFullyFaithful (F j)).symm

include R in
/-- **Lemma 2.5** (`lem:strict-radical-layers`) **for an Artin algebra** `A` over a commutative
Artinian ring `R`, in the category of finitely generated (finite-length) modules, with ordinary
Auslander–Reiten theory as input (`hAR`, assumed by the manuscript, `main.tex`): for a radical
monomorphism-type map `a : U → Y` with `a + h` monic for all `h ∈ J²(U, Y)`, `z ≫ a ∈ J^{n+1}`
implies `z ∈ J^n`. -/
theorem strict_radical_layers_artin [IsNoetherianRing A]
    (hAR : ∀ Y : FGModuleCat.{u} A, ¬ IsZero Y → IsLocalRing (End Y) → Nonempty (ARData Y))
    (n : ℕ) {U Y : FGModuleCat.{u} A} (a : U ⟶ Y)
    (ha : MBDVendor.QSE.CategoricalRadical.IsRadicalMorphism a)
    (hpert : ∀ h ∈ (Ipow 2 : MBDVendor.QSE.CategoricalIdeal.HomIdeal (FGModuleCat.{u} A)).hom U Y,
      Mono (a + h))
    {W : FGModuleCat.{u} A} (z : W ⟶ U)
    (hz : z ≫ a ∈ (Ipow (n + 1) : MBDVendor.QSE.CategoricalIdeal.HomIdeal _).hom W Y) :
    z ∈ (Ipow n : MBDVendor.QSE.CategoricalIdeal.HomIdeal _).hom W U :=
  strict_of_AR (decomp_artin R) hAR n a ha hpert z hz

include R in
/-- **Lemma 2.5** (`lem:strict-radical-layers`) as stated, both directions: for a radical
monomorphism `a` all of whose perturbations by `J²` are monic, `z ≫ a ∈ J^{n+1}` if and only if
`z ∈ J^n`. -/
theorem strict_radical_layers_artin_iff [IsNoetherianRing A]
    (hAR : ∀ Y : FGModuleCat.{u} A, ¬ IsZero Y → IsLocalRing (End Y) → Nonempty (ARData Y))
    (n : ℕ) {U Y : FGModuleCat.{u} A} (a : U ⟶ Y)
    (ha : MBDVendor.QSE.CategoricalRadical.IsRadicalMorphism a)
    (hpert : ∀ h ∈ (Ipow 2 : MBDVendor.QSE.CategoricalIdeal.HomIdeal (FGModuleCat.{u} A)).hom U Y,
      Mono (a + h))
    {W : FGModuleCat.{u} A} (z : W ⟶ U) :
    z ≫ a ∈ (Ipow (n + 1) : MBDVendor.QSE.CategoricalIdeal.HomIdeal _).hom W Y ↔
      z ∈ (Ipow n : MBDVendor.QSE.CategoricalIdeal.HomIdeal _).hom W U :=
  ⟨strict_radical_layers_artin R hAR n a ha hpert z, comp_mem_of_mem ha⟩

end Artin

end MultiplicativeBasisDeformations.StrictLayers
