module

public import Mathlib.RingTheory.Artinian.Ring
public import MBDVendor.QSE.RepresentationTheory.Trace

/-!
# The radical of an indecomposable endomorphism ring

The anti-exchange argument uses the Jacobson radical of the local
endomorphism ring of an indecomposable finite-length module.  Mathlib
proves that the Jacobson radical of an Artinian ring is nilpotent.  This
file identifies its elements with the noninvertible endomorphisms and
packages the iteration-on-images argument needed by the manuscript.
-/

@[expose] public section

noncomputable section

open Function

namespace MBDVendor.QSE

universe u v

variable {A : Type u} {X : Type v}
variable [Ring A] [AddCommGroup X] [Module A X]

/-- If a composite `X → Y → X` is invertible and both modules are
indecomposable, then the first map is a linear equivalence onto `Y`. -/
theorem nonempty_linearEquiv_of_isUnit_comp
    {Y : Type*} [AddCommGroup Y] [Module A Y]
    (hX : MBDVendor.QSE.Foundation.IsIndecomposableModule A X)
    (hY : MBDVendor.QSE.Foundation.IsIndecomposableModule A Y)
    (f : Y →ₗ[A] X) (g : X →ₗ[A] Y)
    (hunit : IsUnit (f.comp g)) :
    Nonempty (X ≃ₗ[A] Y) := by
  let e : X ≃ₗ[A] X :=
    { f.comp g,
      Equiv.ofBijective (f.comp g)
        ((Module.End.isUnit_iff _).mp hunit) with }
  let r : Y →ₗ[A] X := e.symm.toLinearMap.comp f
  have hrg : r.comp g = LinearMap.id := by
    ext x
    exact e.symm_apply_apply x
  let p : Module.End A Y := g.comp r
  have hp : IsIdempotentElem p := by
    change p * p = p
    rw [Module.End.mul_eq_comp]
    ext y
    simp only [p, LinearMap.comp_apply]
    have h := LinearMap.congr_fun hrg (r y)
    simpa using congrArg g h
  rcases hY.eq_zero_or_eq_one_of_isIdempotentElem hp with hp0 | hp1
  · have hg0 : g = 0 := by
      calc
        g = p.comp g := by
          ext x
          simp only [p, LinearMap.comp_apply]
          have h := LinearMap.congr_fun hrg x
          simpa using congrArg g h.symm
        _ = 0 := by rw [hp0, LinearMap.zero_comp]
    have hzero : (f.comp g : Module.End A X) = 0 := by
      simp [hg0]
    rw [hzero] at hunit
    letI := hX.nontrivial
    exact (not_isUnit_zero hunit).elim
  · exact ⟨
      { toLinearMap := g
        invFun := r
        left_inv := fun x => LinearMap.congr_fun hrg x
        right_inv := fun y => by
          have h := LinearMap.congr_fun hp1 y
          simpa [p, Module.End.one_apply] using h }⟩

/-- In a finite-length module, a right factor of an invertible composite
endomorphism is invertible. -/
theorem isUnit_right_of_isUnit_comp
    (hXlen : IsFiniteLength A X)
    (f g : Module.End A X)
    (hunit : IsUnit (f.comp g)) :
    IsUnit g := by
  obtain ⟨hNoetherian, hArtinian⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp hXlen
  letI : IsNoetherian A X := hNoetherian
  letI : IsArtinian A X := hArtinian
  have hcomp_bij : Function.Bijective (f.comp g) :=
    (Module.End.isUnit_iff _).mp hunit
  have hg_inj : Function.Injective g := by
    intro x y hxy
    exact hcomp_bij.1 (by simp [hxy])
  have hg_surj : Function.Surjective g :=
    IsArtinian.surjective_of_injective_endomorphism g hg_inj
  exact (Module.End.isUnit_iff g).mpr ⟨hg_inj, hg_surj⟩

/-- For a finite-length indecomposable, the nonunits in its endomorphism
ring form its unique maximal left ideal. -/
def endNonunitsIdeal
    (hX : MBDVendor.QSE.Foundation.IsIndecomposableModule A X)
    (hXlen : IsFiniteLength A X) :
    Ideal (Module.End A X) := by
  letI : Nontrivial X := hX.nontrivial
  letI : IsLocalRing (Module.End A X) :=
    MBDVendor.QSE.Foundation.isLocalRing_end_of_isIndecomposable hXlen hX
  exact
    { carrier := nonunits (Module.End A X)
      zero_mem' := not_isUnit_zero
      add_mem' := fun hx hy ↦ IsLocalRing.nonunits_add hx hy
      smul_mem' := by
        intro f g hg
        change ¬ IsUnit (f * g)
        rw [Module.End.mul_eq_comp]
        exact fun hfg ↦
          hg (isUnit_right_of_isUnit_comp hXlen f g hfg) }

@[simp]
theorem mem_endNonunitsIdeal_iff
    (hX : MBDVendor.QSE.Foundation.IsIndecomposableModule A X)
    (hXlen : IsFiniteLength A X)
    (f : Module.End A X) :
    f ∈ endNonunitsIdeal hX hXlen ↔ ¬ IsUnit f :=
  Iff.rfl

/-- The ideal of noninvertible endomorphisms is maximal. -/
theorem endNonunitsIdeal_isMaximal
    (hX : MBDVendor.QSE.Foundation.IsIndecomposableModule A X)
    (hXlen : IsFiniteLength A X) :
    (endNonunitsIdeal hX hXlen).IsMaximal := by
  letI : Nontrivial X := hX.nontrivial
  rw [Ideal.isMaximal_iff]
  constructor
  · change ¬ ¬ IsUnit (1 : Module.End A X)
    exact not_not_intro isUnit_one
  · intro J x _ hx hxJ
    have hxunit : IsUnit x := by
      rw [mem_endNonunitsIdeal_iff] at hx
      exact not_not.mp hx
    have hJtop : J = ⊤ := J.eq_top_of_isUnit_mem hxJ hxunit
    rw [hJtop]
    exact Set.mem_univ 1

/-- The Jacobson radical of the endomorphism ring is exactly its ideal
of noninvertible endomorphisms. -/
theorem end_jacobson_eq_nonunits
    (hX : MBDVendor.QSE.Foundation.IsIndecomposableModule A X)
    (hXlen : IsFiniteLength A X) :
    Ring.jacobson (Module.End A X) =
      endNonunitsIdeal hX hXlen := by
  letI : Nontrivial X := hX.nontrivial
  apply le_antisymm
  · letI : (endNonunitsIdeal hX hXlen).IsMaximal :=
      endNonunitsIdeal_isMaximal hX hXlen
    exact Ring.jacobson_le_of_isMaximal
      (endNonunitsIdeal hX hXlen)
  · rw [Ring.jacobson_eq_sInf_isMaximal]
    apply le_sInf
    intro J hJ
    have hJmax : J.IsMaximal := hJ
    have hJI : J ≤ endNonunitsIdeal hX hXlen := by
      intro f hf
      exact coe_subset_nonunits hJmax.ne_top hf
    have hEq : J = endNonunitsIdeal hX hXlen :=
      hJmax.eq_of_le
        (Ideal.IsMaximal.ne_top
          (endNonunitsIdeal_isMaximal hX hXlen))
        hJI
    exact hEq.ge

/-- An endomorphism of an indecomposable finite-length module belongs to
the Jacobson radical exactly when it is not invertible. -/
theorem mem_end_jacobson_iff_not_isUnit
    (hX : MBDVendor.QSE.Foundation.IsIndecomposableModule A X)
    (hXlen : IsFiniteLength A X)
    (f : Module.End A X) :
    f ∈ Ring.jacobson (Module.End A X) ↔ ¬ IsUnit f := by
  rw [end_jacobson_eq_nonunits hX hXlen]
  rfl

/-- The endomorphism ring of a module finite-dimensional over a central
ground field is Artinian. -/
theorem isArtinianRing_moduleEnd_of_finiteDimensional
    {K B M : Type*}
    [Field K] [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module B M]
    [IsScalarTower K B M] [FiniteDimensional K M] :
    IsArtinianRing (Module.End B M) := by
  letI : Module.Finite K (Module.End B M) :=
    Module.Finite.of_injective
      (LinearMap.restrictScalarsₗ K B M M K)
      (LinearMap.restrictScalars_injective K)
  exact isArtinian_of_tower K inferInstance

/-- The sum of the images of all endomorphisms in a left ideal. -/
def idealRange (I : Ideal (Module.End A X)) : Submodule A X :=
  ⨆ f : I, LinearMap.range (f : Module.End A X)

/-- Each ideal element's range belongs to the total ideal range. -/
theorem range_le_idealRange
    {I : Ideal (Module.End A X)}
    (f : Module.End A X) (hf : f ∈ I) :
    LinearMap.range f ≤ idealRange I :=
  le_iSup (fun g : I ↦ LinearMap.range
    (g : Module.End A X)) ⟨f, hf⟩

@[simp]
theorem idealRange_bot :
    idealRange (⊥ : Ideal (Module.End A X)) = ⊥ := by
  apply bot_unique
  apply iSup_le
  rintro ⟨f, hf⟩
  simp only [Ideal.mem_bot] at hf
  subst f
  simp

@[simp]
theorem idealRange_top :
    idealRange (⊤ : Ideal (Module.End A X)) = ⊤ := by
  apply top_unique
  calc
    (⊤ : Submodule A X) = LinearMap.range
        (1 : Module.End A X) := by
          rw [Module.End.one_eq_id, LinearMap.range_id]
    _ ≤ idealRange (⊤ : Ideal (Module.End A X)) :=
      range_le_idealRange 1 (Set.mem_univ 1)

/-- Acting by an element of `I` sends the range of `J` into the range
of the product ideal `I * J`. -/
theorem map_idealRange_le
    {I J : Ideal (Module.End A X)}
    (f : Module.End A X) (hf : f ∈ I) :
    Submodule.map f (idealRange J) ≤ idealRange (I * J) := by
  rw [idealRange, Submodule.map_iSup]
  apply iSup_le
  rintro ⟨g, hg⟩
  rw [← LinearMap.range_comp, ← Module.End.mul_eq_comp]
  exact range_le_idealRange (f * g)
    (Ideal.mul_mem_mul hf hg)

/-- Nilpotence of an ideal, together with a fully invariant submodule
and generation modulo that submodule by the ideal's images, forces the
submodule to be the whole module. -/
theorem eq_top_of_nilpotent_idealRange
    (I : Ideal (Module.End A X)) [I.IsTwoSided]
    (T : Submodule A X)
    (hT : ∀ f : Module.End A X, Submodule.map f T ≤ T)
    (hI : IsNilpotent I)
    (hsup : T ⊔ idealRange I = ⊤) :
    T = ⊤ := by
  have hpowers :
      ∀ n : ℕ, T ⊔ idealRange (I ^ n) = ⊤ := by
    intro n
    induction n with
    | zero =>
        rw [Submodule.pow_zero, Ideal.one_eq_top, idealRange_top,
          sup_top_eq]
    | succ n hn =>
        apply top_unique
        rw [← hn]
        apply sup_le
        · exact le_sup_left
        apply iSup_le
        rintro ⟨f, hf⟩
        rw [← Submodule.map_top, ← hsup, Submodule.map_sup]
        apply sup_le_sup
        · exact hT f
        · rw [Submodule.pow_succ]
          exact map_idealRange_le f hf
  obtain ⟨n, hn⟩ := hI
  have hfinal := hpowers n
  have hnbot : I ^ n = ⊥ := by
    simpa only [Ideal.zero_eq_bot] using hn
  rw [hnbot, idealRange_bot, sup_bot_eq] at hfinal
  exact hfinal

/-- The common kernel of all endomorphisms in a left ideal. -/
def idealKernel (I : Ideal (Module.End A X)) : Submodule A X :=
  ⨅ f : I, LinearMap.ker (f : Module.End A X)

/-- The common ideal kernel lies in the kernel of each ideal element. -/
theorem idealKernel_le_ker
    {I : Ideal (Module.End A X)}
    (f : Module.End A X) (hf : f ∈ I) :
    idealKernel I ≤ LinearMap.ker f :=
  iInf_le (fun g : I ↦ LinearMap.ker
    (g : Module.End A X)) ⟨f, hf⟩

@[simp]
theorem idealKernel_bot :
    idealKernel (⊥ : Ideal (Module.End A X)) = ⊤ := by
  apply top_unique
  apply le_iInf
  rintro ⟨f, hf⟩
  simp only [Ideal.mem_bot] at hf
  subst f
  simp

@[simp]
theorem idealKernel_top :
    idealKernel (⊤ : Ideal (Module.End A X)) = ⊥ := by
  apply bot_unique
  calc
    idealKernel (⊤ : Ideal (Module.End A X)) ≤
        LinearMap.ker (1 : Module.End A X) :=
      idealKernel_le_ker 1 (Set.mem_univ 1)
    _ = ⊥ := by
      rw [Module.End.one_eq_id, LinearMap.ker_id]

/-- If a fully invariant submodule meets the common kernel of a
nilpotent ideal trivially, then the submodule itself is trivial. -/
theorem eq_bot_of_inf_idealKernel
    (I : Ideal (Module.End A X)) [I.IsTwoSided]
    (K : Submodule A X)
    (hK : ∀ f : Module.End A X, Submodule.map f K ≤ K)
    (hI : IsNilpotent I)
    (hinf : K ⊓ idealKernel I = ⊥) :
    K = ⊥ := by
  have hpowers :
      ∀ n : ℕ, K ⊓ idealKernel (I ^ n) = ⊥ := by
    intro n
    induction n with
    | zero =>
        rw [Submodule.pow_zero, Ideal.one_eq_top, idealKernel_top,
          inf_bot_eq]
    | succ n hn =>
        apply le_bot_iff.mp
        intro x hx
        have hxK : x ∈ K := hx.1
        have hxkerI : x ∈ idealKernel I := by
          rw [idealKernel, Submodule.mem_iInf]
          rintro ⟨q, hq⟩
          rw [LinearMap.mem_ker]
          have hqxK : q x ∈ K := by
            exact hK q ⟨x, hxK, rfl⟩
          have hqxker : q x ∈ idealKernel (I ^ n) := by
            rw [idealKernel, Submodule.mem_iInf]
            rintro ⟨p, hp⟩
            rw [LinearMap.mem_ker]
            have hpq : p * q ∈ I ^ (n + 1) := by
              rw [Submodule.pow_succ]
              exact Ideal.mul_mem_mul hp hq
            have hzero :=
              idealKernel_le_ker (p * q) hpq hx.2
            rw [LinearMap.mem_ker, Module.End.mul_eq_comp,
              LinearMap.comp_apply] at hzero
            exact hzero
          have hzero : q x = 0 := by
            have hmem : q x ∈
                K ⊓ idealKernel (I ^ n) :=
              ⟨hqxK, hqxker⟩
            rw [hn] at hmem
            exact hmem
          exact hzero
        have hxbot : x ∈ (⊥ : Submodule A X) := by
          rw [← hinf]
          exact ⟨hxK, hxkerI⟩
        exact hxbot
  obtain ⟨n, hn⟩ := hI
  have hfinal := hpowers n
  have hnbot : I ^ n = ⊥ := by
    simpa only [Ideal.zero_eq_bot] using hn
  rw [hnbot, idealKernel_bot, inf_top_eq] at hfinal
  exact hfinal

end MBDVendor.QSE
