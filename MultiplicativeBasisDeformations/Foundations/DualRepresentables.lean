module

public import MultiplicativeBasisDeformations.Foundations.CategoryAlgebra

/-!
# Dual representables and injective copresentations

For the category algebra `Λ` of a family `F`, the dual representable
`J_p = (D C(F p, F q))_q` is the module `D(e_p Λ)` (in the manuscript's
right-module notation `D(Λ e_p)`, `graded-category.tex`). A
functional `λ` on a module `X` gives `θ_λ : X → J_p`,
`θ_λ(x)_q(h) = λ(h · x)`. Every finite-dimensional module embeds into a finite
sum of the `J_p`, which gives the injective copresentations used in Lemma 2.9.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → 𝒞)

/-- The dual representable `J_p`. -/
def DRep (p : ι) := ∀ q : ι, Module.Dual k (F p ⟶ F q)

instance (p : ι) : AddCommGroup (DRep (k := k) F p) :=
  inferInstanceAs (AddCommGroup (∀ q : ι, Module.Dual k (F p ⟶ F q)))

instance (p : ι) : Module k (DRep (k := k) F p) :=
  inferInstanceAs (Module k (∀ q : ι, Module.Dual k (F p ⟶ F q)))

instance (p : ι) [∀ x y : ι, FiniteDimensional k (F x ⟶ F y)] :
    FiniteDimensional k (DRep (k := k) F p) :=
  inferInstanceAs (FiniteDimensional k (∀ q : ι, Module.Dual k (F p ⟶ F q)))

variable {F}

@[simp] theorem DRep.add_apply {p : ι} (φ ψ : DRep (k := k) F p) (q : ι) : (φ + ψ) q = φ q + ψ q :=
  rfl
@[simp] theorem DRep.zero_apply {p : ι} (q : ι) : (0 : DRep (k := k) F p) q = 0 := rfl
@[simp] theorem DRep.smulk_apply {p : ι} (c : k) (φ : DRep (k := k) F p) (q : ι) :
    (c • φ) q = c • φ q := rfl

/-- Postcomposition, as a linear map. -/
def postL {X Y Z : 𝒞} (g : Y ⟶ Z) : (X ⟶ Y) →ₗ[k] (X ⟶ Z) where
  toFun h := h ≫ g
  map_add' a b := Preadditive.add_comp _ _ _ _ _ _
  map_smul' c a := Linear.smul_comp _ _ _ _ _ _

@[simp] theorem postL_apply {X Y Z : 𝒞} (g : Y ⟶ Z) (h : X ⟶ Y) : postL (k := k) g h = h ≫ g := rfl

instance (p : ι) : SMul (Alg F) (DRep (k := k) F p) :=
  ⟨fun a φ q ↦ ∑ r, (φ r).comp (postL (a q r))⟩

theorem DRep.smul_apply {p : ι} (a : Alg F) (φ : DRep (k := k) F p) (q : ι) (h : F p ⟶ F q) :
    (a • φ) q h = ∑ r, φ r (h ≫ a q r) := by
  change (∑ r, (φ r).comp (postL (a q r))) h = _
  rw [LinearMap.sum_apply]
  rfl

@[ext] theorem DRep.ext {p : ι} {φ ψ : DRep (k := k) F p} (h : ∀ q x, φ q x = ψ q x) : φ = ψ :=
  funext fun q ↦ LinearMap.ext (h q)

instance (p : ι) : Module (Alg F) (DRep (k := k) F p) where
  one_smul φ := by
    ext q h
    rw [DRep.smul_apply]
    simp only [one_apply]
    rw [Finset.sum_eq_single q]
    · simp
    · intro r _ hr; rw [idTo_ne (Ne.symm hr), Limits.comp_zero, map_zero]
    · simp
  mul_smul a b φ := by
    ext q h
    simp only [DRep.smul_apply, mul_apply, Preadditive.comp_sum, map_sum, Category.assoc]
    exact Finset.sum_comm
  smul_zero a := by ext q h; simp [DRep.smul_apply]
  smul_add a φ ψ := by
    ext q h
    simp only [DRep.smul_apply, DRep.add_apply, LinearMap.add_apply, Finset.sum_add_distrib]
  add_smul a b φ := by
    ext q h
    simp only [DRep.smul_apply, add_apply, Preadditive.comp_add, map_add, Finset.sum_add_distrib,
      DRep.add_apply, LinearMap.add_apply]
  zero_smul φ := by ext q h; simp [DRep.smul_apply]

instance (p : ι) : IsScalarTower k (Alg F) (DRep (k := k) F p) where
  smul_assoc c a φ := by
    ext q h
    rw [DRep.smul_apply, DRep.smulk_apply, LinearMap.smul_apply, DRep.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [smul_apply, Linear.comp_smul, map_smul]

/-- The element of `Λ` with the single entry `h : F p → F q`. -/
def elemAt (p q : ι) (h : F p ⟶ F q) : Alg F := fun y z ↦ idTo y p ≫ h ≫ idTo q z

theorem elemAt_mul (p q : ι) (h : F p ⟶ F q) (a : Alg F) :
    elemAt p q h * a = ∑ r, elemAt p r (h ≫ a q r) := by
  ext y z
  rw [sum_apply, mul_apply]
  simp only [elemAt, Category.assoc]
  rw [← Preadditive.comp_sum, ← Preadditive.comp_sum, ← Preadditive.comp_sum,
    ← Preadditive.comp_sum, sum_idTo_comp_alg, sum_comp_idTo_alg]

theorem elemAt_id (p : ι) : elemAt (F := F) p p (𝟙 _) = idem p := by
  ext y z; simp [elemAt, idem, colAlg, unit]

theorem elemAt_add (p q : ι) (h h' : F p ⟶ F q) :
    elemAt (F := F) p q (h + h') = elemAt p q h + elemAt p q h' := by
  ext y z; simp [elemAt, Preadditive.add_comp, Preadditive.comp_add]

theorem elemAt_smul (p q : ι) (c : k) (h : F p ⟶ F q) :
    elemAt (F := F) p q (c • h) = c • elemAt p q h := by
  ext y z; simp [elemAt]

variable {X : Type*} [AddCommGroup X] [Module k X] [Module (Alg F) X] [IsScalarTower k (Alg F) X]

/-- The values of `θ_λ`. -/
def thetaFun (p : ι) (lam : Module.Dual k X) (x : X) : DRep (k := k) F p := fun q ↦
  { toFun h := lam (elemAt p q h • x)
    map_add' h h' := by rw [elemAt_add, add_smul, map_add]
    map_smul' c h := by rw [elemAt_smul, smul_assoc, map_smul]; rfl }

theorem thetaFun_apply (p : ι) (lam : Module.Dual k X) (x : X) (q : ι) (h : F p ⟶ F q) :
    thetaFun (F := F) p lam x q h = lam (elemAt p q h • x) := rfl

/-- `θ_λ : X → J_p`, `θ_λ(x)_q(h) = λ(h · x)`. -/
def theta (p : ι) (lam : Module.Dual k X) : X →ₗ[Alg F] DRep (k := k) F p where
  toFun x := thetaFun p lam x
  map_add' x y := by
    ext q h
    rw [DRep.add_apply, LinearMap.add_apply, thetaFun_apply, thetaFun_apply, thetaFun_apply,
      smul_add, map_add]
  map_smul' a x := by
    ext q h
    rw [RingHom.id_apply, DRep.smul_apply, thetaFun_apply, smul_smul, elemAt_mul, Finset.sum_smul,
      map_sum]
    rfl

theorem theta_apply (p : ι) (lam : Module.Dual k X) (x : X) (q : ι) (h : F p ⟶ F q) :
    theta (F := F) p lam x q h = lam (elemAt p q h • x) := rfl

theorem sum_idem_eq_one : ∑ x, idem (F := F) x = 1 := by
  ext y z
  rw [sum_apply, one_apply]
  simp only [idem, colAlg, unit]
  exact sum_idTo_comp y (fun x ↦ idTo (F := F) x z)

theorem eq_zero_of_idem {x : X} (h : ∀ p, idem (F := F) p • x = 0) : x = 0 := by
  rw [← one_smul (Alg F) x, ← sum_idem_eq_one (F := F), Finset.sum_smul]
  exact Finset.sum_eq_zero fun p _ ↦ h p

/-- **Every finite-dimensional module embeds into a finite sum of dual
representables.** -/
theorem exists_embedding [FiniteDimensional k X] :
    ∃ (n : ℕ) (e : X →ₗ[Alg F] (∀ c : ι × Fin n, DRep (k := k) F c.1)), Function.Injective e := by
  set b := Module.finBasis k (Module.Dual k X)
  refine ⟨Module.finrank k (Module.Dual k X), LinearMap.pi fun c ↦ theta c.1 (b c.2), ?_⟩
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  apply eq_zero_of_idem (F := F)
  intro p
  have hb : ∀ i, b i (idem (F := F) p • x) = 0 := fun i ↦ by
    have := congrArg (fun φ : ∀ c : ι × Fin _, DRep (k := k) F c.1 ↦ φ (p, i) p (𝟙 _)) hx
    simp only [LinearMap.pi_apply] at this
    rw [show (0 : ∀ c : ι × Fin _, DRep (k := k) F c.1) (p, i) p (𝟙 _) = 0 from rfl,
      theta_apply, elemAt_id] at this
    exact this
  rw [← Module.forall_dual_apply_eq_zero_iff k]
  intro lam
  rw [← b.sum_repr lam, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [LinearMap.smul_apply, hb i, smul_zero]

end CatAlg

end MultiplicativeBasisDeformations
