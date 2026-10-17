import MultiplicativeBasisDeformations.Foundations.A0Normed
import MultiplicativeBasisDeformations.Foundations.GradedExt
import MultiplicativeBasisDeformations.Foundations.InjectiveLabels

/-!
# `A₀` and its evaluated modules as graded objects

Section 6 (`positive-deformations.tex:91–98`): "Let `M_1, …, M_h` be the
degree-normalized graded indecomposable `A₀`-modules obtained by evaluating the
objects of `C`: the degree-`d` part at `x` is `C_d(P_x, X_i)`." Here `A₀ =
(Alg F₀)ᵒᵖ` is `ℤ`-graded through `lenA0` (`galgA0`), and the evaluation
`M_X = Rep F₀ X` of an object `X` of the mesh category is a graded right
`A₀`-module (`gmodEv`), with `m·a = a.unop • m`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace GExt

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Algebra k B]

/-- A length grading as a `ℤ`-grading. -/
def ZGr.ofLen (G : LenGrading k B) : ZGr (R := k) B where
  proj p := if 0 ≤ p then G.proj p.toNat else 0
  supp := (Finset.range G.N).map Nat.castEmbedding
  proj_proj p q m := by
    by_cases hq : 0 ≤ q
    · by_cases hp : 0 ≤ p
      · simp only [if_pos hp, if_pos hq, G.proj_proj]
        by_cases h : q = p
        · subst h; simp
        · rw [if_neg (by omega), if_neg h]
      · simp [if_neg hp, show q ≠ p by omega]
    · simp [if_neg hq]
  proj_out p hp := by
    by_cases h0 : 0 ≤ p
    · rw [if_pos h0, G.proj_ge]
      by_contra hlt
      exact hp (Finset.mem_map.2 ⟨p.toNat, Finset.mem_range.2 (by omega), by simp; omega⟩)
    · rw [if_neg h0]
  sum m := by
    rw [Finset.sum_map]
    conv_lhs => rw [G.sum m]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    simp

theorem ZGr.ofLen_isHom (G : LenGrading k B) (d : ℕ) (b : B) :
    (ZGr.ofLen G).IsHom d b ↔ G.IsHom d b := by
  simp [ZGr.IsHom, ZGr.ofLen, LenGrading.IsHom]

theorem ZGr.ofLen_isHom_neg (G : LenGrading k B) {p : ℤ} (hp : p < 0) (b : B) :
    (ZGr.ofLen G).IsHom p b ↔ b = 0 := by
  simp [ZGr.IsHom, ZGr.ofLen, if_neg (show ¬ 0 ≤ p by omega), eq_comm]

/-- A length-graded algebra (with `1` in degree `0`) as a graded algebra. -/
def GAlg.ofLen (G : LenGrading k B) (h1 : G.IsHom 0 (1 : B)) : GAlg (R := k) B where
  gr := ZGr.ofLen G
  mul_hom p q a b ha hb := by
    rcases lt_or_ge p 0 with hp | hp
    · rw [(ZGr.ofLen_isHom_neg G hp a).1 ha, zero_mul]; exact (ZGr.ofLen G).isHom_zero _
    rcases lt_or_ge q 0 with hq | hq
    · rw [(ZGr.ofLen_isHom_neg G hq b).1 hb, mul_zero]; exact (ZGr.ofLen G).isHom_zero _
    obtain ⟨p', rfl⟩ := Int.eq_ofNat_of_zero_le hp
    obtain ⟨q', rfl⟩ := Int.eq_ofNat_of_zero_le hq
    rw [ZGr.ofLen_isHom] at ha hb
    have := G.isHom_mul ha hb
    rw [show (p' : ℤ) + q' = ((p' + q' : ℕ) : ℤ) by push_cast; ring, ZGr.ofLen_isHom]
    exact this
  one_hom := by simpa using (ZGr.ofLen_isHom G 0 1).2 h1

end GExt

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))

theorem one_isHom : (lenA0 D hfin).IsHom 0 (1 : (Alg D.F0)ᵐᵒᵖ) := by
  change projA0 D 0 1 = 1
  apply MulOpposite.unop_injective
  apply CatAlg.ext; intro p q
  rw [projA0_apply]
  exact degProj_of_mem c (idTo_mem_degreePart D p q) |>.trans (if_pos rfl)

/-- **`A₀` as a graded algebra.** -/
abbrev galgA0 : GExt.GAlg (R := k) (Alg D.F0)ᵐᵒᵖ := GExt.GAlg.ofLen (lenA0 D hfin) (one_isHom D hfin)

/-- The degree bound of the mesh category. -/
def Nb : ℕ := Classical.choose (exists_degreePart_eq_bot c hfin)

theorem Nb_spec : ∀ d x y, Nb hfin ≤ d → degreePart c d x y = ⊥ :=
  Classical.choose_spec (exists_degreePart_eq_bot c hfin)

/-- Degree projection on an evaluated module. -/
def repProj (d : ℕ) (X : V) : Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c X) :=
  LinearMap.pi fun y ↦ degProj c d y.1 X ∘ₗ LinearMap.proj (R := k)
    (φ := fun y : D.PV ↦ D.F0 y ⟶ meshFam Q c X) y

theorem repProj_apply (d : ℕ) (X : V) (m : Rep D.F0 (meshFam Q c X)) (y : D.PV) :
    repProj D d X m y = degProj c d y.1 X (m y) := rfl

/-- The grading of the evaluated module `M_X`. -/
def zgrEv (X : V) : GExt.ZGr (R := k) (Rep D.F0 (meshFam Q c X)) where
  proj p := if 0 ≤ p then repProj D p.toNat X else 0
  supp := (Finset.range (Nb hfin)).map Nat.castEmbedding
  proj_proj p q m := by
    by_cases hq : 0 ≤ q
    · by_cases hp : 0 ≤ p
      · simp only [if_pos hp, if_pos hq]
        funext y
        simp only [repProj_apply]
        rw [degProj_of_mem c (degProj_mem c _ _)]
        by_cases h : q = p
        · subst h; simp [repProj_apply]
        · rw [if_neg (by omega), if_neg h]; rfl
      · simp only [if_neg hp, if_pos hq, LinearMap.zero_apply]
        rw [if_neg (by omega)]
    · simp [if_neg hq]
  proj_out p hp := by
    by_cases h0 : 0 ≤ p
    · rw [if_pos h0]
      ext m y
      simp only [repProj_apply, LinearMap.zero_apply]
      have := degProj_mem c p.toNat (m y)
      rw [Nb_spec hfin p.toNat _ _ (by
        by_contra hlt
        exact hp (Finset.mem_map.2 ⟨p.toNat, Finset.mem_range.2 (by omega), by simp; omega⟩)),
        Submodule.mem_bot] at this
      rw [this]; rfl
    · rw [if_neg h0]
  sum m := by
    rw [Finset.sum_map]
    funext y
    rw [Rep.sum_apply]
    conv_lhs => rw [eq_sum_degProj c (Nb_spec hfin) (m y)]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    simp [repProj_apply]

theorem zgrEv_isHom (X : V) (d : ℕ) (m : Rep D.F0 (meshFam Q c X)) :
    (zgrEv D hfin X).IsHom d m ↔ ∀ y, m y ∈ degreePart c d y.1 X := by
  simp only [GExt.ZGr.IsHom, zgrEv, Nat.cast_nonneg, if_true, Int.toNat_natCast]
  constructor
  · intro h y
    rw [← congrFun h y]
    exact degProj_mem c d _
  · intro h
    funext y
    rw [repProj_apply, degProj_of_mem c (h y), if_pos rfl]

theorem zgrEv_isHom_neg (X : V) {p : ℤ} (hp : p < 0) (m : Rep D.F0 (meshFam Q c X)) :
    (zgrEv D hfin X).IsHom p m ↔ m = 0 := by
  simp [GExt.ZGr.IsHom, zgrEv, if_neg (show ¬ 0 ≤ p by omega), eq_comm]

theorem galgA0_isHom (d : ℕ) (a : (Alg D.F0)ᵐᵒᵖ) :
    (galgA0 D hfin).gr.IsHom d a ↔ ∀ y z, a.unop y z ∈ degreePart c d y.1 z.1 := by
  change (GExt.ZGr.ofLen (lenA0 D hfin)).IsHom d a ↔ _
  rw [GExt.ZGr.ofLen_isHom]
  constructor
  · intro h y z
    rw [← h]
    exact degProj_mem c d _
  · intro h
    apply MulOpposite.unop_injective
    apply CatAlg.ext; intro y z
    change degProj c d y.1 z.1 (a.unop y z) = a.unop y z
    rw [degProj_of_mem c (h y z), if_pos rfl]

theorem galgA0_isHom_neg {p : ℤ} (hp : p < 0) (a : (Alg D.F0)ᵐᵒᵖ) :
    (galgA0 D hfin).gr.IsHom p a ↔ a = 0 :=
  GExt.ZGr.ofLen_isHom_neg _ hp a

/-- The right `A₀`-action `m·a = a.unop • m`. -/
def evAct (X : V) :
    Rep D.F0 (meshFam Q c X) →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] Rep D.F0 (meshFam Q c X) :=
  LinearMap.mk₂ k (fun m a ↦ a.unop • m) (fun m m' a ↦ smul_add _ _ _)
    (fun c m a ↦ smul_comm _ _ _) (fun m a a' ↦ by simp [add_smul])
    (fun c m a ↦ by simp [smul_assoc])

/-- **The evaluated module `M_X` as a graded right `A₀`-module.** -/
def gmodEv (X : V) : GExt.GMod (galgA0 D hfin) (Rep D.F0 (meshFam Q c X)) where
  act := evAct D X
  act_one m := one_smul _ _
  act_mul m a b := by simp [evAct, mul_smul]
  gr := zgrEv D hfin X
  act_hom p q m a hm ha := by
    rcases lt_or_ge p 0 with hp | hp
    · rw [(zgrEv_isHom_neg D hfin X hp m).1 hm, map_zero, LinearMap.zero_apply]
      exact GExt.ZGr.isHom_zero _ _
    rcases lt_or_ge q 0 with hq | hq
    · rw [(galgA0_isHom_neg D hfin hq a).1 ha, map_zero]
      exact GExt.ZGr.isHom_zero _ _
    obtain ⟨p', rfl⟩ := Int.eq_ofNat_of_zero_le hp
    obtain ⟨q', rfl⟩ := Int.eq_ofNat_of_zero_le hq
    rw [zgrEv_isHom] at hm
    rw [galgA0_isHom] at ha
    rw [show (p' : ℤ) + q' = ((q' + p' : ℕ) : ℤ) by push_cast; ring, zgrEv_isHom]
    intro y
    change (a.unop • m) y ∈ _
    rw [Rep.smul_apply]
    exact Submodule.sum_mem _ fun z _ ↦ comp_mem_degreePart' c (ha y z) (hm z)

/-! ### Graded maps between evaluated modules -/

omit [Fintype V] [DecidableEq V] in
theorem degreePart_zero_ne {x y : V} (hxy : x ≠ y) {f : obj c x ⟶ obj c y}
    (hf : f ∈ degreePart c 0 x y) : f = 0 := by
  obtain ⟨F, hF, rfl⟩ := hf
  rw [LinearPaths.degreePart_zero_of_ne hxy hF, map_zero]

include hfin in
theorem degProj_comp_left {p r : ℕ} {y x z : V} {g : obj c y ⟶ obj c x}
    (hg : g ∈ degreePart c p y x) (f : obj c x ⟶ obj c z) :
    degProj c (p + r) y z (g ≫ f) = g ≫ degProj c r x z f := by
  classical
  conv_lhs => rw [eq_sum_degProj c (Nb_spec hfin) f, Preadditive.comp_sum, map_sum]
  rw [Finset.sum_eq_single r]
  · rw [degProj_of_mem c (comp_mem_degreePart' c hg (degProj_mem c r f)), if_pos rfl]
  · intro e _ he
    rw [degProj_of_mem c (comp_mem_degreePart' c hg (degProj_mem c e f)), if_neg (by omega)]
  · intro hr
    have := degProj_mem c r f
    rw [Nb_spec hfin r x z (by simpa using hr), Submodule.mem_bot] at this
    rw [this, Limits.comp_zero, map_zero]

/-- The degree-`r` component of an evaluated morphism. -/
theorem comp_repMap_nat (X Y : V) (r : ℕ) (f : obj c X ⟶ obj c Y) :
    (zgrEv D hfin X).comp (zgrEv D hfin Y) r
        ((repMap (F := D.F0) f).restrictScalars k) =
      (repMap (F := D.F0) (degProj c r X Y f)).restrictScalars k := by
  refine (zgrEv D hfin X).ext_of_hom fun p m hm ↦ ?_
  rw [GExt.ZGr.comp_hom _ _ _ hm]
  rcases lt_or_ge p 0 with hp | hp
  · rw [(zgrEv_isHom_neg D hfin X hp m).1 hm]; simp
  obtain ⟨p', rfl⟩ := Int.eq_ofNat_of_zero_le hp
  rw [zgrEv_isHom] at hm
  change (zgrEv D hfin Y).proj ((p' + r : ℕ) : ℤ) _ = _
  simp only [zgrEv, Nat.cast_nonneg, if_true, Int.toNat_natCast]
  funext y
  simp only [repProj_apply, LinearMap.coe_restrictScalars, repMap_apply]
  exact degProj_comp_left hfin (hm y) f

theorem comp_repMap_neg (X Y : V) {r : ℤ} (hr : r < 0) (f : obj c X ⟶ obj c Y) :
    (zgrEv D hfin X).comp (zgrEv D hfin Y) r
        ((repMap (F := D.F0) f).restrictScalars k) = 0 := by
  refine (zgrEv D hfin X).ext_of_hom fun p m hm ↦ ?_
  rw [GExt.ZGr.comp_hom _ _ _ hm, LinearMap.zero_apply]
  rcases lt_or_ge p 0 with hp | hp
  · rw [(zgrEv_isHom_neg D hfin X hp m).1 hm]; simp
  obtain ⟨p', rfl⟩ := Int.eq_ofNat_of_zero_le hp
  rw [zgrEv_isHom] at hm
  rcases lt_or_ge ((p' : ℤ) + r) 0 with hpr | hpr
  · simp [zgrEv, if_neg (show ¬ 0 ≤ (p' : ℤ) + r by omega)]
  · simp only [zgrEv, if_pos hpr]
    funext y
    simp only [repProj_apply, LinearMap.coe_restrictScalars, repMap_apply]
    conv_lhs => rw [eq_sum_degProj c (Nb_spec hfin) f, Preadditive.comp_sum, map_sum]
    refine Finset.sum_eq_zero fun e _ ↦ ?_
    rw [degProj_of_mem c (comp_mem_degreePart' c (hm y) (degProj_mem c e f)), if_neg (by omega)]

variable [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

/-- An `A₀`-linear map between evaluated modules, as an `Alg F₀`-linear map. -/
def toAlgLin {X Y : V}
    (u : Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c Y))
    (hu : ∀ m a, u (evAct D X m a) = evAct D Y (u m) a) :
    Rep D.F0 (meshFam Q c X) →ₗ[Alg D.F0] Rep D.F0 (meshFam Q c Y) where
  toFun := u
  map_add' := u.map_add
  map_smul' a m := hu m (MulOpposite.op a)

include hfd in
theorem exists_repMap {X Y : V}
    (u : Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c Y))
    (hu : ∀ m a, u (evAct D X m a) = evAct D Y (u m) a) :
    ∃ f : obj c X ⟶ obj c Y, u = (repMap (F := D.F0) f).restrictScalars k := by
  obtain ⟨f, hf⟩ := D.hom_eq_repMap X Y (toAlgLin D u hu)
  exact ⟨f, LinearMap.ext hf⟩

include hfd in
/-- **`Hom_{A₀}(M_X, M_Y)_r = 0` for `r < 0`** (`eq:normalized-hom-degrees`). -/
theorem hom_comp_neg {X Y : V}
    (u : Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c Y))
    (hu : ∀ m a, u (evAct D X m a) = evAct D Y (u m) a) {r : ℤ} (hr : r < 0) :
    (zgrEv D hfin X).comp (zgrEv D hfin Y) r u = 0 := by
  obtain ⟨f, rfl⟩ := exists_repMap D u hu
  exact comp_repMap_neg D hfin X Y hr f

include hfd in
/-- **`Hom_{A₀}(M_X, M_Y)_0 = 0` for `X ≠ Y`.** -/
theorem hom_comp_zero_ne {X Y : V} (hXY : X ≠ Y)
    (u : Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c Y))
    (hu : ∀ m a, u (evAct D X m a) = evAct D Y (u m) a) :
    (zgrEv D hfin X).comp (zgrEv D hfin Y) 0 u = 0 := by
  obtain ⟨f, rfl⟩ := exists_repMap D u hu
  have := comp_repMap_nat D hfin X Y 0 f
  rw [Nat.cast_zero] at this
  rw [this, degreePart_zero_ne hXY (degProj_mem c 0 f)]
  ext m y
  simp

include hfd in
/-- **`Hom_{A₀}(M_X, M_X)_0 = k`.** -/
theorem hom_comp_zero_self {X : V}
    (u : Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c X))
    (hu : ∀ m a, u (evAct D X m a) = evAct D X (u m) a) :
    ∃ t : k, (zgrEv D hfin X).comp (zgrEv D hfin X) 0 u = t • LinearMap.id := by
  obtain ⟨f, rfl⟩ := exists_repMap D u hu
  have := comp_repMap_nat D hfin X X 0 f
  rw [Nat.cast_zero] at this
  obtain ⟨t, ht⟩ := degreePart_zero_eq c (degProj_mem c 0 f)
  refine ⟨t, ?_⟩
  rw [this, ht]
  ext m y
  simp

end MeshWalk

end MultiplicativeBasisDeformations
