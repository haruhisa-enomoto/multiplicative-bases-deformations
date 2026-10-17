import MultiplicativeBasisDeformations.Foundations.HochschildMesh

/-!
# Category cocycles and the map `Ψ` (toward Proposition 12.5)

A Hochschild two-cocycle `φ` of the category `C` of internal degree `q` gives the first-order
deformation of `C`; restricted to the projective corner it is a cocycle `μ` of `A₀`, and its
other restrictions are lifts of the actions on the evaluated modules (`ν(m, a) = φ(a, m)`) and
of the arrow maps (`g_a(m) = φ(m, a)`). The mesh error of these lifts is
`Σ_a c_{x,a} φ(σa, a)` (`Ψc_catLift`): this is how `Ψ` reads off the class of the deformation
(`deformation-refinements.tex:261–275`: "Evaluation of every object at those projectives gives a
free lift of its normalized module").
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace GExt

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ] {GΛ : GAlg (R := R) Λ}
  {M : Type*} [AddCommGroup M] [Module R M] {μ : Λ →ₗ[R] Λ →ₗ[R] Λ}

/-- **A lifted action from a bilinear correction** `m * a = ma + εν(m, a)`. -/
def ActLift.ofBilin {q : ℤ} (MM : GMod GΛ M) (ν₂ : M →ₗ[R] Λ →ₗ[R] M)
    (hdeg : ∀ (p d : ℤ) (m : M) (a : Λ), MM.gr.IsHom p m → GΛ.gr.IsHom d a →
      MM.gr.IsHom (p + d + q) (ν₂ m a))
    (heq : ∀ m a b, ν₂ (MM.act m a) b - ν₂ m (a * b) + MM.act (ν₂ m a) b = MM.act m (μ a b)) :
    ActLift μ q MM where
  ν a := ν₂.flip (a 0)
  good := by
    refine ⟨fun a ↦ ?_, fun a i x y hi ↦ ?_, fun a i c x hi ↦ ?_, fun a ds p m ha hm ↦ ?_⟩
    · simp [Bar.tr]
    · obtain rfl : i = 0 := by omega
      ext m; simp
    · obtain rfl : i = 0 := by omega
      ext m; simp
    · simp only [LinearMap.flip_apply, Finset.sum_range_one]
      exact hdeg p (ds 0) m (a 0) hm (ha 0 (by norm_num))
  eq := by
    funext a
    ext m
    simp only [Bar.d_one_apply, LinearMap.add_apply, LinearMap.sub_apply, homAct_l, homAct_r,
      muCochain_apply, LinearMap.comp_apply, LinearMap.flip_apply]
    simp only [Bar.sh, Bar.ct, Bar.tr, show (0 : ℕ) < 1 from Nat.one_pos, if_true,
      lt_self_iff_false, if_false, zero_add]
    norm_num
    exact heq m (a 0) (a 1)

theorem ActLift.ofBilin_act {q : ℤ} (MM : GMod GΛ M) (ν₂ : M →ₗ[R] Λ →ₗ[R] M) (hdeg) (heq)
    (m : M) (a : Λ) : (ActLift.ofBilin (μ := μ) (q := q) MM ν₂ hdeg heq).act m a = ν₂ m a := by
  simp [ActLift.act, ActLift.ofBilin, single, Bar.cons]

end GExt

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}

variable (c) in
/-- **A Hochschild two-cocycle of the category `C`** of internal degree `q`. -/
structure CatCocycle (q : ℕ) where
  φ : ∀ {X Y Z : V}, (obj c X ⟶ obj c Y) → (obj c Y ⟶ obj c Z) → (obj c X ⟶ obj c Z)
  add_left : ∀ {X Y Z : V} (f f' : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z),
    φ (f + f') g = φ f g + φ f' g
  add_right : ∀ {X Y Z : V} (f : obj c X ⟶ obj c Y) (g g' : obj c Y ⟶ obj c Z),
    φ f (g + g') = φ f g + φ f g'
  smul_left : ∀ {X Y Z : V} (t : k) (f : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z),
    φ (t • f) g = t • φ f g
  smul_right : ∀ {X Y Z : V} (t : k) (f : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z),
    φ f (t • g) = t • φ f g
  cocycle : ∀ {W X Y Z : V} (f : obj c W ⟶ obj c X) (g : obj c X ⟶ obj c Y)
    (h : obj c Y ⟶ obj c Z), f ≫ φ g h - φ (f ≫ g) h + φ f (g ≫ h) - φ f g ≫ h = 0
  deg : ∀ {X Y Z : V} {d e : ℕ} {f : obj c X ⟶ obj c Y} {g : obj c Y ⟶ obj c Z},
    f ∈ degreePart c d X Y → g ∈ degreePart c e Y Z → φ f g ∈ degreePart c (d + e + q) X Z

namespace CatCocycle

variable {q : ℕ} (Φ : CatCocycle c q)

theorem zero_left {X Y Z : V} (g : obj c Y ⟶ obj c Z) : Φ.φ (0 : obj c X ⟶ obj c Y) g = 0 := by
  have := Φ.add_left (0 : obj c X ⟶ obj c Y) 0 g
  rw [add_zero] at this
  simpa using this

theorem zero_right {X Y Z : V} (f : obj c X ⟶ obj c Y) : Φ.φ f (0 : obj c Y ⟶ obj c Z) = 0 := by
  have := Φ.add_right f (0 : obj c Y ⟶ obj c Z) 0
  rw [add_zero] at this
  simpa using this

theorem sum_left {X Y Z : V} {ι : Type*} (s : Finset ι) (f : ι → (obj c X ⟶ obj c Y))
    (g : obj c Y ⟶ obj c Z) : Φ.φ (∑ i ∈ s, f i) g = ∑ i ∈ s, Φ.φ (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Φ.zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Φ.add_left, ih]

theorem sum_right {X Y Z : V} {ι : Type*} (s : Finset ι) (f : obj c X ⟶ obj c Y)
    (g : ι → (obj c Y ⟶ obj c Z)) : Φ.φ f (∑ i ∈ s, g i) = ∑ i ∈ s, Φ.φ f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Φ.zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Φ.add_right, ih]

/-- The cocycle identity, solved for `φ(f, gh)`. -/
theorem cocycle' {W X Y Z : V} (f : obj c W ⟶ obj c X) (g : obj c X ⟶ obj c Y)
    (h : obj c Y ⟶ obj c Z) : φ Φ f (g ≫ h) = φ Φ (f ≫ g) h + φ Φ f g ≫ h - f ≫ φ Φ g h := by
  have := Φ.cocycle f g h
  rw [← sub_eq_zero, ← this]; abel

/-- **The mesh value** `Σ_a c_{x,a} φ(σa, a)` of a category cocycle. -/
def meshVal : MeshFamily c := fun x ↦
  ∑ a : Σ y : V, y ⟶ x.1, ((c x a.1 a.2 : kˣ) : k) •
    Φ.φ (arrowMor c (Q.mate x a.1 a.2)) (arrowMor c a.2)

end CatCocycle

variable {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  {q : ℕ} (Φ : CatCocycle c q)

/-- **The cocycle of `A₀`**: `μ(a, b) = Σ_w φ(b_{yw}, a_{wz})`. -/
def catMu : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ :=
  LinearMap.mk₂ k (fun a b ↦ MulOpposite.op (fun y z ↦ ∑ w, Φ.φ (b.unop y w) (a.unop w z)))
    (fun a a' b ↦ by
      apply MulOpposite.unop_injective; apply CatAlg.ext; intro y z
      change ∑ w, Φ.φ (b.unop y w) ((a + a').unop w z) =
        ∑ w, Φ.φ (b.unop y w) (a.unop w z) + ∑ w, Φ.φ (b.unop y w) (a'.unop w z)
      simp only [MulOpposite.unop_add, CatAlg.add_apply, Φ.add_right, Finset.sum_add_distrib])
    (fun t a b ↦ by
      apply MulOpposite.unop_injective; apply CatAlg.ext; intro y z
      change ∑ w, Φ.φ (b.unop y w) ((t • a).unop w z) = t • ∑ w, Φ.φ (b.unop y w) (a.unop w z)
      simp only [MulOpposite.unop_smul, CatAlg.smul_apply, Φ.smul_right, Finset.smul_sum])
    (fun a b b' ↦ by
      apply MulOpposite.unop_injective; apply CatAlg.ext; intro y z
      change ∑ w, Φ.φ ((b + b').unop y w) (a.unop w z) =
        ∑ w, Φ.φ (b.unop y w) (a.unop w z) + ∑ w, Φ.φ (b'.unop y w) (a.unop w z)
      simp only [MulOpposite.unop_add, CatAlg.add_apply, Φ.add_left, Finset.sum_add_distrib])
    (fun t a b ↦ by
      apply MulOpposite.unop_injective; apply CatAlg.ext; intro y z
      change ∑ w, Φ.φ ((t • b).unop y w) (a.unop w z) = t • ∑ w, Φ.φ (b.unop y w) (a.unop w z)
      simp only [MulOpposite.unop_smul, CatAlg.smul_apply, Φ.smul_left, Finset.smul_sum])

theorem catMu_apply (a b : (Alg D.F0)ᵐᵒᵖ) (y z : D.PV) :
    (catMu D Φ a b).unop y z = ∑ w, Φ.φ (b.unop y w) (a.unop w z) := rfl

theorem catMu_isHCocycle : IsHCocycle (catMu D Φ) := by
  intro a b c'
  apply MulOpposite.unop_injective; apply CatAlg.ext; intro y z
  simp only [MulOpposite.unop_sub, MulOpposite.unop_add, MulOpposite.unop_mul,
    MulOpposite.unop_zero, CatAlg.sub_apply, CatAlg.add_apply, CatAlg.zero_apply, mul_apply,
    catMu_apply, Preadditive.sum_comp, Preadditive.comp_sum, Φ.sum_left, Φ.sum_right]
  have key : ∑ w, ∑ v, (c'.unop y w ≫ Φ.φ (b.unop w v) (a.unop v z) -
      Φ.φ (c'.unop y w ≫ b.unop w v) (a.unop v z) +
      Φ.φ (c'.unop y w) (b.unop w v ≫ a.unop v z) -
      Φ.φ (c'.unop y w) (b.unop w v) ≫ a.unop v z) = 0 := by
    simp [Φ.cocycle]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at key
  rw [Finset.sum_comm (f := fun w v ↦ Φ.φ (c'.unop y w ≫ b.unop w v) (a.unop v z))] at key
  rw [← neg_eq_zero, ← key]
  rw [Finset.sum_comm (f := fun x y_1 ↦ Φ.φ (c'.unop y y_1) (b.unop y_1 x) ≫ a.unop x z)]
  abel

include hfin in
theorem catMu_hDeg : HDeg (galgA0 D hfin) (catMu D Φ) (q : ℤ) := by
  intro p p' a b ha hb
  rcases lt_or_ge p 0 with hp | hp
  · rw [(galgA0_isHom_neg D hfin hp a).1 ha, map_zero, LinearMap.zero_apply]
    exact ZGr.isHom_zero _ _
  rcases lt_or_ge p' 0 with hp' | hp'
  · rw [(galgA0_isHom_neg D hfin hp' b).1 hb, map_zero]
    exact ZGr.isHom_zero _ _
  obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  obtain ⟨e, rfl⟩ := Int.eq_ofNat_of_zero_le hp'
  rw [galgA0_isHom] at ha hb
  rw [show (d : ℤ) + e + q = ((e + d + q : ℕ) : ℤ) by push_cast; ring, galgA0_isHom]
  intro y z
  rw [catMu_apply]
  exact Submodule.sum_mem _ fun w _ ↦ Φ.deg (hb y w) (ha w z)

/-- The correction `ν(m, a)_y = Σ_w φ(a_{yw}, m_w)` of the action on `M_X`. -/
def catNu (X : V) :
    Rep D.F0 (meshFam Q c X) →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] Rep D.F0 (meshFam Q c X) :=
  LinearMap.mk₂ k (fun m a y ↦ ∑ w, Φ.φ (a.unop y w) (m w))
    (fun m m' a ↦ by
      ext y
      change ∑ w, Φ.φ (a.unop y w) ((m + m') w) =
        ∑ w, Φ.φ (a.unop y w) (m w) + ∑ w, Φ.φ (a.unop y w) (m' w)
      simp only [Rep.add_apply, Φ.add_right, Finset.sum_add_distrib])
    (fun t m a ↦ by
      ext y
      change ∑ w, Φ.φ (a.unop y w) ((t • m) w) = t • ∑ w, Φ.φ (a.unop y w) (m w)
      simp only [Rep.smul_apply', Φ.smul_right, Finset.smul_sum])
    (fun m a a' ↦ by
      ext y
      change ∑ w, Φ.φ ((a + a').unop y w) (m w) =
        ∑ w, Φ.φ (a.unop y w) (m w) + ∑ w, Φ.φ (a'.unop y w) (m w)
      simp only [MulOpposite.unop_add, CatAlg.add_apply, Φ.add_left, Finset.sum_add_distrib])
    (fun t m a ↦ by
      ext y
      change ∑ w, Φ.φ ((t • a).unop y w) (m w) = t • ∑ w, Φ.φ (a.unop y w) (m w)
      simp only [MulOpposite.unop_smul, CatAlg.smul_apply, Φ.smul_left, Finset.smul_sum])

theorem catNu_apply (X : V) (m : Rep D.F0 (meshFam Q c X)) (a : (Alg D.F0)ᵐᵒᵖ) (y : D.PV) :
    catNu D Φ X m a y = ∑ w, Φ.φ (a.unop y w) (m w) := rfl

theorem evAct_apply (X : V) (m : Rep D.F0 (meshFam Q c X)) (a : (Alg D.F0)ᵐᵒᵖ) (y : D.PV) :
    evAct D X m a y = ∑ w, a.unop y w ≫ m w := rfl

/-- **The lifted action on `M_X`.** -/
def catL (X : V) : ActLift (catMu D Φ) (q : ℤ) (gmodEv D hfin X) :=
  ActLift.ofBilin (gmodEv D hfin X) (catNu D Φ X)
    (fun p d m a hm ha ↦ by
      rcases lt_or_ge p 0 with hp | hp
      · rw [(zgrEv_isHom_neg D hfin X hp m).1 hm, map_zero, LinearMap.zero_apply]
        exact ZGr.isHom_zero _ _
      rcases lt_or_ge d 0 with hd | hd
      · rw [(galgA0_isHom_neg D hfin hd a).1 ha, map_zero]
        exact ZGr.isHom_zero _ _
      obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hd
      change (zgrEv D hfin X).IsHom _ m at hm
      rw [zgrEv_isHom] at hm
      rw [galgA0_isHom] at ha
      change (zgrEv D hfin X).IsHom _ _
      rw [show (p : ℤ) + d + q = ((d + p + q : ℕ) : ℤ) by push_cast; ring, zgrEv_isHom]
      intro y
      rw [catNu_apply]
      exact Submodule.sum_mem _ fun w _ ↦ Φ.deg (ha y w) (hm w))
    (fun m a b ↦ by
      ext y
      change catNu D Φ X (evAct D X m a) b y - catNu D Φ X m (a * b) y +
        evAct D X (catNu D Φ X m a) b y = evAct D X m (catMu D Φ a b) y
      simp only [catNu_apply, evAct_apply, catMu_apply, MulOpposite.unop_mul, mul_apply,
        Φ.sum_left, Φ.sum_right, Preadditive.sum_comp, Preadditive.comp_sum]
      have key : ∑ w, ∑ v, (b.unop y w ≫ Φ.φ (a.unop w v) (m v) -
          Φ.φ (b.unop y w ≫ a.unop w v) (m v) + Φ.φ (b.unop y w) (a.unop w v ≫ m v) -
          Φ.φ (b.unop y w) (a.unop w v) ≫ m v) = 0 := by
        simp [Φ.cocycle]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at key
      rw [Finset.sum_comm (f := fun w v ↦ Φ.φ (b.unop y w ≫ a.unop w v) (m v))] at key
      rw [Finset.sum_comm (f := fun x y_1 ↦ Φ.φ (b.unop y y_1) (a.unop y_1 x) ≫ m x)]
      rw [← sub_eq_zero, ← key]
      abel)

theorem catL_act (X : V) (m : Rep D.F0 (meshFam Q c X)) (a : (Alg D.F0)ᵐᵒᵖ) :
    (catL D hfin Φ X).act m a = catNu D Φ X m a :=
  ActLift.ofBilin_act _ _ _ _ m a

/-- The lifted arrow map `g_a(m)_y = φ(m_y, a)`. -/
def catG {y x : V} (α : y ⟶ x) :
    Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x) where
  toFun m z := Φ.φ (m z) (arrowMor c α)
  map_add' m m' := by ext z; exact Φ.add_left _ _ _
  map_smul' t m := by ext z; exact Φ.smul_left _ _ _

theorem catG_lift {y x : V} (α : y ⟶ x) :
    IsLiftHom (catL D hfin Φ y) (catL D hfin Φ x) (fA D α) (catG D Φ α) := by
  refine ⟨fA_act D α, fun m b ↦ ?_⟩
  rw [catL_act, catL_act]
  ext z
  change Φ.φ (evAct D y m b z) (arrowMor c α) - evAct D x (catG D Φ α m) b z =
    catNu D Φ x (fA D α m) b z - (catNu D Φ y m b z ≫ arrowMor c α)
  simp only [evAct_apply, catNu_apply, catG, LinearMap.coe_mk, AddHom.coe_mk, Φ.sum_left,
    Preadditive.sum_comp, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  change _ - _ = Φ.φ (b.unop z w) (m w ≫ arrowMor c α) - _
  rw [Φ.cocycle']
  abel

theorem catG_deg {y x : V} (α : y ⟶ x) (p : ℤ) (m : Rep D.F0 (meshFam Q c y))
    (hm : (zgrEv D hfin y).IsHom p m) :
    (zgrEv D hfin x).IsHom (p + (1 + (q : ℤ))) (catG D Φ α m) := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [(zgrEv_isHom_neg D hfin y hp m).1 hm, map_zero]
    exact ZGr.isHom_zero _ _
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  rw [zgrEv_isHom] at hm
  rw [show (p : ℤ) + (1 + q) = ((p + 1 + q : ℕ) : ℤ) by push_cast; ring, zgrEv_isHom]
  intro z
  exact Φ.deg (hm z) (arrowMor_mem_degreePart (c := c) α)

/-- **The lift data of a category cocycle.** -/
def catLift : LiftData D hfin q (catMu D Φ) where
  L := catL D hfin Φ
  g := catG D Φ
  lift := catG_lift D hfin Φ
  deg := catG_deg D hfin Φ

include hfd in
/-- **`Ψ` of the restricted cocycle is the mesh value** `[Σ_a c_{x,a} φ(σa, a)]`. -/
theorem Ψc_catLift : Ψc (catLift D hfin Φ) = Submodule.Quotient.mk Φ.meshVal := by
  unfold Ψc
  congr 1
  funext x
  apply rs_inj (D := D)
  rw [← zhat_spec']
  ext m y
  change (zE (catLift D hfin Φ) x m) y = m y ≫ Φ.meshVal x
  simp only [zE, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.comp_apply]
  rw [Rep.sum_apply]
  simp only [Rep.smul_apply', Rep.add_apply]
  change ∑ a : Σ z : V, z ⟶ x.1, ((c x a.1 a.2 : kˣ) : k) •
      (Φ.φ (m y) (arrowMor c (Q.mate x a.1 a.2)) ≫ arrowMor c a.2 +
        Φ.φ (m y ≫ arrowMor c (Q.mate x a.1 a.2)) (arrowMor c a.2)) = _
  have hmesh : ∑ a : Σ z : V, z ⟶ x.1, ((c x a.1 a.2 : kˣ) : k) •
      Φ.φ (m y) (arrowMor c (Q.mate x a.1 a.2) ≫ arrowMor c a.2) = 0 := by
    simp only [← Φ.smul_right, ← Φ.sum_right]
    rw [mesh_zero (c := c) x, Φ.zero_right]
  rw [← sub_zero (∑ _, _), ← hmesh, ← Finset.sum_sub_distrib, CatCocycle.meshVal,
    Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Linear.comp_smul, ← smul_sub, Φ.cocycle']
  congr 1
  abel

end MeshWalk

end MultiplicativeBasisDeformations
