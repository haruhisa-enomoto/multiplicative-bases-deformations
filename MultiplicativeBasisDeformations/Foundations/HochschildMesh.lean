module

public import MultiplicativeBasisDeformations.Foundations.ExtHigher
public import MultiplicativeBasisDeformations.Foundations.SquareZero
public import MultiplicativeBasisDeformations.Foundations.RowRotation

/-!
# Hochschild classes and mesh corrections (Proposition 7.6, the map `Ψ`)

`weights-and-parameters.tex` (`prop:hochschild-mesh-restriction`): "Represent
a homogeneous class by a normalized relative cocycle `μ`. Apply Lemma 6.6 with
`R = k`, `Λ = A₀` and the normalized modules, using Lemma 6.3. Choose the actual
projectives at their labels, give `ε` degree `−q`, and lift the arrows
homogeneously to the Hom category of the lifted modules. Each mesh error reduces
to zero, so by the freeness in Lemma 6.6 it is `ε` times a map of the original
category. Thus the mesh errors are `εz_v` with `z_v ∈ C_{q+2}(τv, v)`. Changing the
arrow lifts by `εf_a` changes their tuple by `D_{q+1}f`."

Here: the arrow maps `fA` on evaluated modules, the choice data `LiftData`
(module lifts and arrow lifts), the mesh error `zE`, its representative
`zhat ∈ C_{q+2}(τx, x)`, and the class `Ψ ∈ coker D_{q+1}`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

/-- **The mesh relation holds in `C`.** -/
theorem mesh_zero (x : Q.nonprojective) :
    ∑ a : Σ y : V, y ⟶ x.1, ((c x a.1 a.2 : kˣ) : k) •
      (arrowMor c (Q.mate x a.1 a.2) ≫ arrowMor c a.2) = 0 := by
  have h : (RelationCategory.functor k (meshRelations c)).map (meshRelation c x) = 0 := by
    rw [RelationCategory.functor_map_eq_zero_iff]
    exact CategoricalIdeal.HomIdeal.relation_mem_linearSpan _ ⟨x, rfl, rfl, by simp⟩
  rw [← h, meshRelation, Functor.map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Functor.map_smul]
  congr 1
  rw [← pathMor_toPath, ← pathMor_toPath, ← pathMor_comp]
  rfl

/-! ### Arrow maps and lift data -/

/-- The arrow map `M_y → M_x` of evaluated modules. -/
def fA {y x : V} (a : y ⟶ x) : Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x) :=
  (repMap (F := D.F0) (arrowMor c a)).restrictScalars k

theorem fA_act {y x : V} (a : y ⟶ x) (m : Rep D.F0 (meshFam Q c y)) (b : (Alg D.F0)ᵐᵒᵖ) :
    fA D a (evAct D y m b) = evAct D x (fA D a m) b :=
  (repMap (F := D.F0) (arrowMor c a)).map_smul b.unop m

theorem arrowMor_mem_degreePart {y x : V} (a : y ⟶ x) : arrowMor c a ∈ degreePart c 1 y x :=
  ⟨_, LinearPaths.arrow_mem_degreePart a, rfl⟩

theorem fA_deg {y x : V} (a : y ⟶ x) {p : ℤ} {m : Rep D.F0 (meshFam Q c y)}
    (hm : (zgrEv D hfin y).IsHom p m) : (zgrEv D hfin x).IsHom (p + 1) (fA D a m) := by
  have := repMap_isHom (D := D) hfin (arrowMor_mem_degreePart (c := c) a) hm
  simpa [fA] using this

variable (q : ℕ) (μ : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ)

/-- **Choices for `Ψ`**: lifted actions on all evaluated modules and lifts of the
arrow maps, homogeneous of degree `1 + q`. -/
structure LiftData where
  L : ∀ X : V, ActLift μ (q : ℤ) (gmodEv D hfin X)
  g : ∀ {y x : V}, (y ⟶ x) → (Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x))
  lift : ∀ {y x : V} (a : y ⟶ x), IsLiftHom (L y) (L x) (fA D a) (g a)
  deg : ∀ {y x : V} (a : y ⟶ x) (p : ℤ) (m : Rep D.F0 (meshFam Q c y)),
    (zgrEv D hfin y).IsHom p m → (zgrEv D hfin x).IsHom (p + (1 + (q : ℤ))) (g a m)

variable {D hfin q μ}

theorem isLiftHom_zero {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {MM : GMod (galgA0 D hfin) M} {NN : GMod (galgA0 D hfin) N} {L₁ : ActLift μ (q : ℤ) MM}
    {L₂ : ActLift μ (q : ℤ) NN} : IsLiftHom L₁ L₂ 0 0 :=
  ⟨fun _ _ ↦ by simp, fun _ _ ↦ by simp⟩

theorem IsLiftHom.sum {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {MM : GMod (galgA0 D hfin) M} {NN : GMod (galgA0 D hfin) N} {L₁ : ActLift μ (q : ℤ) MM}
    {L₂ : ActLift μ (q : ℤ) NN} {ι : Type*} (s : Finset ι) {f g : ι → M →ₗ[k] N}
    (h : ∀ i ∈ s, IsLiftHom L₁ L₂ (f i) (g i)) :
    IsLiftHom L₁ L₂ (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isLiftHom_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- **The mesh error** `Σ_a c_{x,a} (f_a g_{σa} + g_a f_{σa})` at a row. -/
def zE (Ld : LiftData D hfin q μ) (x : Q.nonprojective) :
    Rep D.F0 (meshFam Q c (Q.tau x).1) →ₗ[k] Rep D.F0 (meshFam Q c x.1) :=
  ∑ a : Σ y : V, y ⟶ x.1, ((c x a.1 a.2 : kˣ) : k) •
    (fA D a.2 ∘ₗ Ld.g (Q.mate x a.1 a.2) + Ld.g a.2 ∘ₗ fA D (Q.mate x a.1 a.2))

theorem mesh_fA (x : Q.nonprojective) :
    ∑ a : Σ y : V, y ⟶ x.1, ((c x a.1 a.2 : kˣ) : k) •
      (fA D a.2 ∘ₗ fA D (Q.mate x a.1 a.2)) = 0 := by
  ext m z
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.zero_apply]
  rw [Rep.sum_apply]
  simp only [Rep.smul_apply', fA, LinearMap.coe_restrictScalars, repMap_apply]
  rw [show (0 : Rep D.F0 (meshFam Q c x.1)) z = 0 from rfl]
  have := congrArg (fun f ↦ m z ≫ f) (mesh_zero (c := c) x)
  simp only [Preadditive.comp_sum, Linear.comp_smul, Limits.comp_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Category.assoc]

theorem zE_lift (Ld : LiftData D hfin q μ) (x : Q.nonprojective) :
    IsLiftHom (Ld.L (Q.tau x).1) (Ld.L x.1) 0 (zE Ld x) := by
  have h := IsLiftHom.sum (Finset.univ : Finset (Σ y : V, y ⟶ x.1))
    (fun a _ ↦ ((Ld.lift a.2).comp (Ld.lift (Q.mate x a.1 a.2))).smul ((c x a.1 a.2 : kˣ) : k))
  rw [mesh_fA] at h
  exact h

theorem zE_act (Ld : LiftData D hfin q μ) (x : Q.nonprojective)
    (m : Rep D.F0 (meshFam Q c (Q.tau x).1)) (b : (Alg D.F0)ᵐᵒᵖ) :
    zE Ld x (evAct D _ m b) = evAct D _ (zE Ld x m) b :=
  (isLiftHom_zero_iff _ _ _).1 (zE_lift Ld x) m b

/-! ### The representative `zhat` and the class `Ψ` -/

variable (D hfin) in
/-- A homogeneous `A₀`-map between evaluated modules comes from `C` in that degree. -/
theorem mem_degreePart_of_repMap {X Y : V} {f : obj c X ⟶ obj c Y} {r : ℕ}
    (h : ∀ p m, (zgrEv D hfin X).IsHom p m →
      (zgrEv D hfin Y).IsHom (p + r) ((repMap (F := D.F0) f).restrictScalars k m)) :
    f ∈ degreePart c r X Y := by
  have h1 := comp_repMap_nat D hfin X Y r f
  rw [ZGr.comp_eq_self_of_hom (zgrEv D hfin X) (zgrEv D hfin Y) h] at h1
  have : f - degProj c r X Y f = 0 := D.repMap_eq_zero X Y _ fun m ↦ by
    have := LinearMap.congr_fun h1 m
    simp only [LinearMap.coe_restrictScalars] at this
    rw [show repMap (F := D.F0) (f - degProj c r X Y f) m =
      repMap (F := D.F0) f m - repMap (F := D.F0) (degProj c r X Y f) m from by
        ext y; simp [Preadditive.comp_sub]]
    rw [this, sub_self]
  rw [sub_eq_zero] at this
  rw [this]
  exact degProj_mem c r f

theorem zE_deg (Ld : LiftData D hfin q μ) (x : Q.nonprojective) (p : ℤ)
    (m : Rep D.F0 (meshFam Q c (Q.tau x).1)) (hm : (zgrEv D hfin _).IsHom p m) :
    (zgrEv D hfin x.1).IsHom (p + ((q + 2 : ℕ) : ℤ)) (zE Ld x m) := by
  simp only [zE, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.comp_apply]
  refine ZGr.isHom_sum _ _ _ fun a _ ↦ ZGr.isHom_smul _ _ (ZGr.isHom_add _ ?_ ?_)
  · have := fA_deg D hfin a.2 (Ld.deg (Q.mate x a.1 a.2) p m hm)
    convert this using 1; push_cast; ring
  · have := Ld.deg a.2 _ _ (fA_deg D hfin (Q.mate x a.1 a.2) hm)
    convert this using 1; push_cast; ring

/-- **The mesh error as a morphism of `C`**: `z_x ∈ C_{q+2}(τx, x)`. -/
def zhat (Ld : LiftData D hfin q μ) (x : Q.nonprojective) : obj c (Q.tau x).1 ⟶ obj c x.1 :=
  Classical.choose (exists_repMap D (zE Ld x) (zE_act Ld x))

theorem zhat_spec (Ld : LiftData D hfin q μ) (x : Q.nonprojective) :
    zE Ld x = (repMap (F := D.F0) (zhat Ld x)).restrictScalars k :=
  Classical.choose_spec (exists_repMap D (zE Ld x) (zE_act Ld x))

theorem zhat_mem (Ld : LiftData D hfin q μ) (x : Q.nonprojective) :
    zhat Ld x ∈ degreePart c (q + 2) (Q.tau x).1 x.1 :=
  mem_degreePart_of_repMap D hfin fun p m hm ↦ by
    rw [← zhat_spec]; exact zE_deg Ld x p m hm

/-- **The class `Ψ` of the mesh errors** in `coker D_{q+1}`. -/
def Ψc (Ld : LiftData D hfin q μ) : Coker c (q + 1) :=
  Submodule.Quotient.mk (fun x ↦ zhat Ld x)

/-! ### Independence of the arrow lifts -/

section RS

variable (D) in
/-- An evaluated morphism as a `k`-linear map. -/
abbrev rs {X Y : V} (f : obj c X ⟶ obj c Y) :
    Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c Y) :=
  (repMap (F := D.F0) f).restrictScalars k

theorem rs_comp {X Y Z : V} (f : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z) :
    rs D g ∘ₗ rs D f = rs D (f ≫ g) := by
  ext m y; simp [Category.assoc]

theorem rs_add {X Y : V} (f f' : obj c X ⟶ obj c Y) : rs D (f + f') = rs D f + rs D f' := by
  ext m y; simp [Preadditive.comp_add]

theorem rs_sub {X Y : V} (f f' : obj c X ⟶ obj c Y) : rs D (f - f') = rs D f - rs D f' := by
  ext m y; simp [Preadditive.comp_sub]

theorem rs_smul {X Y : V} (t : k) (f : obj c X ⟶ obj c Y) : rs D (t • f) = t • rs D f := by
  ext m y; simp [Linear.comp_smul]

theorem rs_sum {X Y : V} {ι : Type*} (s : Finset ι) (f : ι → (obj c X ⟶ obj c Y)) :
    rs D (∑ i ∈ s, f i) = ∑ i ∈ s, rs D (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext m y; simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, rs_add, ih]

theorem rs_inj {X Y : V} {f f' : obj c X ⟶ obj c Y} (h : rs D f = rs D f') : f = f' := by
  have : f - f' = 0 := D.repMap_eq_zero X Y _ fun m ↦ by
    have := LinearMap.congr_fun (show rs D (f - f') = 0 by rw [rs_sub, h, sub_self]) m
    exact this
  exact sub_eq_zero.1 this

end RS

theorem zhat_spec' (Ld : LiftData D hfin q μ) (x : Q.nonprojective) :
    zE Ld x = rs D (zhat Ld x) := zhat_spec Ld x

theorem isLiftHom_sub {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {MM : GMod (galgA0 D hfin) M} {NN : GMod (galgA0 D hfin) N} {L₁ : ActLift μ (q : ℤ) MM}
    {L₂ : ActLift μ (q : ℤ) NN} {f g g' : M →ₗ[k] N} (h : IsLiftHom L₁ L₂ f g)
    (h' : IsLiftHom L₁ L₂ f g') : IsLiftHom L₁ L₂ 0 (g' - g) := by
  have := h'.add (h.smul (-1))
  simpa [sub_eq_add_neg] using this

theorem Ψc_eq_of_L (Ld Ld' : LiftData D hfin q μ) (hL : Ld'.L = Ld.L) : Ψc Ld' = Ψc Ld := by
  classical
  -- the differences of the arrow lifts are evaluated morphisms of degree `q + 1`
  have hdiff : ∀ {y x : V} (a : y ⟶ x), ∃ h : obj c y ⟶ obj c x,
      h ∈ degreePart c (q + 1) y x ∧ Ld'.g a - Ld.g a = rs D h := by
    intro y x a
    have hl : IsLiftHom (Ld.L y) (Ld.L x) (fA D a) (Ld'.g a) := by
      have := Ld'.lift a; rw [hL] at this; exact this
    have h0 := isLiftHom_sub (Ld.lift a) hl
    obtain ⟨h, hh⟩ := exists_repMap D _ ((isLiftHom_zero_iff _ _ _).1 h0)
    refine ⟨h, mem_degreePart_of_repMap D hfin fun p m hm ↦ ?_, hh⟩
    rw [← hh, LinearMap.sub_apply]
    have h1 := Ld'.deg a p m hm
    have h2 := Ld.deg a p m hm
    have e : p + ((q + 1 : ℕ) : ℤ) = p + (1 + (q : ℤ)) := by push_cast; ring
    rw [e, sub_eq_add_neg]
    exact ZGr.isHom_add _ h1 (ZGr.isHom_neg _ h2)
  choose hA hAmem hAeq using fun (a : Σ x y : V, x ⟶ y) ↦ hdiff a.2.2
  let f : ArrowFamily c := fun a ↦ hA a
  have hf : f ∈ familiesDeg c (q + 1) := fun a ↦ hAmem a
  unfold Ψc
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
  refine ⟨f, hf, ?_⟩
  funext x
  rw [meshDerivativeₗ_apply]
  apply rs_inj (D := D)
  rw [Pi.sub_apply, rs_sub, ← zhat_spec', ← zhat_spec']
  simp only [zE, ← Finset.sum_sub_distrib, ← smul_sub, meshDerivative, rs_sum, rs_smul, rs_add]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  congr 1
  have e1 := hAeq ⟨_, _, Q.mate x a.1 a.2⟩
  have e2 := hAeq ⟨_, _, a.2⟩
  simp only at e1 e2
  rw [← rs_comp, ← rs_comp, ← e1, ← e2]
  simp only [fA, LinearMap.comp_sub, LinearMap.sub_comp]
  abel

/-! ### Existence of choices and independence of the module lifts -/

section Choices

variable (J : InjData D) (h1 : DegOne D)

include J h1 in
theorem extVanish_one (X : V) : ExtVanish (gmodEv D hfin X) (gmodEv D hfin X) 1 (q : ℤ) :=
  extVanish_ev D hfin J h1 1 X X q (Or.inr (by push_cast; omega))

include J h1 in
theorem extVanish_zero (X Y : V) (t : ℤ) (ht : -2 < t) :
    ExtVanish (gmodEv D hfin X) (gmodEv D hfin Y) 0 t :=
  extVanish_ev D hfin J h1 0 X Y t (Or.inr (by push_cast; omega))

variable (hμ : IsHCocycle μ) (hμdeg : HDeg (galgA0 D hfin) μ (q : ℤ))

open Classical in
/-- The lifted actions: the regular lifts at projective labels. -/
def stdL (X : V) : ActLift μ (q : ℤ) (gmodEv D hfin X) :=
  if hX : D.proj X then (cycProj D hfin ⟨X, hX⟩).actLift hμdeg hμ
  else Classical.choice (exists_actLift μ hμdeg hμ _ (extVanish_one J h1 X))

include J h1 hμ hμdeg in
/-- **Choices for `Ψ` exist** (Lemma 6.6 with Lemma 6.3). -/
theorem exists_liftData : ∃ Ld : LiftData D hfin q μ,
    ∀ X, Ld.L X = stdL J h1 hμ hμdeg X := by
  choose g hgdeg hg using fun (a : Σ y x : V, y ⟶ x) ↦
    exists_mapLift (r := 1) (stdL J h1 hμ hμdeg a.1) (stdL J h1 hμ hμdeg a.2.1) (fA D a.2.2)
      (fA_act D a.2.2) (fun p m hm ↦ fA_deg D hfin a.2.2 hm)
      (extVanish_zero J h1 _ _ _ (by omega))
  exact ⟨⟨stdL J h1 hμ hμdeg, fun {y x} a ↦ g ⟨y, x, a⟩, fun {y x} a ↦ hg ⟨y, x, a⟩,
    fun {y x} a ↦ hgdeg ⟨y, x, a⟩⟩, fun _ ↦ rfl⟩

include J h1 in
/-- **`Ψ` does not depend on the choices.** -/
theorem Ψc_indep (Ld Ld' : LiftData D hfin q μ) : Ψc Ld' = Ψc Ld := by
  classical
  choose φ hφdeg hφ using fun X ↦ (Ld.L X).exists_iso (Ld'.L X)
    (extVanish_zero J h1 X X q (by omega))
  let g'' : ∀ {y x : V}, (y ⟶ x) → (Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x)) :=
    fun {y x} a ↦ Ld.g a + φ x ∘ₗ fA D a - fA D a ∘ₗ φ y
  have hlift : ∀ {y x : V} (a : y ⟶ x), IsLiftHom (Ld'.L y) (Ld'.L x) (fA D a) (g'' a) := by
    intro y x a
    refine ⟨fA_act D a, fun m b ↦ ?_⟩
    have hg := (Ld.lift a).2 m b
    have hx := hφ x (fA D a m) b
    have hy := hφ y m b
    have hfa : fA D a ((gmodEv D hfin y).act m b) = (gmodEv D hfin x).act (fA D a m) b :=
      fA_act D a m b
    have hfa' : fA D a ((gmodEv D hfin y).act (φ y m) b) =
        (gmodEv D hfin x).act (fA D a (φ y m)) b := fA_act D a _ b
    simp only [g'', LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add,
      map_sub, LinearMap.add_apply, LinearMap.sub_apply, hfa]
    rw [← hfa']
    have hy' := congrArg (fA D a) hy
    rw [map_sub, map_sub] at hy'
    rw [show Ld.g a ((gmodEv D hfin y).act m b) + φ x ((gmodEv D hfin x).act (fA D a m) b) -
        fA D a (φ y ((gmodEv D hfin y).act m b)) -
        ((gmodEv D hfin x).act (Ld.g a m) b + (gmodEv D hfin x).act (φ x (fA D a m)) b -
          fA D a ((gmodEv D hfin y).act (φ y m) b)) =
      (Ld.g a ((gmodEv D hfin y).act m b) - (gmodEv D hfin x).act (Ld.g a m) b) +
      (φ x ((gmodEv D hfin x).act (fA D a m) b) - (gmodEv D hfin x).act (φ x (fA D a m)) b) -
      (fA D a (φ y ((gmodEv D hfin y).act m b)) - fA D a ((gmodEv D hfin y).act (φ y m) b))
      by abel, hg, ← hx, ← hy']
    abel
  let Ld'' : LiftData D hfin q μ :=
    { L := Ld'.L
      g := fun a ↦ g'' a
      lift := fun a ↦ hlift a
      deg := fun {y x} a p m hm ↦ by
        simp only [g'', LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply]
        have h1' := Ld.deg a p m hm
        have h2' := hφdeg x _ _ (fA_deg D hfin a hm)
        have h3' := fA_deg D hfin a (hφdeg y p m hm)
        have e2 : p + 1 + (q : ℤ) = p + (1 + (q : ℤ)) := by ring
        have e3 : p + (q : ℤ) + 1 = p + (1 + (q : ℤ)) := by ring
        rw [e2] at h2'
        rw [e3] at h3'
        rw [sub_eq_add_neg]
        exact ZGr.isHom_add _ (ZGr.isHom_add _ h1' h2') (ZGr.isHom_neg _ h3') }
  rw [← Ψc_eq_of_L Ld' Ld'' rfl]
  unfold Ψc
  congr 1
  funext x
  apply rs_inj (D := D)
  rw [← zhat_spec', ← zhat_spec']
  simp only [zE, Ld'', g'']
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hm0 := mesh_fA (D := D) x
  have key : ∀ a : Σ y : V, y ⟶ x.1,
      ((c x a.1 a.2 : kˣ) : k) • (fA D a.2 ∘ₗ (Ld.g (Q.mate x a.1 a.2) +
          φ a.1 ∘ₗ fA D (Q.mate x a.1 a.2) - fA D (Q.mate x a.1 a.2) ∘ₗ φ (Q.tau x).1) +
        (Ld.g a.2 + φ x.1 ∘ₗ fA D a.2 - fA D a.2 ∘ₗ φ a.1) ∘ₗ fA D (Q.mate x a.1 a.2)) -
      ((c x a.1 a.2 : kˣ) : k) • (fA D a.2 ∘ₗ Ld.g (Q.mate x a.1 a.2) +
        Ld.g a.2 ∘ₗ fA D (Q.mate x a.1 a.2)) =
      φ x.1 ∘ₗ (((c x a.1 a.2 : kˣ) : k) • (fA D a.2 ∘ₗ fA D (Q.mate x a.1 a.2))) -
      (((c x a.1 a.2 : kˣ) : k) • (fA D a.2 ∘ₗ fA D (Q.mate x a.1 a.2))) ∘ₗ φ (Q.tau x).1 := by
    intro a
    simp only [LinearMap.comp_add, LinearMap.comp_sub, LinearMap.add_comp, LinearMap.sub_comp,
      LinearMap.comp_smul, LinearMap.smul_comp, ← smul_sub, LinearMap.comp_assoc]
    congr 1
    abel
  rw [Finset.sum_congr rfl fun a _ ↦ key a, Finset.sum_sub_distrib, ← lcomp_sum, ← lsum_comp, hm0,
    LinearMap.comp_zero, LinearMap.zero_comp, sub_self]

end Choices

/-! ### Linearity of `Ψ` and invariance under coboundaries -/

section Linear

variable {μ' : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ}

/-- The sum of choices for `μ` and `μ'`. -/
def LiftData.add (Ld : LiftData D hfin q μ) (Ld' : LiftData D hfin q μ') :
    LiftData D hfin q (μ + μ') where
  L X := (Ld.L X).add (Ld'.L X)
  g a := Ld.g a + Ld'.g a
  lift a := ⟨fA_act D a, fun m b ↦ by
    simp only [LinearMap.add_apply, ActLift.add_act, map_add]
    rw [show Ld.g a ((gmodEv D hfin _).act m b) + Ld'.g a ((gmodEv D hfin _).act m b) -
        ((gmodEv D hfin _).act (Ld.g a m) b + (gmodEv D hfin _).act (Ld'.g a m) b) =
      (Ld.g a ((gmodEv D hfin _).act m b) - (gmodEv D hfin _).act (Ld.g a m) b) +
        (Ld'.g a ((gmodEv D hfin _).act m b) - (gmodEv D hfin _).act (Ld'.g a m) b) by abel,
      (Ld.lift a).2, (Ld'.lift a).2]
    abel⟩
  deg a p m hm := ZGr.isHom_add _ (Ld.deg a p m hm) (Ld'.deg a p m hm)

/-- A scalar multiple of choices. -/
def LiftData.smul (Ld : LiftData D hfin q μ) (t : k) : LiftData D hfin q (t • μ) where
  L X := (Ld.L X).smul t
  g a := t • Ld.g a
  lift a := ⟨fA_act D a, fun m b ↦ by
    simp only [LinearMap.smul_apply, ActLift.smul_act, map_smul]
    rw [← smul_sub, (Ld.lift a).2, smul_sub]⟩
  deg a p m hm := ZGr.isHom_smul _ t (Ld.deg a p m hm)

theorem Ψc_add (Ld : LiftData D hfin q μ) (Ld' : LiftData D hfin q μ') :
    Ψc (Ld.add Ld') = Ψc Ld + Ψc Ld' := by
  unfold Ψc
  rw [← Submodule.Quotient.mk_add]
  congr 1
  funext x
  apply rs_inj (D := D)
  rw [Pi.add_apply, rs_add, ← zhat_spec', ← zhat_spec', ← zhat_spec']
  simp only [zE, LiftData.add, LinearMap.comp_add, LinearMap.add_comp, ← Finset.sum_add_distrib,
    ← smul_add]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  congr 1
  abel

theorem Ψc_smul (Ld : LiftData D hfin q μ) (t : k) : Ψc (Ld.smul t) = t • Ψc Ld := by
  unfold Ψc
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  funext x
  apply rs_inj (D := D)
  rw [Pi.smul_apply, rs_smul, ← zhat_spec', ← zhat_spec']
  simp only [zE, LiftData.smul, LinearMap.comp_smul, LinearMap.smul_comp, ← smul_add,
    Finset.smul_sum, smul_comm t]

variable (h : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ)
  (hdeg : ∀ p a, (galgA0 D hfin).gr.IsHom p a → (galgA0 D hfin).gr.IsHom (p + (q : ℤ)) (h a))

/-- The transport of choices along a coboundary. -/
def LiftData.cobdry (Ld : LiftData D hfin q μ) : LiftData D hfin q (μ + hcobdry h) where
  L X := (Ld.L X).cobdry h hdeg
  g a := Ld.g a
  lift a := ⟨fA_act D a, fun m b ↦ by
    rw [ActLift.cobdry_act, ActLift.cobdry_act, map_add, (Ld.lift a).2]
    have : fA D a ((gmodEv D hfin _).act m (h b)) = (gmodEv D hfin _).act (fA D a m) (h b) :=
      fA_act D a m (h b)
    rw [this]
    abel⟩
  deg a p m hm := Ld.deg a p m hm

theorem Ψc_cobdry (Ld : LiftData D hfin q μ) : Ψc (Ld.cobdry h hdeg) = Ψc Ld := rfl

end Linear

end MeshWalk

end MultiplicativeBasisDeformations
