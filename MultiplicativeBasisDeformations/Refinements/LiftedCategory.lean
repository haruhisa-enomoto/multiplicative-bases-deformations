module

public import MultiplicativeBasisDeformations.Refinements.LiftedMesh
public import MultiplicativeBasisDeformations.Foundations.A0RepFinite

/-!
# The category of lifted modules (toward Corollary 12.1)

The filtered lifts `M_X^B` of the evaluated modules as right `B`-modules (`FB`), with
`B`-linear maps identified with filtered maps of the underlying graded spaces (`toLin`,
`ofLin`). The maps of filtration order at least one form the radical of a local family
(Proposition 6.5(3): "the map-degree filtration has nilpotent positive part, and its degree-zero
part is a product of copies of `k`").
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt PosFiltration

attribute [local instance] Classical.decEq

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  {hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  {B : Type u} [Ring B] [Algebra k B] {P : PosFiltration (lenA0 D hfin) B}
  (Ls : Lifts D hfin P)

/-- The underlying space of the lifted module `M_X^B`. -/
def LMod (_Ls : Lifts D hfin P) (X : V) : Type u := Rep D.F0 (meshFam Q c X)

instance (X : V) : AddCommGroup (LMod Ls X) :=
  inferInstanceAs (AddCommGroup (Rep D.F0 (meshFam Q c X)))

instance (X : V) : Module Bᵐᵒᵖ (LMod Ls X) where
  smul b m := (Ls.L X).act (show Rep D.F0 (meshFam Q c X) from m) b.unop
  one_smul m := (Ls.L X).one m
  mul_smul b b' m := ((Ls.L X).mul (show Rep D.F0 (meshFam Q c X) from m) b'.unop b.unop).symm
  smul_zero b := LinearMap.congr_fun ((Ls.L X).act.map_zero) b.unop
  smul_add b m m' := LinearMap.congr_fun ((Ls.L X).act.map_add
    (show Rep D.F0 (meshFam Q c X) from m) m') b.unop
  add_smul b b' m := ((Ls.L X).act (show Rep D.F0 (meshFam Q c X) from m)).map_add b.unop b'.unop
  zero_smul m := ((Ls.L X).act (show Rep D.F0 (meshFam Q c X) from m)).map_zero

/-- **The lifted module `M_X^B`** as a right `B`-module. -/
def FB (X : V) : RightModuleCat B := ModuleCat.of Bᵐᵒᵖ (LMod Ls X)

theorem smul_act (X : V) (t : k) (m : Rep D.F0 (meshFam Q c X)) :
    t • m = (Ls.L X).act m (algebraMap k B t) := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, (Ls.L X).one]

variable {Ls}

/-- A `B`-linear map of lifts, as a `k`-linear map of the graded spaces. -/
def toLin {X Y : V} (f : FB Ls X ⟶ FB Ls Y) :
    Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c Y) where
  toFun m := f.hom m
  map_add' m m' := f.hom.map_add m m'
  map_smul' t m := (congrArg (fun z ↦ f.hom z) (smul_act Ls X t m)).trans
    ((f.hom.map_smul (MulOpposite.op (algebraMap k B t)) m).trans
      (smul_act Ls Y t (f.hom m)).symm)

theorem toLin_act {X Y : V} (f : FB Ls X ⟶ FB Ls Y) (m : Rep D.F0 (meshFam Q c X)) (b : B) :
    toLin f ((Ls.L X).act m b) = (Ls.L Y).act (toLin f m) b :=
  f.hom.map_smul (MulOpposite.op b) m

variable (Ls)

/-- A `B`-linear `k`-linear map of the graded spaces, as a map of lifts. -/
def ofLin {X Y : V} (g : Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c Y))
    (hg : ∀ m b, g ((Ls.L X).act m b) = (Ls.L Y).act (g m) b) : FB Ls X ⟶ FB Ls Y :=
  ModuleCat.ofHom
    { toFun := fun m ↦ g m
      map_add' := fun m m' ↦ g.map_add m m'
      map_smul' := fun b m ↦ hg m b.unop }

variable {Ls}

@[simp] theorem toLin_ofLin {X Y : V} (g : Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c Y))
    (hg) : toLin (ofLin Ls g hg) = g := rfl

theorem toLin_injective {X Y : V} : Function.Injective (toLin (Ls := Ls) (X := X) (Y := Y)) := by
  intro f f' h
  ext m
  exact LinearMap.congr_fun h m

@[simp] theorem ofLin_toLin {X Y : V} (f : FB Ls X ⟶ FB Ls Y) :
    ofLin Ls (toLin f) (toLin_act f) = f := toLin_injective rfl

@[simp] theorem toLin_comp {X Y Z : V} (f : FB Ls X ⟶ FB Ls Y) (g : FB Ls Y ⟶ FB Ls Z) :
    toLin (f ≫ g) = toLin g ∘ₗ toLin f := rfl

@[simp] theorem toLin_id (X : V) : toLin (𝟙 (FB Ls X)) = LinearMap.id := rfl

@[simp] theorem toLin_add {X Y : V} (f f' : FB Ls X ⟶ FB Ls Y) :
    toLin (f + f') = toLin f + toLin f' := rfl

@[simp] theorem toLin_zero {X Y : V} : toLin (0 : FB Ls X ⟶ FB Ls Y) = 0 := rfl

@[simp] theorem toLin_neg {X Y : V} (f : FB Ls X ⟶ FB Ls Y) : toLin (-f) = -toLin f := rfl

@[simp] theorem toLin_sub {X Y : V} (f f' : FB Ls X ⟶ FB Ls Y) :
    toLin (f - f') = toLin f - toLin f' := rfl

@[simp] theorem toLin_smul {X Y : V} (t : k) (f : FB Ls X ⟶ FB Ls Y) :
    toLin (t • f) = t • toLin f := by
  refine LinearMap.ext fun m ↦ ?_
  exact (smul_act Ls Y t (toLin f m)).symm

theorem toLin_sum {X Y : V} {ι : Type*} (s : Finset ι) (f : ι → (FB Ls X ⟶ FB Ls Y)) :
    toLin (∑ i ∈ s, f i) = ∑ i ∈ s, toLin (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, toLin_add, ih]

/-- `toLin` as a `k`-linear map. -/
def toLinL (X Y : V) :
    (FB Ls X ⟶ FB Ls Y) →ₗ[k] (Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c Y)) where
  toFun := toLin
  map_add' := toLin_add
  map_smul' := toLin_smul

instance finiteDimensional_FB (X Y : V) : FiniteDimensional k (FB Ls X ⟶ FB Ls Y) :=
  FiniteDimensional.of_injective (toLinL X Y) toLin_injective

/-! ### The radical of the lifted category -/

variable (Ls) (Vx : LenGrading.Vertices (lenA0 D hfin))

include hfd in
/-- `Hom_{A₀}(M_X, M_Y)_r = 0` for `r < 0`, in the form used by Proposition 6.5(3). -/
theorem hneg (X Y : V) : ∀ r : ℤ, r < 0 → ∀ f : Rep D.F0 (meshFam Q c X) →ₗ[k]
    Rep D.F0 (meshFam Q c Y), (∀ m a, f ((gmodEv D hfin X).act m a) =
      (gmodEv D hfin Y).act (f m) a) →
    (∀ p m, (gmodEv D hfin X).gr.IsHom p m → (gmodEv D hfin Y).gr.IsHom (p + r) (f m)) → f = 0 := by
  intro r hr f hf hdeg
  rw [← ZGr.comp_eq_self_of_hom _ _ hdeg]
  exact hom_comp_neg D hfin f hf hr

variable {Ls}

include Vx in
theorem order0 {X Y : V} (f : FB Ls X ⟶ FB Ls Y) :
    OrderGe (gmodEv D hfin X) (gmodEv D hfin Y) 0 (toLin f) :=
  fLift_orderGe_zero Vx (Ls.L X) (Ls.L Y) (hneg X Y) (toLin f) (toLin_act f)

include Vx in
/-- The leading term of a map of lifts is a morphism of `C` of degree zero. -/
theorem exists_lead0 {X Y : V} (f : FB Ls X ⟶ FB Ls Y) :
    ∃ φ : obj c X ⟶ obj c Y, φ ∈ degreePart c 0 X Y ∧
      ZGr.comp (gmodEv D hfin X).gr (gmodEv D hfin Y).gr 0 (toLin f) = rs D φ := by
  have hℓ : ∀ m a, ZGr.comp (gmodEv D hfin X).gr (gmodEv D hfin Y).gr 0 (toLin f)
      (evAct D X m a) = evAct D Y (ZGr.comp (gmodEv D hfin X).gr (gmodEv D hfin Y).gr 0
        (toLin f) m) a :=
    fun m a ↦ fLift_leading Vx (Ls.L X) (Ls.L Y) (toLin f) (toLin_act f) (order0 Vx f) m a
  obtain ⟨φ, hφ⟩ := exists_repMap D _ hℓ
  refine ⟨φ, mem_degreePart_of_repMap D hfin fun p m hm ↦ ?_, hφ⟩
  rw [← hφ]
  exact ZGr.comp_isHom _ _ (toLin f) hm

theorem rs_id (X : V) : rs D (𝟙 (obj c X)) = LinearMap.id := by
  ext m y; simp

theorem comp_id0 (X : V) :
    ZGr.comp (gmodEv D hfin X).gr (gmodEv D hfin X).gr 0 LinearMap.id = LinearMap.id :=
  ZGr.comp_eq_self_of_hom _ _ fun p m hm ↦ by simpa using hm

variable (Ls)

/-- **The radical of the lifted category**: maps of filtration order at least one. -/
def radB (X Y : V) : Submodule k (FB Ls X ⟶ FB Ls Y) where
  carrier := {f | OrderGe (gmodEv D hfin X) (gmodEv D hfin Y) 1 (toLin f)}
  add_mem' {f g} hf hg := by
    change OrderGe _ _ 1 (toLin (f + g)); rw [toLin_add]; exact hf.add hg
  zero_mem' := by change OrderGe _ _ 1 (toLin 0); rw [toLin_zero]; exact OrderGe.zero 1
  smul_mem' t f hf := by
    change OrderGe _ _ 1 (toLin (t • f)); rw [toLin_smul]; exact hf.smul t

theorem toLin_pow {X : V} (f : End (FB Ls X)) (n : ℕ) :
    toLin (f ^ n) = (toLin f) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    change toLin (f ≫ f ^ n) = _
    rw [toLin_comp, ih]
    rfl

include hfd in
theorem nontrivial_rep (x : V) : Nontrivial (Rep D.F0 (meshFam Q c x)) := by
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have hloc := CatAlg.MeshData.evObj_isLocalRing (D := D) x
  obtain ⟨a, b, hab⟩ := exists_pair_ne (End (CatAlg.MeshData.evObj (D := D) x))
  exact hab (ModuleCat.hom_ext (LinearMap.ext fun m ↦
    @Subsingleton.elim (Rep D.F0 (meshFam Q c x)) hnt _ _))

include Vx in
theorem prod_order (l : List (Alg (FB Ls))) (hl : ∀ a ∈ l, ∀ y z, a y z ∈ radB Ls y z) (y z : V) :
    OrderGe (gmodEv D hfin y) (gmodEv D hfin z) l.length (toLin (l.prod y z)) := by
  induction l generalizing y z with
  | nil =>
    change OrderGe _ _ ((0 : ℕ) : ℤ) (toLin (idTo (F := FB Ls) y z))
    by_cases h : y = z
    · subst h
      rw [idTo_self, toLin_id]
      intro p m hm e he
      rw [LinearMap.id_apply, (gmodEv D hfin y).gr.proj_of_isHom hm, if_neg (by omega)]
    · rw [idTo_ne h, toLin_zero]; exact OrderGe.zero _
  | cons a l ih =>
    rw [List.prod_cons, CatAlg.mul_apply, toLin_sum, List.length_cons]
    refine Finset.sum_induction _ (OrderGe (gmodEv D hfin y) (gmodEv D hfin z) _)
      (fun u v hu hv ↦ hu.add hv) (OrderGe.zero _) fun t _ ↦ ?_
    rw [toLin_comp]
    have := (hl a List.mem_cons_self y t).comp (ih (fun b hb ↦ hl b (List.mem_cons_of_mem _ hb)) t z)
    rwa [show (1 : ℤ) + l.length = ((l.length + 1 : ℕ) : ℤ) by push_cast; ring] at this

include Vx in
/-- **The local family of the lifted modules** (Proposition 6.5(3)). -/
def localB : LocalFamily (k := k) (FB Ls) where
  rad := radB Ls
  comp_left {x y z} f {g} hg := by
    change OrderGe _ _ 1 (toLin (f ≫ g))
    rw [toLin_comp]
    have := (order0 Vx f).comp hg
    rwa [zero_add] at this
  comp_right {x y z} {f} hf g := by
    change OrderGe _ _ 1 (toLin (f ≫ g))
    rw [toLin_comp]
    have := hf.comp (order0 Vx g)
    rwa [add_zero] at this
  mem_of_ne {x y} hxy f := by
    obtain ⟨φ, hφ, hlead⟩ := exists_lead0 Vx f
    have h0 : ZGr.comp (gmodEv D hfin x).gr (gmodEv D hfin y).gr 0 (toLin f) = 0 := by
      rw [hlead, degreePart_zero_ne hxy hφ]
      ext m z; simp
    have := orderGe_succ (order0 Vx f) h0
    rwa [zero_add] at this
  diag x f := by
    obtain ⟨φ, hφ, hlead⟩ := exists_lead0 Vx f
    obtain ⟨t, rfl⟩ := ScalarMeshCategory.degreePart_zero_eq c hφ
    refine ⟨t, ?_⟩
    change OrderGe _ _ 1 (toLin (f - t • 𝟙 (FB Ls x)))
    rw [toLin_sub, toLin_smul, toLin_id]
    have hord : OrderGe (gmodEv D hfin x) (gmodEv D hfin x) 0 (toLin f - t • LinearMap.id) := by
      have hid : OrderGe (gmodEv D hfin x) (gmodEv D hfin x) 0 LinearMap.id := by
        intro p m hm e he
        rw [LinearMap.id_apply, (gmodEv D hfin x).gr.proj_of_isHom hm, if_neg (by omega)]
      have := (order0 Vx f).add (hid.smul (-t))
      rwa [neg_smul, ← sub_eq_add_neg] at this
    have h0 : ZGr.comp (gmodEv D hfin x).gr (gmodEv D hfin x).gr 0 (toLin f - t • LinearMap.id) =
        0 := by
      rw [comp_sub, comp_smul, hlead, comp_id0, rs_smul, rs_id, sub_self]
    have := orderGe_succ hord h0
    rwa [zero_add] at this
  id_not_mem x h := by
    change OrderGe _ _ 1 (toLin (𝟙 (FB Ls x))) at h
    rw [toLin_id] at h
    have hz : ∀ m : Rep D.F0 (meshFam Q c x), m = 0 := by
      intro m
      rw [(gmodEv D hfin x).gr.sum m]
      refine Finset.sum_eq_zero fun p _ ↦ ?_
      have := h p _ ((gmodEv D hfin x).gr.isHom_proj p m) p (by omega)
      rwa [LinearMap.id_apply, (gmodEv D hfin x).gr.proj_proj, if_pos rfl] at this
    have := nontrivial_rep (D := D) x
    obtain ⟨m, hm⟩ := exists_ne (0 : Rep D.F0 (meshFam Q c x))
    exact hm (hz m)
  nilpotent x f hf := by
    refine ⟨2 * degBound (gmodEv D hfin x).gr + 1, toLin_injective ?_⟩
    rw [toLin_pow, toLin_zero]
    have hr : RaisesBy (gmodEv D hfin x) 1 (toLin f) := hf
    exact (hr.pow _).eq_zero (by push_cast; omega)
  idealNilp := by
    refine ⟨2 * ∑ y : V, degBound (gmodEv D hfin y).gr + 1, fun l hl hrad ↦ ?_⟩
    refine CatAlg.ext fun y z ↦ ?_
    apply toLin_injective
    rw [CatAlg.zero_apply, toLin_zero]
    refine orderGe_eq_zero_of_large ((prod_order Ls Vx l hrad y z).mono (le_refl _)) ?_
    have hy := Finset.single_le_sum (f := fun y : V ↦ degBound (gmodEv D hfin y).gr)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ y)
    have hz := Finset.single_le_sum (f := fun y : V ↦ degBound (gmodEv D hfin y).gr)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ z)
    by_cases hyz : y = z
    · subst hyz; push_cast; omega
    · push_cast; omega

end MeshWalk

end MultiplicativeBasisDeformations
