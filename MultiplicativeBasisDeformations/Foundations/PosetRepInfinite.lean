import MultiplicativeBasisDeformations.Foundations.OrbitDim
import MultiplicativeBasisDeformations.Foundations.RepFinite

/-!
# Lemma 8.8 for incidence algebras of posets with unique paths

`local-ray-geometry.tex` (`lem:dimension-infinity` and the table after it): "For the
relation-free diagrams used below the required vectors are […] These counts depend only on
the underlying graphs; for a tree any orientation is allowed."

Here: a finite poset `P` with a set `E` of arrows (`x < y`) such that between comparable
points there is exactly one `E`-path. Its incidence algebra is the path algebra of `E`, so a
right module of dimension vector `d` is a tuple of matrices on the arrows, and isomorphism
is conjugation by `∏ GL_{d v}` (`isoConj`). If `∑ d_v² ≤ ∑_{x → y} d_x d_y` and `d ≠ 0`, the
incidence algebra is representation-infinite (`not_isRepresentationFinite`): finite
representation type would give finitely many orbits (`exists_labels_iso`), contradicting
`OrbitDim.orbits_not_finite` with `F = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MultiplicativeBasisDeformations

namespace PosetRep

universe u

variable {k : Type u} [Field k] {P : Type} [PartialOrder P] [Fintype P] [DecidableEq P]
  [LocallyFiniteOrder P] [DecidableLE P]

/-! ### Paths along the arrows -/

/-- Paths along the arrows `E`. -/
inductive EPath (E : P → P → Prop) : P → P → Type
  | nil (x : P) : EPath E x x
  | cons {x y z : P} (p : EPath E x y) (h : E y z) : EPath E x z

variable {E : P → P → Prop}

/-- Concatenation. -/
def EPath.comp {x y : P} (p : EPath E x y) : ∀ {z : P}, EPath E y z → EPath E x z
  | _, EPath.nil _ => p
  | _, EPath.cons q h => EPath.cons (p.comp q) h

theorem EPath.le (hE : ∀ x y, E x y → x < y) {x y : P} : EPath E x y → x ≤ y
  | EPath.nil _ => le_rfl
  | EPath.cons p h => (p.le hE).trans (hE _ _ h).le

/-- The vector space at a vertex. -/
abbrev Sp (k : Type u) (d : P → ℕ) (v : P) := Fin (d v) → k

variable (d : P → ℕ)

/-- Transport along a path. -/
def tr (M : ∀ x y, E x y → (Sp k d x →ₗ[k] Sp k d y)) : ∀ {x y : P}, EPath E x y →
    (Sp k d x →ₗ[k] Sp k d y)
  | _, _, EPath.nil _ => LinearMap.id
  | _, _, EPath.cons p h => M _ _ h ∘ₗ tr M p

theorem tr_nil (M : ∀ x y, E x y → (Sp k d x →ₗ[k] Sp k d y)) (x : P) :
    tr d M (EPath.nil x) = LinearMap.id := by
  rw [tr]

theorem tr_cons (M : ∀ x y, E x y → (Sp k d x →ₗ[k] Sp k d y)) {x y z : P} (p : EPath E x y)
    (h : E y z) : tr d M (EPath.cons p h) = M _ _ h ∘ₗ tr d M p := by
  rw [tr]

theorem tr_comp (M : ∀ x y, E x y → (Sp k d x →ₗ[k] Sp k d y)) {x y : P} (p : EPath E x y) :
    ∀ {z : P} (q : EPath E y z), tr d M (p.comp q) = tr d M q ∘ₗ tr d M p
  | _, EPath.nil _ => by rw [tr_nil, LinearMap.id_comp]; rfl
  | _, EPath.cons q h => by
      rw [EPath.comp, tr_cons, tr_cons, tr_comp M p q, LinearMap.comp_assoc]

variable (hE : ∀ x y, E x y → x < y) (huniq : ∀ x y, Subsingleton (EPath E x y))
  (hex : ∀ x y, x ≤ y → Nonempty (EPath E x y))

/-- **The transport between comparable points.** -/
def T (M : ∀ x y, E x y → (Sp k d x →ₗ[k] Sp k d y)) (x y : P) : Sp k d x →ₗ[k] Sp k d y :=
  if h : x ≤ y then tr d M (Classical.choice (hex x y h)) else 0

include hE huniq in
theorem T_path (M : ∀ x y, E x y → (Sp k d x →ₗ[k] Sp k d y)) {x y : P} (p : EPath E x y) :
    T d hex M x y = tr d M p := by
  rw [T, dif_pos (p.le hE), (huniq x y).elim (Classical.choice _) p]

include hE huniq in
theorem T_self (M : ∀ x y, E x y → (Sp k d x →ₗ[k] Sp k d y)) (x : P) :
    T d hex M x x = LinearMap.id :=
  (T_path d hE huniq hex M (EPath.nil x)).trans (tr_nil d M x)

include hE huniq in
theorem T_trans (M : ∀ x y, E x y → (Sp k d x →ₗ[k] Sp k d y)) {x y z : P} (hxy : x ≤ y)
    (hyz : y ≤ z) : T d hex M x z = T d hex M y z ∘ₗ T d hex M x y := by
  obtain ⟨p⟩ := hex x y hxy
  obtain ⟨q⟩ := hex y z hyz
  rw [T_path d hE huniq hex M p, T_path d hE huniq hex M q, T_path d hE huniq hex M (p.comp q),
    tr_comp]

include hE huniq in
theorem T_arrow (M : ∀ x y, E x y → (Sp k d x →ₗ[k] Sp k d y)) {x y : P} (h : E x y) :
    T d hex M x y = M x y h := by
  rw [T_path d hE huniq hex M (EPath.cons (EPath.nil x) h), tr_cons, tr_nil, LinearMap.comp_id]

theorem T_not_le (M : ∀ x y, E x y → (Sp k d x →ₗ[k] Sp k d y)) {x y : P} (h : ¬ x ≤ y) :
    T d hex M x y = 0 := by
  rw [T, dif_neg h]

/-! ### The module of a tuple of matrices -/

section Module

variable (M : ∀ x y, E x y → (Sp k d x →ₗ[k] Sp k d y))

/-- The action of the incidence algebra. -/
def act (a : IncidenceAlgebra k P) (w : ∀ v, Sp k d v) : ∀ v, Sp k d v :=
  fun y ↦ ∑ x : P, a x y • T d hex M x y (w x)

include hE huniq in
theorem act_mul (a b : IncidenceAlgebra k P) (w : ∀ v, Sp k d v) :
    act d hex M (b * a) w = act d hex M a (act d hex M b w) := by
  funext z
  simp only [act, IncidenceAlgebra.mul_apply, map_sum, map_smul, Finset.smul_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have key : ∀ y : P, a y z • b x y • T d hex M y z (T d hex M x y (w x)) =
      if x ≤ y ∧ y ≤ z then (b x y * a y z) • T d hex M x z (w x) else 0 := by
    intro y
    split_ifs with h
    · rw [T_trans d hE huniq hex M h.1 h.2, LinearMap.comp_apply, smul_smul, mul_comm]
    · rw [not_and_or] at h
      rcases h with h | h
      · rw [IncidenceAlgebra.apply_eq_zero_of_not_le h, zero_smul, smul_zero]
      · rw [IncidenceAlgebra.apply_eq_zero_of_not_le h, zero_smul]
  rw [Finset.sum_congr rfl fun y _ ↦ key y, ← Finset.sum_filter, Finset.filter_and]
  rw [← Finset.filter_le_le_eq_Icc]
  congr 1
  ext y; simp

include hE huniq in
theorem act_one (w : ∀ v, Sp k d v) : act d hex M 1 w = w := by
  funext y
  simp only [act, IncidenceAlgebra.one_apply]
  rw [Finset.sum_eq_single y]
  · rw [if_pos rfl, one_smul, T_self d hE huniq hex M]; rfl
  · intro x _ hx; rw [if_neg hx, zero_smul]
  · simp

include hE huniq in
theorem act_algebraMap (c : k) (w : ∀ v, Sp k d v) :
    act d hex M (algebraMap k (IncidenceAlgebra k P) c) w = c • w := by
  funext y
  simp only [act, Pi.smul_apply]
  rw [Finset.sum_eq_single y]
  · change (algebraMap k k c • (1 : IncidenceAlgebra k P)) y y • _ = _
    rw [IncidenceAlgebra.constSMul_apply, IncidenceAlgebra.one_apply, if_pos rfl,
      T_self d hE huniq hex M]
    simp
  · intro x _ hx
    change (algebraMap k k c • (1 : IncidenceAlgebra k P)) x y • _ = _
    rw [IncidenceAlgebra.constSMul_apply, IncidenceAlgebra.one_apply, if_neg hx]
    simp
  · simp

/-- The carrier. -/
abbrev Car (_M : ∀ x y, E x y → (Sp k d x →ₗ[k] Sp k d y)) : Type u := ∀ v, Sp k d v

include hE huniq in
/-- The right module structure. -/
def repModule : Module (IncidenceAlgebra k P)ᵐᵒᵖ (Car d M) where
  smul a w := act d hex M a.unop w
  one_smul w := act_one d hE huniq hex M w
  mul_smul a b w := act_mul d hE huniq hex M a.unop b.unop w
  smul_zero a := by
    change act d hex M a.unop 0 = 0
    funext y; simp [act]
  smul_add a v w := by
    change act d hex M a.unop (v + w) = act d hex M a.unop v + act d hex M a.unop w
    funext y
    simp only [act, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    change _ • T d hex M x y (v x + w x) = _
    rw [map_add, smul_add]
  add_smul a b w := by
    change act d hex M (a + b).unop w = act d hex M a.unop w + act d hex M b.unop w
    funext y; simp [act, add_smul, Finset.sum_add_distrib, IncidenceAlgebra.add_apply]
  zero_smul w := by
    change act d hex M (0 : (IncidenceAlgebra k P)ᵐᵒᵖ).unop w = 0
    funext y; simp [act, IncidenceAlgebra.zero_apply]

/-- **The module of a tuple of matrices.** -/
def repObj : RightModuleCat (IncidenceAlgebra k P) :=
  @ModuleCat.of _ _ (Car d M) _ (repModule d hE huniq hex M)

/-- The identification with `∏ k^{d v}` is `k`-linear. -/
def toPi : repObj d hE huniq hex M →ₗ[k] (∀ v, Sp k d v) where
  toFun w := w
  map_add' _ _ := rfl
  map_smul' c w := act_algebraMap d hE huniq hex M c w

theorem repObj_finite : Module.Finite k (repObj d hE huniq hex M) :=
  Module.Finite.of_injective (toPi d hE huniq hex M) fun _ _ h ↦ h

end Module

/-! ### Isomorphisms are conjugations -/

section Iso

/-- The matrix unit at `x ≤ y`. -/
def sgl (x y : P) (h : x ≤ y) : IncidenceAlgebra k P :=
  ⟨fun a b ↦ if a = x ∧ b = y then 1 else 0, fun a b hab ↦ by
    rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hab h⟩

variable (M : ∀ x y, E x y → (Sp k d x →ₗ[k] Sp k d y))

theorem act_sgl (p q : P) (hpq : p ≤ q) (w : ∀ v, Sp k d v) :
    act d hex M (sgl p q hpq) w = Pi.single q (T d hex M p q (w p)) := by
  funext z
  simp only [act, sgl, IncidenceAlgebra.coe_mk]
  by_cases hz : z = q
  · subst hz
    rw [Pi.single_eq_same, Finset.sum_eq_single p]
    · simp
    · intro x _ hx; rw [if_neg (fun h ↦ hx h.1), zero_smul]
    · simp
  · rw [Pi.single_eq_of_ne hz]
    exact Finset.sum_eq_zero fun x _ ↦ by rw [if_neg (fun h ↦ hz h.2), zero_smul]

variable {M} {M' : ∀ x y, E x y → (Sp k d x →ₗ[k] Sp k d y)}
  (f : (∀ v, Sp k d v) → (∀ v, Sp k d v))
  (hf : ∀ a w, f (act d hex M a w) = act d hex M' a (f w))
  (hfa : ∀ w w', f (w + w') = f w + f w')

/-- The component maps of an isomorphism. -/
def comp (v : P) (u : Sp k d v) : Sp k d v := f (Pi.single v u) v

include hE huniq hf in
theorem f_single (v : P) (u : Sp k d v) :
    f (Pi.single v u) = Pi.single v (comp d f v u) := by
  have h1 := hf (sgl v v le_rfl) (Pi.single v u)
  rw [act_sgl, act_sgl, T_self d hE huniq hex, T_self d hE huniq hex, LinearMap.id_apply,
    LinearMap.id_apply, Pi.single_eq_same] at h1
  rw [h1]; rfl

include hE huniq hf in
theorem f_smul (c : k) (w : ∀ v, Sp k d v) : f (c • w) = c • f w := by
  have := hf (algebraMap k _ c) w
  rwa [act_algebraMap d hE huniq hex, act_algebraMap d hE huniq hex] at this

/-- The component maps as linear maps. -/
def compL (v : P) : Sp k d v →ₗ[k] Sp k d v where
  toFun := comp d f v
  map_add' u u' := by
    simp only [comp, Pi.single_add, hfa, Pi.add_apply]
  map_smul' c u := by
    simp only [comp, RingHom.id_apply]
    rw [show (Pi.single v (c • u) : ∀ v, Sp k d v) = c • Pi.single v u from Pi.single_smul v c u,
      f_smul d hE huniq hex f hf]
    rfl

include hE huniq hf in
/-- **The arrow relation** `g_q M_e = M'_e g_p`. -/
theorem comp_arrow {p q : P} (h : E p q) (u : Sp k d p) :
    compL d hE huniq hex f hf hfa q (M p q h u) = M' p q h (compL d hE huniq hex f hf hfa p u) := by
  have h1 := hf (sgl p q (hE p q h).le) (Pi.single p u)
  rw [act_sgl, act_sgl, Pi.single_eq_same, f_single d hE huniq hex f hf,
    f_single d hE huniq hex f hf, Pi.single_eq_same, T_arrow d hE huniq hex M h,
    T_arrow d hE huniq hex M' h] at h1
  exact Pi.single_injective q h1

variable (g : (∀ v, Sp k d v) → (∀ v, Sp k d v))
  (hg : ∀ a w, g (act d hex M' a w) = act d hex M a (g w))
  (hga : ∀ w w', g (w + w') = g w + g w') (hgf : ∀ w, g (f w) = w)

include hE huniq hf hg hgf in
theorem comp_left_inv (v : P) (u : Sp k d v) : compL d hE huniq hex g hg hga v (compL d hE huniq hex f hf hfa v u) = u := by
  change g (Pi.single v (comp d f v u)) v = u
  rw [← f_single d hE huniq hex f hf, hgf, Pi.single_eq_same]

end Iso

/-! ### Points of the representation space -/

section Points

variable (E) in
/-- The arrows. -/
abbrev Arr := {e : P × P // E e.1 e.2}

/-- The source of an arrow. -/
abbrev src (a : Arr E) : P := a.1.1

/-- The target of an arrow. -/
abbrev tgt (a : Arr E) : P := a.1.2

variable [DecidableRel E]

/-- The maps of a point of the representation space. -/
def Mpt (x : OrbitDim.Coord d (src (E := E)) tgt → k) : ∀ p q, E p q → (Sp k d p →ₗ[k] Sp k d q) :=
  fun p q h ↦ Matrix.toLin' (OrbitDim.mat x ⟨(p, q), h⟩)

include hE huniq in
/-- **Isomorphic modules are conjugate points.** -/
theorem conj_of_iso (x y : OrbitDim.Coord d (src (E := E)) tgt → k)
    (L : repObj d hE huniq hex (Mpt d x) ≃ₗ[(IncidenceAlgebra k P)ᵐᵒᵖ] repObj d hE huniq hex (Mpt d y)) :
    ∃ g : ∀ v, GL (Fin (d v)) k, y = OrbitDim.act g x := by
  set f : (∀ v, Sp k d v) → (∀ v, Sp k d v) := fun w ↦ L w
  set g : (∀ v, Sp k d v) → (∀ v, Sp k d v) := fun w ↦ L.symm w
  have hf : ∀ a w, f (act d hex (Mpt d x) a w) = act d hex (Mpt d y) a (f w) :=
    fun a w ↦ L.map_smul (MulOpposite.op a) w
  have hfa : ∀ w w', f (w + w') = f w + f w' := fun w w' ↦ L.map_add w w'
  have hg : ∀ a w, g (act d hex (Mpt d y) a w) = act d hex (Mpt d x) a (g w) :=
    fun a w ↦ L.symm.map_smul (MulOpposite.op a) w
  have hga : ∀ w w', g (w + w') = g w + g w' := fun w w' ↦ L.symm.map_add w w'
  have hgf : ∀ w, g (f w) = w := fun w ↦ L.symm_apply_apply w
  have hfg : ∀ w, f (g w) = w := fun w ↦ L.apply_symm_apply w
  set gL := compL d hE huniq hex f hf hfa
  set hL := compL d hE huniq hex g hg hga
  have h1 : ∀ v u, hL v (gL v u) = u := comp_left_inv d hE huniq hex f hf hfa g hg hga hgf
  have h2 : ∀ v u, gL v (hL v u) = u := comp_left_inv d hE huniq hex g hg hga f hf hfa hfg
  let G : ∀ v, GL (Fin (d v)) k := fun v ↦
    ⟨LinearMap.toMatrix' (gL v), LinearMap.toMatrix' (hL v), by
      rw [← LinearMap.toMatrix'_comp,
        show gL v ∘ₗ hL v = LinearMap.id from LinearMap.ext fun u ↦ h2 v u,
        LinearMap.toMatrix'_id], by
      rw [← LinearMap.toMatrix'_comp,
        show hL v ∘ₗ gL v = LinearMap.id from LinearMap.ext fun u ↦ h1 v u,
        LinearMap.toMatrix'_id]⟩
  refine ⟨G, ?_⟩
  funext co
  obtain ⟨⟨⟨p, q⟩, h⟩, i, j⟩ := co
  have harr := comp_arrow d hE huniq hex f hf hfa h
  -- `My = gL q ∘ Mx ∘ hL p`
  have hMy : Mpt d y p q h = gL q ∘ₗ Mpt d x p q h ∘ₗ hL p := by
    refine LinearMap.ext fun u ↦ ?_
    simp only [LinearMap.comp_apply]
    rw [harr, h2]
  have hmat : OrbitDim.mat y ⟨(p, q), h⟩ =
      LinearMap.toMatrix' (gL q) * OrbitDim.mat x ⟨(p, q), h⟩ * LinearMap.toMatrix' (hL p) := by
    have := congrArg LinearMap.toMatrix' hMy
    simp only [Mpt, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_comp] at this
    rw [this, Matrix.mul_assoc]
  change y ⟨⟨(p, q), h⟩, i, j⟩ = (LinearMap.toMatrix' (gL q) * OrbitDim.mat x ⟨(p, q), h⟩ *
    LinearMap.toMatrix' (hL p)) i j
  rw [← hmat]; rfl

/-- The labelled biproducts. -/
def Obj {N : ℕ} (X : Fin N → RightModuleCat (IncidenceAlgebra k P)) (B : ℕ)
    (τ : Σ m : Fin (B + 1), (Fin m → Fin N)) : RightModuleCat (IncidenceAlgebra k P) :=
  ⨁ fun j : Fin τ.1 ↦ X (τ.2 j)

theorem finrank_repObj_le (M : ∀ x y, E x y → (Sp k d x →ₗ[k] Sp k d y)) :
    Module.finrank k (repObj d hE huniq hex M) ≤ ∑ v, d v := by
  have := LinearMap.finrank_le_finrank_of_injective (f := toPi d hE huniq hex M) fun _ _ h ↦ h
  refine this.trans (le_of_eq ?_)
  rw [Module.finrank_pi_fintype]
  simp

include hE huniq hex in
/-- **Lemma 8.8** (`lem:dimension-infinity`) for incidence algebras of posets with unique
paths: if `d ≠ 0` and `∑ d_v² ≤ ∑_{x → y} d_x d_y`, the incidence algebra is
representation-infinite. -/
theorem not_isRepresentationFinite [IsAlgClosed k] (hd : ∃ v, 0 < d v)
    (hN : ∑ v, d v ^ 2 ≤ ∑ a : Arr E, d (tgt a) * d (src a)) :
    ¬ IsRepresentationFinite k (IncidenceAlgebra k P) := by
  classical
  intro hA
  haveI : FiniteDimensional k (IncidenceAlgebra k P) := by
    let f : IncidenceAlgebra k P →ₗ[k] (P → P → k) :=
      { toFun := fun a ↦ ⇑a
        map_add' := fun a b ↦ rfl
        map_smul' := fun c a ↦ rfl }
    exact Module.Finite.of_injective f fun a b h ↦ DFunLike.coe_injective h
  obtain ⟨N, X, -, hX⟩ := exists_labels_iso hA
  set B := ∑ v, d v
  have hfin : ∀ y : OrbitDim.Coord d (src (E := E)) tgt → k,
      Module.Finite k (repObj d hE huniq hex (Mpt d y)) := fun y ↦ repObj_finite d hE huniq hex _
  choose n l hn hiso using fun y ↦ hX _ (hfin y)
  have hnB : ∀ y, n y < B + 1 := fun y ↦
    Nat.lt_succ_of_le ((hn y).trans (finrank_repObj_le d hE huniq hex _))
  let lab : (OrbitDim.Coord d (src (E := E)) tgt → k) → Σ m : Fin (B + 1), (Fin m → Fin N) :=
    fun y ↦ ⟨⟨n y, hnB y⟩, l y⟩
  have hM : ∀ y, Nonempty (repObj d hE huniq hex (Mpt d y) ≅ Obj X B (lab y)) := fun y ↦ hiso y
  let rep : (Σ m : Fin (B + 1), (Fin m → Fin N)) → (OrbitDim.Coord d (src (E := E)) tgt → k) :=
    fun τ ↦ if h : ∃ y, lab y = τ then Classical.choose h else 0
  refine OrbitDim.orbits_not_finite (k := k) 0 Fin.elim0 (fun i ↦ i.elim0)
    (fun _ _ _ i ↦ i.elim0) hd ?_ (Finset.univ.image rep) fun y _ ↦ ?_
  · simp only [OrbitDim.Coord, OrbitDim.GC, Fintype.card_sigma, Fintype.card_prod,
      Fintype.card_fin, add_zero]
    simpa [sq] using hN
  · have hex' : ∃ y', lab y' = lab y := ⟨y, rfl⟩
    have hrep : rep (lab y) = Classical.choose hex' := dif_pos hex'
    have hlab : lab (rep (lab y)) = lab y := by rw [hrep]; exact Classical.choose_spec hex'
    refine ⟨rep (lab y), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have e : repObj d hE huniq hex (Mpt d (rep (lab y))) ≅ repObj d hE huniq hex (Mpt d y) :=
      (hM _).some ≪≫ eqToIso (congrArg (Obj X B) hlab) ≪≫ (hM y).some.symm
    exact conj_of_iso d hE huniq hex _ _ e.toLinearEquiv

end Points

end PosetRep

end MultiplicativeBasisDeformations
