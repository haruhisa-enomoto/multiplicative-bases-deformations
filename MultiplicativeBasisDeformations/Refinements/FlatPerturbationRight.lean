module

public import MultiplicativeBasisDeformations.Refinements.FlatPerturbationGr

/-!
# Lemma 12.3 for right modules and first arrows

`lem:flat-mesh-perturbations` is stated for right modules, splitting each relation by its first
arrow; `flat_perturbation` uses the representables `C(−, x)` and last arrows. This file states
the lemma in the manuscript's convention and derives it from the opposite quiver: path reversal
gives isomorphisms `kQ(w, y) ≅ kQᵒᵖ(y, w)` reversing composition (`opE`), carrying the ideals of
`C` and `B` to those of the opposite presentation, and the first-arrow presentations of the right
simple modules to the last-arrow presentations of the representables of `Qᵒᵖ`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory Opposite

namespace MultiplicativeBasisDeformations

namespace FlatPert

universe u

variable {V : Type} [Quiver.{0} V]

/-! ### Path reversal -/

/-- **The reversed path** in the opposite quiver. -/
def pathOp : ∀ {x y : V}, Quiver.Path x y → Quiver.Path (op y) (op x)
  | _, _, .nil => .nil
  | _, _, .cons p e => (Quiver.Hom.op e).toPath.comp (pathOp p)

/-- **The reversed path** of a path of the opposite quiver. -/
def pathUnop : ∀ {a b : Vᵒᵖ}, Quiver.Path a b → Quiver.Path (unop b) (unop a)
  | _, _, .nil => .nil
  | _, _, .cons p e => (Quiver.Hom.unop e).toPath.comp (pathUnop p)

@[simp] theorem pathOp_nil (x : V) : pathOp (Quiver.Path.nil : Quiver.Path x x) = .nil := by
  simp only [pathOp]

theorem pathOp_cons {x y z : V} (p : Quiver.Path x y) (e : y ⟶ z) :
    pathOp (p.cons e) = (Quiver.Hom.op e).toPath.comp (pathOp p) := by simp only [pathOp]

@[simp] theorem pathUnop_nil (a : Vᵒᵖ) : pathUnop (Quiver.Path.nil : Quiver.Path a a) = .nil := by
  simp only [pathUnop]

theorem pathUnop_cons {a b c : Vᵒᵖ} (p : Quiver.Path a b) (e : b ⟶ c) :
    pathUnop (p.cons e) = (Quiver.Hom.unop e).toPath.comp (pathUnop p) := by simp only [pathUnop]

theorem pathOp_toPath {x y : V} (e : x ⟶ y) : pathOp e.toPath = (Quiver.Hom.op e).toPath := by
  rw [Quiver.Hom.toPath, pathOp_cons, pathOp_nil, Quiver.Path.comp_nil]

theorem pathUnop_toPath {a b : Vᵒᵖ} (e : a ⟶ b) :
    pathUnop e.toPath = (Quiver.Hom.unop e).toPath := by
  rw [Quiver.Hom.toPath, pathUnop_cons, pathUnop_nil, Quiver.Path.comp_nil]

theorem pathOp_comp {x y : V} (p : Quiver.Path x y) : ∀ {z : V} (q : Quiver.Path y z),
    pathOp (p.comp q) = (pathOp q).comp (pathOp p)
  | _, .nil => by simp
  | _, .cons q e => by
      rw [Quiver.Path.comp_cons, pathOp_cons, pathOp_cons, pathOp_comp p q, Quiver.Path.comp_assoc]

theorem pathUnop_comp {a b : Vᵒᵖ} (p : Quiver.Path a b) : ∀ {c : Vᵒᵖ} (q : Quiver.Path b c),
    pathUnop (p.comp q) = (pathUnop q).comp (pathUnop p)
  | _, .nil => by simp
  | _, .cons q e => by
      rw [Quiver.Path.comp_cons, pathUnop_cons, pathUnop_cons, pathUnop_comp p q,
        Quiver.Path.comp_assoc]

theorem pathOp_length {x y : V} : ∀ p : Quiver.Path x y, (pathOp p).length = p.length
  | .nil => by simp
  | .cons p e => by
      rw [pathOp_cons, Quiver.Path.length_comp, pathOp_length p, Quiver.Path.length_cons,
        Quiver.Hom.toPath, Quiver.Path.length_cons, Quiver.Path.length_nil]; omega

theorem pathUnop_length {a b : Vᵒᵖ} : ∀ p : Quiver.Path a b, (pathUnop p).length = p.length
  | .nil => by simp
  | .cons p e => by
      rw [pathUnop_cons, Quiver.Path.length_comp, pathUnop_length p, Quiver.Path.length_cons,
        Quiver.Hom.toPath, Quiver.Path.length_cons, Quiver.Path.length_nil]; omega

theorem pathUnop_pathOp {x y : V} : ∀ p : Quiver.Path x y, pathUnop (pathOp p) = p
  | .nil => by simp
  | .cons p e => by
      rw [pathOp_cons, pathUnop_comp, pathUnop_pathOp p, pathUnop_toPath]
      rfl

theorem pathOp_pathUnop {a b : Vᵒᵖ} : ∀ p : Quiver.Path a b, pathOp (pathUnop p) = p
  | .nil => by simp
  | .cons p e => by
      rw [pathUnop_cons, pathOp_comp, pathOp_pathUnop p, pathOp_toPath]
      rfl

/-- Path reversal as an equivalence. -/
def pathEquiv (x y : V) : Quiver.Path x y ≃ Quiver.Path (op y) (op x) where
  toFun := pathOp
  invFun := pathUnop
  left_inv := pathUnop_pathOp
  right_inv := pathOp_pathUnop

/-! ### Reversal on `kQ` -/

open LinearPaths

variable {k : Type u} [Field k]

/-- **Reversal** `kQ(x, y) ≅ kQᵒᵖ(op y, op x)`. -/
def opE (x y : V) : Hm k x y ≃ₗ[k] Hm k (op y) (op x) :=
  (finsuppEquiv x y).trans ((Finsupp.domLCongr (pathEquiv x y)).trans
    (finsuppEquiv (op y) (op x)).symm)

theorem toFinsupp_opE {x y : V} (g : Hm k x y) (q : Quiver.Path (op y) (op x)) :
    toFinsupp (opE x y g) q = toFinsupp g (pathUnop q) := rfl

theorem opE_path {x y : V} (p : Quiver.Path x y) : opE (k := k) x y (path p) = path (pathOp p) := by
  classical
  apply (finsuppEquiv (k := k) (op y) (op x)).injective
  apply Finsupp.ext
  intro q
  change toFinsupp (opE x y (path p)) q = toFinsupp (path (k := k) (pathOp p)) q
  rw [toFinsupp_opE, toFinsupp_path, toFinsupp_path]
  by_cases h : q = pathOp p
  · subst h; rw [pathUnop_pathOp, Finsupp.single_eq_same, Finsupp.single_eq_same]
  · have h1 : ¬ p = pathUnop q := fun h' ↦ h (by rw [h', pathOp_pathUnop])
    have h2 : ¬ pathOp p = q := fun h' ↦ h h'.symm
    rw [Finsupp.single_apply, Finsupp.single_apply, if_neg h1, if_neg h2]

theorem opE_comp {x y z : V} (f : Hm k x y) (g : Hm k y z) :
    opE x z (f ≫ g) = opE y z g ≫ opE x y f := by
  induction f using induction_on with
  | h0 => simp
  | hadd f f' hf hf' => rw [Preadditive.add_comp, map_add, hf, hf', map_add, Preadditive.comp_add]
  | hsingle p c =>
    induction g using induction_on with
    | h0 => simp
    | hadd g g' hg hg' =>
        rw [Preadditive.comp_add, map_add, hg, hg', map_add, Preadditive.add_comp]
    | hsingle q c' =>
        rw [Linear.smul_comp, Linear.comp_smul, map_smul, map_smul, map_smul, map_smul, opE_path,
          opE_path, path_comp_path, opE_path, Linear.smul_comp, Linear.comp_smul, path_comp_path,
          pathOp_comp, smul_smul, smul_smul, mul_comm]

theorem opE_comp3 {w x z y : V} (u : Hm k w x) (r : Hm k x z) (v : Hm k z y) :
    opE w y (u ≫ r ≫ v) = opE z y v ≫ opE x z r ≫ opE w x u := by
  rw [opE_comp, opE_comp, Category.assoc]

theorem opE_id (x : V) : opE (k := k) x x (𝟙 _) = 𝟙 _ := by
  have := opE_path (k := k) (Quiver.Path.nil : Quiver.Path x x)
  rw [pathOp_nil] at this
  exact this

theorem opE_arrow {x y : V} (a : x ⟶ y) :
    opE (k := k) x y (arrow a) = arrow (Quiver.Hom.op a) := by
  rw [arrow, opE_path, pathOp_toPath]; rfl

theorem map_opE_span (S : ℕ → Prop) (x y : V) :
    (Submodule.span k {g | ∃ p : Quiver.Path x y, S p.length ∧ g = path p}).map
        (opE (k := k) x y).toLinearMap =
      Submodule.span k {g | ∃ q : Quiver.Path (op y) (op x), S q.length ∧ g = path q} := by
  rw [Submodule.map_span]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨pathOp p, by rwa [pathOp_length], opE_path p⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨path (pathUnop q), ⟨pathUnop q, by rwa [pathUnop_length], rfl⟩,
      by rw [LinearEquiv.coe_coe, opE_path, pathOp_pathUnop]⟩

theorem map_opE_geSpan (d : ℕ) (x y : V) :
    (geSpan k d x y).map (opE (k := k) x y).toLinearMap = geSpan k d (op y) (op x) :=
  map_opE_span (d ≤ ·) x y

theorem map_opE_degreePart (d : ℕ) (x y : V) :
    (degreePart (k := k) d x y).map (opE (k := k) x y).toLinearMap =
      degreePart (k := k) d (op y) (op x) :=
  map_opE_span (· = d) x y

theorem opE_mem_degreePart {d : ℕ} {x y : V} {g : Hm k x y} (hg : g ∈ degreePart (k := k) d x y) :
    opE x y g ∈ degreePart (k := k) d (op y) (op x) := by
  rw [← map_opE_degreePart]; exact Submodule.mem_map_of_mem hg

theorem opE_mem_geSpan {d : ℕ} {x y : V} {g : Hm k x y} (hg : g ∈ geSpan k d x y) :
    opE x y g ∈ geSpan k d (op y) (op x) := by
  rw [← map_opE_geSpan]; exact Submodule.mem_map_of_mem hg

/-- The arrows out of `x` and the arrows into `op x`. -/
def arrowsOp (x : V) : (Σ y : V, x ⟶ y) ≃ (Σ b : Vᵒᵖ, b ⟶ op x) where
  toFun a := ⟨op a.1, Quiver.Hom.op a.2⟩
  invFun b := ⟨unop b.1, Quiver.Hom.unop b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype V] [∀ x y : V, Fintype (x ⟶ y)]

instance : Fintype Vᵒᵖ := Fintype.ofEquiv V Opposite.equivToOpposite

instance (a b : Vᵒᵖ) : Fintype (a ⟶ b) := Fintype.ofEquiv (unop b ⟶ unop a) Quiver.Hom.opEquiv

/-! ### Presentations by an indexed family of relations -/

/-- **A graded presentation** `C = kQ/(r₁, …, r_t)` with relations `r_i : s_i → t_i`,
homogeneous of degree at least two. -/
structure PresI (k : Type u) [Field k] (V : Type) [Quiver.{0} V] where
  ι : Type
  [fin : Fintype ι]
  s : ι → V
  t : ι → V
  deg : ι → ℕ
  r : ∀ i, Hm k (s i) (t i)
  hom : ∀ i, r i ∈ degreePart (k := k) (deg i) (s i) (t i)
  two : ∀ i, 2 ≤ deg i

attribute [instance] PresI.fin

variable [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] (P : PresI k V)

instance : DecidableEq Vᵒᵖ := fun a b ↦ decidable_of_iff (unop a = unop b) (unop_inj_iff a b)

instance (a b : Vᵒᵖ) : DecidableEq (a ⟶ b) := fun e e' ↦
  decidable_of_iff (Quiver.Hom.unop e = Quiver.Hom.unop e') Quiver.Hom.unop_inj.eq_iff

namespace PresI

/-- A family of maps parallel to the relations, indexed by targets. -/
def famT (ρ : ∀ i, Hm k (P.s i) (P.t i)) (y : V) (j : {i // P.t i = y}) : Hm k (P.s j.1) y :=
  ρ j.1 ≫ eqToHom (congrArg (LinearPaths.obj (k := k)) j.2)

/-- A family of maps parallel to the relations, reversed and indexed by sources. -/
def famO (ρ : ∀ i, Hm k (P.s i) (P.t i)) (a : Vᵒᵖ) (j : {i // P.s i = unop a}) :
    Hm k (op (P.t j.1)) a :=
  opE _ _ (ρ j.1) ≫ eqToHom (congrArg (fun z ↦ LinearPaths.obj (k := k) (op z)) j.2)

@[simp] theorem famT_self (ρ : ∀ i, Hm k (P.s i) (P.t i)) (i : P.ι) :
    P.famT ρ (P.t i) ⟨i, rfl⟩ = ρ i := by simp [famT]

@[simp] theorem famO_self (ρ : ∀ i, Hm k (P.s i) (P.t i)) (i : P.ι) :
    P.famO ρ (op (P.s i)) ⟨i, rfl⟩ = opE _ _ (ρ i) := by simp [famO]

/-- **The presentation indexed by targets.** -/
def toPres : Pres k V where
  T y := {i // P.t i = y}
  src y j := P.s j.1
  deg y j := P.deg j.1
  r := P.famT P.r
  hom y j := by obtain ⟨i, rfl⟩ := j; rw [famT_self]; exact P.hom i
  two y j := P.two j.1

/-- **The opposite presentation** on `Qᵒᵖ`, indexed by the sources of the relations. -/
def opPres : Pres k Vᵒᵖ where
  T a := {i // P.s i = unop a}
  src a j := op (P.t j.1)
  deg a j := P.deg j.1
  r := P.famO P.r
  hom a j := by
    obtain ⟨a⟩ := a
    obtain ⟨i, hi⟩ := j
    change P.s i = a at hi
    subst hi
    rw [famO_self]; exact opE_mem_degreePart (P.hom i)
  two a j := P.two j.1

theorem ctx_mem_T (ρ : ∀ i, Hm k (P.s i) (P.t i)) (i : P.ι) {w y : V} (u : Hm k w (P.s i))
    (v : Hm k (P.t i) y) : u ≫ ρ i ≫ v ∈ ctxSpan P.toPres (P.famT ρ) w y := by
  have := ctx_mem P.toPres (P.famT ρ) (x := P.t i) ⟨i, rfl⟩ u v
  simp only [famT, eqToHom_refl, Category.comp_id] at this
  exact this

theorem ctx_mem_O (ρ : ∀ i, Hm k (P.s i) (P.t i)) (i : P.ι) {a b : Vᵒᵖ} (u : Hm k a (op (P.t i)))
    (v : Hm k (op (P.s i)) b) : u ≫ opE _ _ (ρ i) ≫ v ∈ ctxSpan P.opPres (P.famO ρ) a b := by
  have := ctx_mem P.opPres (P.famO ρ) (x := op (P.s i)) ⟨i, rfl⟩ u v
  simp only [famO, eqToHom_refl, Category.comp_id] at this
  exact this

theorem map_ctx (ρ : ∀ i, Hm k (P.s i) (P.t i)) (w y : V) :
    (ctxSpan P.toPres (P.famT ρ) w y).map (opE (k := k) w y).toLinearMap =
      ctxSpan P.opPres (P.famO ρ) (op y) (op w) := by
  apply le_antisymm
  · apply (Submodule.map_span_le _ _ _).2
    rintro _ ⟨x, ⟨i, hi⟩, u, v, rfl⟩
    subst hi
    change opE w y (path u ≫ P.famT ρ (P.t i) ⟨i, rfl⟩ ≫ path v) ∈ _
    rw [famT_self]
    erw [opE_comp3, opE_path, opE_path]
    exact ctx_mem_O P ρ i _ _
  · apply Submodule.span_le.2
    rintro _ ⟨a, ⟨i, hi⟩, u', v', rfl⟩
    obtain ⟨a⟩ := a
    change P.s i = a at hi
    subst hi
    change path u' ≫ P.famO ρ (op (P.s i)) ⟨i, rfl⟩ ≫ path v' ∈ _
    rw [famO_self]
    refine ⟨path (pathUnop v') ≫ ρ i ≫ path (pathUnop u'), ctx_mem_T P ρ i _ _, ?_⟩
    erw [LinearEquiv.coe_coe, opE_comp3, opE_path, opE_path, pathOp_pathUnop, pathOp_pathUnop]
    rfl

theorem famT_sub (ρ σ : ∀ i, Hm k (P.s i) (P.t i)) :
    (fun y j ↦ P.famT ρ y j - P.famT σ y j) = P.famT (fun i ↦ ρ i - σ i) := by
  funext y j; obtain ⟨i, rfl⟩ := j; simp

theorem famO_sub (ρ σ : ∀ i, Hm k (P.s i) (P.t i)) :
    (fun a j ↦ P.famO ρ a j - P.famO σ a j) = P.famO (fun i ↦ ρ i - σ i) := by
  funext a j; obtain ⟨a⟩ := a; obtain ⟨i, hi⟩ := j; change P.s i = a at hi; subst hi; simp

theorem map_C (w y : V) :
    ((idealC P.toPres).I w y).map (opE (k := k) w y).toLinearMap = (idealC P.opPres).I (op y) (op w) :=
  P.map_ctx P.r w y

variable (f : ∀ i, Hm k (P.s i) (P.t i)) (hf : ∀ i, f i ∈ geSpan k (P.deg i + 1) (P.s i) (P.t i))
  (N : ℕ)

include hf in
theorem hfT (y : V) (j : P.toPres.T y) :
    P.famT f y j ∈ geSpan k (P.toPres.deg y j + 1) (P.toPres.src y j) y := by
  obtain ⟨i, rfl⟩ := j; rw [famT_self]; exact hf i

include hf in
theorem hfO (a : Vᵒᵖ) (j : P.opPres.T a) :
    P.famO f a j ∈ geSpan k (P.opPres.deg a j + 1) (P.opPres.src a j) a := by
  obtain ⟨a⟩ := a; obtain ⟨i, hi⟩ := j; change P.s i = a at hi; subst hi
  rw [famO_self]; exact opE_mem_geSpan (hf i)

/-- The ideal of `B = kQ/(𝔪^{N+1}, r_i − f_i)`. -/
abbrev idealBT : IdealFam k V := idealB P.toPres (P.famT f) (P.hfT f hf) N

/-- The ideal of the opposite of `B`. -/
abbrev idealBO : IdealFam k Vᵒᵖ := idealB P.opPres (P.famO f) (P.hfO f hf) N

theorem map_B (w y : V) :
    ((P.idealBT f hf N).I w y).map (opE (k := k) w y).toLinearMap =
      (P.idealBO f hf N).I (op y) (op w) := by
  change (ctxSpan P.toPres (rf P.toPres (P.famT f)) w y ⊔ geSpan k (N + 1) w y).map _ =
    ctxSpan P.opPres (rf P.opPres (P.famO f)) (op y) (op w) ⊔ geSpan k (N + 1) (op y) (op w)
  rw [Submodule.map_sup, map_opE_geSpan]
  congr 1
  have h1 : rf P.toPres (P.famT f) = P.famT (fun i ↦ P.r i - f i) := P.famT_sub P.r f
  have h2 : rf P.opPres (P.famO f) = P.famO (fun i ↦ P.r i - f i) := P.famO_sub P.r f
  rw [h1, h2]
  exact P.map_ctx _ w y

end PresI

/-! ### Transport of quotients -/

section Transport

variable (J : IdealFam k V) (J' : IdealFam k Vᵒᵖ)
  (hJ : ∀ w y, (J.I w y).map (opE (k := k) w y).toLinearMap = J'.I (op y) (op w))

/-- **Reversal on the quotients** `(kQ/J)(y, w) ≅ (kQᵒᵖ/J')(op w, op y)`. -/
def qE (y w : V) : Q J y w ≃ₗ[k] Q J' (op w) (op y) :=
  Submodule.Quotient.equiv _ _ (opE y w) (hJ y w)

theorem qE_mk {y w : V} (g : Hm k y w) :
    qE J J' hJ y w (Submodule.Quotient.mk g) = Submodule.Quotient.mk (opE y w g) := rfl

include hJ in
theorem finrank_qE (y w : V) :
    Module.finrank k (Q J y w) = Module.finrank k (Q J' (op w) (op y)) :=
  (qE J J' hJ y w).finrank_eq

/-- Left composition with a morphism of `kQ`. -/
def compL {x y w : V} (h : Hm k x y) : Hm k y w →ₗ[k] Hm k x w where
  toFun g := h ≫ g
  map_add' g g' := Preadditive.comp_add _ _ _ _ _ _
  map_smul' c g := Linear.comp_smul _ _ _ _ _ _

/-- Left composition on the quotients. -/
def compQL {x y w : V} (h : Hm k x y) : Q J y w →ₗ[k] Q J x w :=
  Submodule.mapQ _ _ (compL h) fun _ hg ↦ J.comp_left hg h

theorem compQL_mk {x y w : V} (h : Hm k x y) (g : Hm k y w) :
    compQL J h (Submodule.Quotient.mk g) = Submodule.Quotient.mk (h ≫ g) := rfl

theorem qE_compQL {x y w : V} (h : Hm k x y) (q : Q J y w) :
    qE J J' hJ x w (compQL J h q) = compQ J' (opE x y h) (qE J J' hJ y w q) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [compQL_mk, qE_mk, qE_mk, compQ_mk, opE_comp]

end Transport

/-! ### First-arrow components -/

theorem toPath_comp_injective {x y z : V} (a : x ⟶ y) :
    Function.Injective (fun p : Quiver.Path y z ↦ a.toPath.comp p) :=
  Quiver.Path.comp_injective_right _

/-- **The first-arrow components** `f = f₀ + Σ_a a f_a`. -/
def firstComp {x z : V} (a : Σ y : V, x ⟶ y) : Hm k x z →ₗ[k] Hm k a.1 z :=
  Finsupp.lcomapDomain (fun p : Quiver.Path a.1 z ↦ a.2.toPath.comp p) (toPath_comp_injective a.2)

theorem toFinsupp_firstComp {x z : V} (a : Σ y : V, x ⟶ y) (g : Hm k x z)
    (p : Quiver.Path a.1 z) : toFinsupp (firstComp (k := k) a g) p = toFinsupp g (a.2.toPath.comp p) :=
  rfl

theorem lastComp_opE {x z : V} (a : Σ y : V, x ⟶ y) (g : Hm k x z) :
    lastComp (k := k) (arrowsOp x a) (opE x z g) = opE a.1 z (firstComp a g) := by
  apply (finsuppEquiv (k := k) _ _).injective
  apply Finsupp.ext
  intro q
  change toFinsupp g (pathUnop (q.cons (Quiver.Hom.op a.2))) =
    toFinsupp g (a.2.toPath.comp (pathUnop q))
  exact congrArg (toFinsupp g) (pathUnop_cons (V := V) q (Quiver.Hom.op a.2))

/-! ### The first-arrow presentations of the right simple modules -/

section RightSimple

variable (J : IdealFam k V)

/-- The relations starting at `x`, as maps out of `x`. -/
def PresI.famS (ρ : ∀ i, Hm k (P.s i) (P.t i)) (x : V) (i : {i // P.s i = x}) : Hm k x (P.t i.1) :=
  eqToHom (congrArg (LinearPaths.obj (k := k)) i.2.symm) ≫ ρ i.1

theorem PresI.famO_op (ρ : ∀ i, Hm k (P.s i) (P.t i)) (x : V) (i : {i // P.s i = x}) :
    P.famO ρ (op x) i = opE x (P.t i.1) (P.famS ρ x i) := by
  obtain ⟨i, h⟩ := i
  subst h
  simp [PresI.famO, PresI.famS]

/-- **The arrow map** of the right simple module `S_x`, evaluated at `w`:
`⊕_{a : x → y} B(y, w) → B(x, w)`, `(z_a) ↦ Σ_a a z_a`. -/
def alphaR (w x : V) : (∀ a : Σ y : V, x ⟶ y, Q J a.1 w) →ₗ[k] Q J x w :=
  ∑ a : Σ y : V, x ⟶ y, compQL J (arrow a.2) ∘ₗ LinearMap.proj a

/-- **The relation map** `⊕_{r_i : x → t_i} B(t_i, w) → ⊕_{a : x → y} B(y, w)`, splitting each
relation starting at `x` by its first arrows. -/
def relMapR (ρ : ∀ i, Hm k (P.s i) (P.t i)) (w x : V) :
    (∀ i : {i // P.s i = x}, Q J (P.t i.1) w) →ₗ[k] (∀ a : Σ y : V, x ⟶ y, Q J a.1 w) :=
  LinearMap.pi fun a ↦ ∑ i : {i // P.s i = x},
    compQL J (firstComp a (P.famS ρ x i)) ∘ₗ LinearMap.proj i

variable (J' : IdealFam k Vᵒᵖ)
  (hJ : ∀ w y, (J.I w y).map (opE (k := k) w y).toLinearMap = J'.I (op y) (op w))

/-- The arrow terms, reversed. -/
def piA (w x : V) : (∀ a : Σ y : V, x ⟶ y, Q J a.1 w) ≃ₗ[k]
    (∀ b : Σ b : Vᵒᵖ, b ⟶ op x, Q J' (op w) b.1) where
  toFun c b := qE J J' hJ (unop b.1) w (c ((arrowsOp x).symm b))
  invFun c a := (qE J J' hJ a.1 w).symm (c (arrowsOp x a))
  map_add' c c' := by funext b; exact map_add _ _ _
  map_smul' a c := by funext b; exact (qE J J' hJ (unop b.1) w).map_smul a _
  left_inv c := by funext a; exact (qE J J' hJ a.1 w).symm_apply_apply (c a)
  right_inv c := by funext b; exact (qE J J' hJ (unop b.1) w).apply_symm_apply (c b)

/-- The relation terms, reversed. -/
def piR (w x : V) : (∀ i : {i // P.s i = x}, Q J (P.t i.1) w) ≃ₗ[k]
    (∀ j : P.opPres.T (op x), Q J' (op w) (P.opPres.src (op x) j)) :=
  LinearEquiv.piCongrRight fun i ↦ qE J J' hJ (P.t i.1) w

theorem piA_apply (w x : V) (c : ∀ a : Σ y : V, x ⟶ y, Q J a.1 w) (a : Σ y : V, x ⟶ y) :
    piA J J' hJ w x c (arrowsOp x a) = qE J J' hJ a.1 w (c a) := rfl

theorem piR_apply (w x : V) (d : ∀ i : {i // P.s i = x}, Q J (P.t i.1) w) (i : {i // P.s i = x}) :
    piR P J J' hJ w x d i = qE J J' hJ (P.t i.1) w (d i) := rfl

theorem alpha_piA (w x : V) (c : ∀ a : Σ y : V, x ⟶ y, Q J a.1 w) :
    alpha J' (op w) (op x) (piA J J' hJ w x c) = qE J J' hJ x w (alphaR J w x c) := by
  simp only [alpha, alphaR, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum]
  rw [← (arrowsOp x).sum_comp]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [piA_apply, qE_compQL, opE_arrow]
  rfl

theorem relMap_piR (ρ : ∀ i, Hm k (P.s i) (P.t i)) (w x : V)
    (d : ∀ i : {i // P.s i = x}, Q J (P.t i.1) w) :
    relMap P.opPres J' (P.famO ρ) (op w) (op x) (piR P J J' hJ w x d) =
      piA J J' hJ w x (relMapR P J ρ w x d) := by
  funext b
  obtain ⟨a, rfl⟩ := (arrowsOp x).surjective b
  rw [piA_apply]
  simp only [relMap, relMapR, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [qE_compQL, ← lastComp_opE]
  congr 2
  exact congrArg _ (P.famO_op ρ x i)

include hJ in
theorem injective_relMapR_iff (ρ : ∀ i, Hm k (P.s i) (P.t i)) (w x : V) :
    Function.Injective (relMapR P J ρ w x) ↔
      Function.Injective (relMap P.opPres J' (P.famO ρ) (op w) (op x)) := by
  have h := relMap_piR P J J' hJ ρ w x
  constructor
  · intro hinj d₁ d₂ heq
    obtain ⟨e₁, rfl⟩ := (piR P J J' hJ w x).surjective d₁
    obtain ⟨e₂, rfl⟩ := (piR P J J' hJ w x).surjective d₂
    rw [h, h] at heq
    rw [hinj ((piA J J' hJ w x).injective heq)]
  · intro hinj e₁ e₂ heq
    apply (piR P J J' hJ w x).injective
    apply hinj
    rw [h, h, heq]

include hJ in
theorem ker_le_range_iff (ρ : ∀ i, Hm k (P.s i) (P.t i)) (w x : V) :
    LinearMap.ker (alphaR J w x) ≤ LinearMap.range (relMapR P J ρ w x) ↔
      LinearMap.ker (alpha J' (op w) (op x)) ≤
        LinearMap.range (relMap P.opPres J' (P.famO ρ) (op w) (op x)) := by
  have h := relMap_piR P J J' hJ ρ w x
  constructor
  · intro hle c hc
    obtain ⟨c₀, rfl⟩ := (piA J J' hJ w x).surjective c
    rw [LinearMap.mem_ker, alpha_piA, LinearEquiv.map_eq_zero_iff] at hc
    obtain ⟨d₀, hd₀⟩ := hle hc
    exact ⟨piR P J J' hJ w x d₀, by rw [h, hd₀]⟩
  · intro hle c₀ hc₀
    have hc : piA J J' hJ w x c₀ ∈ LinearMap.ker (alpha J' (op w) (op x)) := by
      rw [LinearMap.mem_ker, alpha_piA, LinearMap.mem_ker.1 hc₀, map_zero]
    obtain ⟨d, hd⟩ := hle hc
    obtain ⟨d₀, rfl⟩ := (piR P J J' hJ w x).surjective d
    rw [h] at hd
    exact ⟨d₀, (piA J J' hJ w x).injective hd⟩

end RightSimple

/-! ### Lemma 12.3 -/

/-- **Lemma 12.3** (`lem:flat-mesh-perturbations`), in the source's convention: let
`C = kQ/(r₁, …, r_t)` be a graded presentation with relations of degree at least two such that
the presentations of the right simple modules obtained by splitting each relation by its first
arrow are projective resolutions of length at most two (`hC`: at every `w`, the relation map is
injective and its image is the kernel of the arrow map), let `C_d = 0` for `d ≥ N` (`hN`) and let
`f_i` be parallel to `r_i` of strictly higher degree. Then `B = kQ/(𝔪^{N+1}, r_i − f_i)` has
`gr_𝔪 B ≅ C` (in every degree `d`, paths induce `C_d(w, y) ≅ 𝔪^d B(w, y)/𝔪^{d+1} B(w, y)`), the
dimensions of `C`, every path basis of `C` lifts to a basis of `B`, and splitting the perturbed
relations by their first arrows gives projective resolutions of the right simple modules of `B`. -/
theorem flat_perturbation_right (f : ∀ i, Hm k (P.s i) (P.t i))
    (hf : ∀ i, f i ∈ geSpan k (P.deg i + 1) (P.s i) (P.t i)) (N : ℕ)
    (hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length → path (k := k) p ∈ (idealC P.toPres).I w y)
    (hC : ∀ w x, Function.Injective (relMapR P (idealC P.toPres) P.r w x) ∧
      LinearMap.ker (alphaR (idealC P.toPres) w x) ≤
        LinearMap.range (relMapR P (idealC P.toPres) P.r w x)) :
    (∀ d w y, ∃ e : CD P.toPres d w y ≃ₗ[k] grB P.toPres (P.famT f) (P.hfT f hf) N d w y,
      ∀ g : degreePart (k := k) d w y,
        e ⟨ψC P.toPres d w y g, range_ψC P.toPres d w y ▸ LinearMap.mem_range_self _ g⟩ =
          θ₀ P.toPres (P.famT f) (P.hfT f hf) N d w y g) ∧
    (∀ w y, Module.finrank k (Q (P.idealBT f hf N) w y) =
      Module.finrank k (Q (idealC P.toPres) w y)) ∧
    (∀ (w y : V) {ι : Type} [Fintype ι] (p : ι → Quiver.Path w y),
      LinearIndependent k (fun i ↦ Submodule.Quotient.mk (p := (idealC P.toPres).I w y)
        (path (k := k) (p i))) →
      Submodule.span k (Set.range fun i ↦ Submodule.Quotient.mk (p := (idealC P.toPres).I w y)
        (path (k := k) (p i))) = ⊤ →
      LinearIndependent k (fun i ↦ Submodule.Quotient.mk (p := (P.idealBT f hf N).I w y)
        (path (k := k) (p i))) ∧
      Submodule.span k (Set.range fun i ↦ Submodule.Quotient.mk (p := (P.idealBT f hf N).I w y)
        (path (k := k) (p i))) = ⊤) ∧
    ∀ w x, Function.Injective (relMapR P (P.idealBT f hf N) (fun i ↦ P.r i - f i) w x) ∧
      LinearMap.ker (alphaR (P.idealBT f hf N) w x) ≤
        LinearMap.range (relMapR P (P.idealBT f hf N) (fun i ↦ P.r i - f i) w x) := by
  have hJC := P.map_C (k := k)
  have hJB := P.map_B f hf N
  -- the hypotheses for the opposite presentation
  have hNO : ∀ a b (q : Quiver.Path a b), N ≤ q.length →
      path (k := k) q ∈ ctxSpan P.opPres P.opPres.r a b := by
    intro a b q hq
    obtain ⟨y⟩ := a
    obtain ⟨w⟩ := b
    have h1 := hN w y (pathUnop q) (by rw [pathUnop_length]; exact hq)
    have h2 := Submodule.mem_map_of_mem (f := (opE (k := k) w y).toLinearMap) h1
    rw [hJC] at h2
    rw [LinearEquiv.coe_coe, opE_path, pathOp_pathUnop] at h2
    exact h2
  have hCO : ∀ a b, Function.Injective (relMap P.opPres (idealC P.opPres) P.opPres.r a b) ∧
      LinearMap.ker (alpha (idealC P.opPres) a b) ≤
        LinearMap.range (relMap P.opPres (idealC P.opPres) P.opPres.r a b) := by
    intro a b
    obtain ⟨w⟩ := a
    obtain ⟨x⟩ := b
    exact ⟨(injective_relMapR_iff P _ _ hJC P.r w x).1 (hC w x).1,
      (ker_le_range_iff P _ _ hJC P.r w x).1 (hC w x).2⟩
  have FP := flat_perturbation P.opPres (P.famO f) (P.hfO f hf) N hNO hCO
  have hdim : ∀ w y, Module.finrank k (Q (P.idealBT f hf N) w y) =
      Module.finrank k (Q (idealC P.toPres) w y) := fun w y ↦ by
    rw [finrank_qE _ _ hJB, finrank_qE _ _ hJC]
    exact FP.1 (op y) (op w)
  have hrf : rf P.opPres (P.famO f) = P.famO (fun i ↦ P.r i - f i) := P.famO_sub P.r f
  refine ⟨fun d w y ↦ grIso_of_finrank P.toPres (P.famT f) (P.hfT f hf) N hN hdim d w y, hdim,
    fun w y ι _ p hli hsp ↦
      lift_basis_of_finrank P.toPres (P.famT f) (P.hfT f hf) N hN hdim w y p hli hsp,
    fun w x ↦ ?_⟩
  have h := FP.2.1 (op w) (op x)
  rw [hrf] at h
  exact ⟨(injective_relMapR_iff P _ _ hJB _ w x).2 h.1, (ker_le_range_iff P _ _ hJB _ w x).2 h.2⟩

end FlatPert

end MultiplicativeBasisDeformations
