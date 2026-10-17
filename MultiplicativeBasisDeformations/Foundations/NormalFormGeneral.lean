import MultiplicativeBasisDeformations.Foundations.FilteredNormalForm

/-!
# Proposition 5.4 in its general form

`mesh-deformations.tex:212–241` (`prop:filtered-normal-form`): "Let `C = kQ/(r_1, …, r_t)` be a
finite-dimensional graded algebra over any field, with `Q` finite and each `r_i` homogeneous
quadratic. For `q ≥ 3`, let `D_{q-1}` send a family `(f_a)_a`, where `f_a ∈ C_{q-1}` is parallel
to the arrow `a`, to the family whose `i`th entry is the sum, over the arrow occurrences in `r_i`,
of the terms obtained by replacing that occurrence of `a` by `f_a`; these entries lie in `C_q`.
Assume that `D_{q-1}` is surjective for every `q ≥ 3`. Let `E` be a finite filtered algebra, or a
finite filtered category with the vertices of `Q` as objects, with a specified graded
identification `gr E = C`. Then `E` is isomorphic to `C` by a map inducing that identification."

Here `C` is the relation category of the quadratic relations `r_i` (`Rel`), `E` a `k`-linear
category with objects `O x` (`x` a vertex), a finite multiplicative filtration `F` of its Hom
spaces and symbols `σ_d : F^d → C_d` realizing `gr E = C` (`FilteredId`). The proof is the
source's: lift the arrows (`Lifts`); the relation errors lie in `F³`; a degree-`q` error is
`D_{q-1}` of a family, and subtracting its lifts cancels it, the terms with two corrections having
degree `2q - 2 > q` (`exists_correction`); the filtration is finite, so the errors vanish; the
resulting functor `C → E` is bijective on Hom spaces by graded injectivity and surjectivity
(`normalForm`). The case `E = ind(mod A)`, `C = k(Γ_A)` is `IndSkeleton.filteredNormalForm`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MultiplicativeBasisDeformations

namespace GeneralNormalForm

universe u v w u' w'

variable {k : Type u} [Field k] {V : Type v} [Quiver.{w} V]
  {𝓔 : Type u'} [Category.{w'} 𝓔] [Preadditive 𝓔] [Linear k 𝓔] (O : V → 𝓔)

/-! ### Realizing paths -/

section Realize

variable {O} (L : ∀ {x y : V}, (x ⟶ y) → (O x ⟶ O y))

/-- The realization of a path. -/
def pathMap {x : V} : ∀ {y : V}, Quiver.Path x y → (O x ⟶ O y)
  | _, Quiver.Path.nil => 𝟙 _
  | _, Quiver.Path.cons p a => pathMap p ≫ L a

@[simp] theorem pathMap_nil {x : V} : pathMap L (Quiver.Path.nil : Quiver.Path x x) = 𝟙 _ := rfl

@[simp] theorem pathMap_cons {x y z : V} (p : Quiver.Path x y) (a : y ⟶ z) :
    pathMap L (p.cons a) = pathMap L p ≫ L a := rfl

theorem pathMap_comp {x y z : V} (p : Quiver.Path x y) (q : Quiver.Path y z) :
    pathMap L (p.comp q) = pathMap L p ≫ pathMap L q := by
  induction q with
  | nil => simp
  | cons q a ih => simp [Quiver.Path.comp_cons, ih, Category.assoc]

/-- The realization of a morphism of `kQ`. -/
def realize (x y : V) :
    (LinearPaths.obj (k := k) x ⟶ LinearPaths.obj (k := k) y) →ₗ[k] (O x ⟶ O y) :=
  (Finsupp.linearCombination k (pathMap L (x := x) (y := y))).comp
    (LinearPaths.finsuppEquiv (k := k) x y).toLinearMap

theorem realize_path {x y : V} (p : Quiver.Path x y) :
    realize L x y (LinearPaths.path (k := k) p) = pathMap L p := by
  change Finsupp.linearCombination k (pathMap L) (Finsupp.single p 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

theorem realize_comp {x y z : V} (f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y)
    (g : LinearPaths.obj (k := k) y ⟶ LinearPaths.obj z) :
    realize L x z (f ≫ g) = realize L x y f ≫ realize L y z g := by
  induction f using LinearPaths.induction_on with
  | h0 => simp
  | hadd f₁ f₂ h₁ h₂ => rw [Preadditive.add_comp, map_add, map_add, h₁, h₂, Preadditive.add_comp]
  | hsingle p c =>
      induction g using LinearPaths.induction_on with
      | h0 => simp
      | hadd g₁ g₂ h₁ h₂ =>
          rw [Preadditive.comp_add, map_add, map_add, h₁, h₂, Preadditive.comp_add]
      | hsingle q c' =>
          rw [Linear.smul_comp, Linear.comp_smul, LinearPaths.path_comp_path, map_smul, map_smul,
            map_smul, map_smul, realize_path, realize_path, realize_path, pathMap_comp,
            Linear.smul_comp, Linear.comp_smul]

theorem realize_id (x : V) : realize L x x (𝟙 (LinearPaths.obj (k := k) x)) = 𝟙 (O x) :=
  realize_path L Quiver.Path.nil

/-- The functor `kQ → E` sending each arrow to its lift. -/
def pathFunctor : LinearPaths k V ⥤ 𝓔 where
  obj X := O X
  map {X Y} f := realize L X Y f
  map_id X := realize_id L X
  map_comp f g := realize_comp L f g

end Realize

/-! ### Quadratic relations -/

variable {ι : Type} (s t : ι → V)
  (r : ∀ i, LinearPaths.obj (k := k) (s i) ⟶ LinearPaths.obj (k := k) (t i))

/-- The relations `r_i` as a family of morphisms of `kQ`. -/
def Rel : ∀ X Y : LinearPaths k V, Set (X ⟶ Y) :=
  fun X Y ↦ {f | ∃ (i : ι) (hX : X = LinearPaths.obj (s i)) (hY : Y = LinearPaths.obj (t i)),
    f = eqToHom hX ≫ r i ≫ eqToHom hY.symm}

/-- The quotient `kQ → C = kQ/(r)`. -/
abbrev cl : LinearPaths k V ⥤ RelationCategory k (Rel s t r) := RelationCategory.functor k _

/-- The image in `C` of the degree-`d` part. -/
def Cdeg (d : ℕ) (x y : V) :
    Submodule k ((cl s t r).obj (LinearPaths.obj x) ⟶ (cl s t r).obj (LinearPaths.obj y)) :=
  (LinearPaths.degreePart (k := k) d x y).map ((cl s t r).mapLinearMap k)

theorem cl_mem_Cdeg {d : ℕ} {x y : V} {P : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y}
    (hP : P ∈ LinearPaths.degreePart (k := k) d x y) : (cl s t r).map P ∈ Cdeg s t r d x y :=
  ⟨P, hP, rfl⟩

/-! ### The filtered category -/

/-- **A finite filtered category `E` with objects `O x` and `gr E = C`**: a finite multiplicative
filtration `F` of the Hom spaces and symbols `σ_d : F^d → C_d`, onto, with kernel `F^{d+1}`,
multiplicative. -/
structure FilteredId where
  F : ℕ → ∀ x y : V, Submodule k (O x ⟶ O y)
  F_zero : ∀ x y, F 0 x y = ⊤
  F_succ_le : ∀ d x y, F (d + 1) x y ≤ F d x y
  F_comp : ∀ (d e : ℕ) {x y z : V} {f : O x ⟶ O y} {g : O y ⟶ O z}, f ∈ F d x y → g ∈ F e y z →
    f ≫ g ∈ F (d + e) x z
  N : ℕ
  F_N : ∀ x y, F N x y = ⊥
  σ : ℕ → ∀ x y : V, (O x ⟶ O y) →ₗ[k]
    ((cl s t r).obj (LinearPaths.obj x) ⟶ (cl s t r).obj (LinearPaths.obj y))
  σ_mem : ∀ d x y f, f ∈ F d x y → σ d x y f ∈ Cdeg s t r d x y
  σ_ker : ∀ d x y f, f ∈ F d x y → (σ d x y f = 0 ↔ f ∈ F (d + 1) x y)
  σ_surj : ∀ d x y c, c ∈ Cdeg s t r d x y → ∃ f ∈ F d x y, σ d x y f = c
  σ_comp : ∀ (d e : ℕ) {x y z : V} (f : O x ⟶ O y) (g : O y ⟶ O z), f ∈ F d x y → g ∈ F e y z →
    σ (d + e) x z (f ≫ g) = σ d x y f ≫ σ e y z g
  σ_id : ∀ x : V, σ 0 x x (𝟙 (O x)) = 𝟙 _

variable {O s t r} (E : FilteredId O s t r)

namespace FilteredId

theorem F_anti {d d' : ℕ} (h : d ≤ d') (x y : V) : E.F d' x y ≤ E.F d x y := by
  induction d', h using Nat.le_induction with
  | base => exact le_rfl
  | succ d' _ ih => exact (E.F_succ_le d' x y).trans ih

theorem σ_eq_zero {d : ℕ} {x y : V} {f : O x ⟶ O y} (hf : f ∈ E.F (d + 1) x y) :
    E.σ d x y f = 0 :=
  (E.σ_ker d x y f (E.F_succ_le d x y hf)).2 hf

end FilteredId

/-- **Lifts of the arrows**: in `F¹` with symbol the arrow. -/
structure Lifts where
  L : ∀ {x y : V}, (x ⟶ y) → (O x ⟶ O y)
  mem : ∀ {x y : V} (a : x ⟶ y), L a ∈ E.F 1 x y
  sym : ∀ {x y : V} (a : x ⟶ y), E.σ 1 x y (L a) = (cl s t r).map (LinearPaths.arrow a)

namespace Lifts

variable {E} (L : Lifts E)

theorem exists_lifts : Nonempty (Lifts E) := by
  have : ∀ (x y : V) (a : x ⟶ y), ∃ f ∈ E.F 1 x y,
      E.σ 1 x y f = (cl s t r).map (LinearPaths.arrow a) := fun _ _ a ↦
    E.σ_surj 1 _ _ _ (cl_mem_Cdeg s t r (LinearPaths.arrow_mem_degreePart a))
  choose L hL1 hL2 using this
  exact ⟨⟨fun {x y} a ↦ L x y a, fun {x y} a ↦ hL1 x y a, fun {x y} a ↦ hL2 x y a⟩⟩

theorem pathMap_mem {x y : V} (p : Quiver.Path x y) :
    pathMap L.L p ∈ E.F p.length x y ∧
      E.σ p.length x y (pathMap L.L p) = (cl s t r).map (LinearPaths.path p) := by
  induction p with
  | nil =>
      refine ⟨by change _ ∈ E.F 0 _ _; rw [E.F_zero]; trivial, ?_⟩
      change E.σ 0 _ _ (𝟙 _) = (cl s t r).map (𝟙 _)
      rw [E.σ_id, CategoryTheory.Functor.map_id]
  | cons p a ih =>
      rw [pathMap_cons, Quiver.Path.length_cons]
      refine ⟨E.F_comp _ 1 ih.1 (L.mem a), ?_⟩
      rw [E.σ_comp _ 1 _ _ ih.1 (L.mem a), ih.2, L.sym a, ← Functor.map_comp]
      congr 1
      rw [LinearPaths.arrow, LinearPaths.path_comp_path]
      rfl

theorem realize_mem {d : ℕ} {x y : V} {P : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y}
    (hP : P ∈ LinearPaths.degreePart (k := k) d x y) :
    realize L.L x y P ∈ E.F d x y ∧ E.σ d x y (realize L.L x y P) = (cl s t r).map P := by
  induction hP using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨p, rfl, rfl⟩ := hg
      rw [realize_path]
      exact L.pathMap_mem p
  | zero => simp
  | add a c _ _ ha hc =>
      rw [map_add, map_add, ha.2, hc.2, Functor.map_add]
      exact ⟨add_mem ha.1 hc.1, rfl⟩
  | smul c a _ ha =>
      rw [map_smul, map_smul, ha.2, Functor.map_smul]
      exact ⟨Submodule.smul_mem _ c ha.1, rfl⟩

/-- The relation error of the lifts. -/
def error (i : ι) : O (s i) ⟶ O (t i) := realize L.L (s i) (t i) (r i)

theorem r_mem (i : ι) : r i ∈ (CategoricalIdeal.HomIdeal.linearSpan k (Rel s t r)).hom _ _ := by
  change r i ∈ CategoricalIdeal.HomIdeal.generatedHomSubmodule k _ _ _
  exact Submodule.subset_span ⟨_, _, r i, ⟨i, rfl, rfl, by simp⟩, 𝟙 _, 𝟙 _, by simp⟩

theorem cl_r (i : ι) : (cl s t r).map (r i) = 0 :=
  (RelationCategory.functor_map_eq_zero_iff (k := k) _ (r i)).2 (r_mem (s := s) (t := t) (r := r) i)

/-- The relation errors lie in `F³`. -/
theorem error_mem_three (hr : ∀ i, r i ∈ LinearPaths.degreePart (k := k) 2 (s i) (t i)) (i : ι) :
    L.error i ∈ E.F 3 (s i) (t i) := by
  obtain ⟨h1, h2⟩ := L.realize_mem (hr i)
  rw [cl_r] at h2
  exact (E.σ_ker 2 _ _ _ h1).1 h2

end Lifts

/-! ### The derivative `D_{q-1}` -/

/-- Replacing one arrow occurrence of a path by `f_a`, summed over the occurrences. -/
def pathDer (f : ∀ {x y : V}, (x ⟶ y) →
    ((cl s t r).obj (LinearPaths.obj x) ⟶ (cl s t r).obj (LinearPaths.obj y))) {x : V} :
    ∀ {y : V}, Quiver.Path x y →
      ((cl s t r).obj (LinearPaths.obj x) ⟶ (cl s t r).obj (LinearPaths.obj y))
  | _, Quiver.Path.nil => 0
  | _, Quiver.Path.cons p a =>
      pathDer f p ≫ (cl s t r).map (LinearPaths.arrow a) +
        (cl s t r).map (LinearPaths.path p) ≫ f a

/-- Its linear extension to `kQ`. -/
def derL (f : ∀ {x y : V}, (x ⟶ y) →
    ((cl s t r).obj (LinearPaths.obj x) ⟶ (cl s t r).obj (LinearPaths.obj y))) (x y : V) :
    (LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) →ₗ[k]
      ((cl s t r).obj (LinearPaths.obj x) ⟶ (cl s t r).obj (LinearPaths.obj y)) :=
  (Finsupp.linearCombination k (pathDer f (x := x) (y := y))).comp
    (LinearPaths.finsuppEquiv (k := k) x y).toLinearMap

theorem derL_path (f : ∀ {x y : V}, (x ⟶ y) →
    ((cl s t r).obj (LinearPaths.obj x) ⟶ (cl s t r).obj (LinearPaths.obj y))) {x y : V}
    (p : Quiver.Path x y) : derL f x y (LinearPaths.path p) = pathDer f p := by
  change Finsupp.linearCombination k (pathDer f) (Finsupp.single p 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

/-- **The derivative** `D_{q-1}(f)_i`. -/
def Dmap (f : ∀ {x y : V}, (x ⟶ y) →
    ((cl s t r).obj (LinearPaths.obj x) ⟶ (cl s t r).obj (LinearPaths.obj y))) (i : ι) :
    (cl s t r).obj (LinearPaths.obj (s i)) ⟶ (cl s t r).obj (LinearPaths.obj (t i)) :=
  derL f (s i) (t i) (r i)


/-! ### The correction step -/

namespace Lifts

variable {E}

/-- **Cancelling the degree-`q` errors** (`q = q' + 1 ≥ 3`): if the errors lie in `F^q` and
`D_{q-1}(f) = σ_q(errors)`, subtracting lifts of `f` from the arrows pushes the errors into
`F^{q+1}`; a term with two corrections has degree `2q - 2 > q`. -/
theorem exists_correction (L : Lifts E) {q' : ℕ} (hq : 2 ≤ q')
    (hL : ∀ i, L.error i ∈ E.F (q' + 1) (s i) (t i))
    (f : ∀ {x y : V}, (x ⟶ y) →
      ((cl s t r).obj (LinearPaths.obj x) ⟶ (cl s t r).obj (LinearPaths.obj y)))
    (hf : ∀ {x y : V} (a : x ⟶ y), f a ∈ Cdeg s t r q' x y)
    (hD : ∀ i, Dmap f i = E.σ (q' + 1) _ _ (L.error i))
    (hr : ∀ i, r i ∈ LinearPaths.degreePart (k := k) 2 (s i) (t i)) :
    ∃ L' : Lifts E, ∀ i, L'.error i ∈ E.F (q' + 2) (s i) (t i) := by
  have hft : ∀ (x y : V) (a : x ⟶ y), ∃ g ∈ E.F q' x y, E.σ q' x y g = f a :=
    fun x y a ↦ E.σ_surj q' x y _ (hf a)
  choose ft hft1 hft2 using hft
  have hft2' : ∀ {x y : V} (a : x ⟶ y), ft x y a ∈ E.F 2 x y := fun a ↦ E.F_anti hq _ _ (hft1 _ _ a)
  let L' : Lifts E :=
    { L := fun {x y} a ↦ L.L a - ft x y a
      mem := fun a ↦ sub_mem (L.mem a) (E.F_anti (by omega) _ _ (hft1 _ _ a))
      sym := fun a ↦ by
        rw [map_sub, L.sym a, E.σ_eq_zero (hft2' a), sub_zero] }
  -- the change on homogeneous morphisms of degree two
  have key : ∀ {x y : V} {P : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y},
      P ∈ LinearPaths.degreePart (k := k) 2 x y →
      realize L'.L x y P - realize L.L x y P ∈ E.F (q' + 1) x y ∧
        E.σ (q' + 1) x y (realize L'.L x y P - realize L.L x y P) = -derL f x y P := by
    intro x y P hP
    induction hP using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨p, hp, rfl⟩ := hg
        rcases p with _ | ⟨p₁, b⟩
        · simp at hp
        rcases p₁ with _ | ⟨p₀, a⟩
        · simp at hp
        rcases p₀ with _ | ⟨p₀, c⟩
        swap
        · simp at hp
        rw [realize_path, realize_path, derL_path]
        simp only [pathMap_cons, pathMap_nil, Category.id_comp, pathDer, Limits.zero_comp,
          zero_add]
        change (L.L a - ft _ _ a) ≫ (L.L b - ft _ _ b) - L.L a ≫ L.L b ∈ _ ∧ _
        have e : (L.L a - ft _ _ a) ≫ (L.L b - ft _ _ b) - L.L a ≫ L.L b =
            -(ft _ _ a ≫ L.L b) - L.L a ≫ ft _ _ b + ft _ _ a ≫ ft _ _ b := by
          simp only [Preadditive.sub_comp, Preadditive.comp_sub]; abel
        rw [e]
        have m1 : ft _ _ a ≫ L.L b ∈ E.F (q' + 1) _ _ := E.F_comp q' 1 (hft1 _ _ a) (L.mem b)
        have m2 : L.L a ≫ ft _ _ b ∈ E.F (q' + 1) _ _ := by
          rw [add_comm]; exact E.F_comp 1 q' (L.mem a) (hft1 _ _ b)
        have m3 : ft _ _ a ≫ ft _ _ b ∈ E.F (q' + 2) _ _ :=
          E.F_anti (show q' + 2 ≤ q' + q' by omega) _ _ (E.F_comp q' q' (hft1 _ _ a) (hft1 _ _ b))
        refine ⟨add_mem (sub_mem (neg_mem m1) m2) (E.F_succ_le _ _ _ m3), ?_⟩
        rw [map_add, map_sub, map_neg, E.σ_eq_zero m3, add_zero,
          E.σ_comp q' 1 _ _ (hft1 _ _ a) (L.mem b), hft2, L.sym b]
        rw [show q' + 1 = 1 + q' by omega, E.σ_comp 1 q' _ _ (L.mem a) (hft1 _ _ b), hft2, L.sym a]
        have hnil : (cl s t r).map (LinearPaths.path (k := k) (Quiver.Path.nil : Quiver.Path x x)) =
            𝟙 _ := CategoryTheory.Functor.map_id (cl s t r) (LinearPaths.obj x)
        rw [hnil, Category.id_comp]
        change _ = -(f a ≫ (cl s t r).map (LinearPaths.arrow b) +
          (cl s t r).map (LinearPaths.arrow a) ≫ f b)
        abel
    | zero => simp
    | add P₁ P₂ _ _ h₁ h₂ =>
        have e : realize L'.L x y (P₁ + P₂) - realize L.L x y (P₁ + P₂) =
            (realize L'.L x y P₁ - realize L.L x y P₁) + (realize L'.L x y P₂ - realize L.L x y P₂) := by
          rw [map_add, map_add]; abel
        rw [e, map_add, h₁.2, h₂.2, map_add, neg_add]
        exact ⟨add_mem h₁.1 h₂.1, rfl⟩
    | smul c P₁ _ h₁ =>
        rw [map_smul, map_smul, ← smul_sub, map_smul, h₁.2, map_smul, smul_neg]
        exact ⟨Submodule.smul_mem _ c h₁.1, rfl⟩
  refine ⟨L', fun i ↦ ?_⟩
  obtain ⟨k1, k2⟩ := key (hr i)
  have e : L'.error i = L.error i + (realize L'.L _ _ (r i) - realize L.L _ _ (r i)) := by
    change realize L'.L _ _ (r i) = realize L.L _ _ (r i) + _; abel
  have hm : L'.error i ∈ E.F (q' + 1) _ _ := by rw [e]; exact add_mem (hL i) k1
  refine (E.σ_ker (q' + 1) _ _ _ hm).1 ?_
  rw [e, map_add, k2, ← hD i, Dmap, add_neg_cancel]

end Lifts

/-! ### The isomorphism -/

namespace Lifts

variable {E}

/-- Lifts satisfying the relations kill the relation ideal. -/
theorem realize_eq_zero_of_mem (L : Lifts E) (hL : ∀ i, L.error i = 0) {x y : V}
    {G : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y}
    (hG : G ∈ (CategoricalIdeal.HomIdeal.linearSpan k (Rel s t r)).hom _ _) :
    realize L.L x y G = 0 := by
  change G ∈ CategoricalIdeal.HomIdeal.generatedHomSubmodule k _ _ _ at hG
  induction hG using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨X, Y, rr, hrr, a, a', rfl⟩ := hg
      obtain ⟨i, hX, hY, rfl⟩ := hrr
      subst hX hY
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rw [realize_comp, realize_comp]
      have h0 : realize L.L (s i) (t i) (r i) = 0 := hL i
      rw [h0, Limits.zero_comp, Limits.comp_zero]
  | zero => simp
  | add a c _ _ ha hc => rw [map_add, ha, hc, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

/-- **Faithfulness**: a morphism of `kQ` realized to zero lies in the relation ideal. -/
theorem mem_of_realize_eq_zero (L : Lifts E) (hL : ∀ i, L.error i = 0) {x y : V}
    {G : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y} (hG : realize L.L x y G = 0) :
    G ∈ (CategoricalIdeal.HomIdeal.linearSpan k (Rel s t r)).hom _ _ := by
  classical
  obtain ⟨M, hM⟩ := LinearPaths.eq_sum_proj (k := k) G
  have hmem : ∀ {P : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y}, (cl s t r).map P = 0 →
      P ∈ (CategoricalIdeal.HomIdeal.linearSpan k (Rel s t r)).hom _ _ :=
    fun h ↦ (RelationCategory.functor_map_eq_zero_iff (k := k) _ _).1 h
  have hd : ∀ n, ∀ d < n, LinearPaths.proj d x y G ∈
      (CategoricalIdeal.HomIdeal.linearSpan k (Rel s t r)).hom _ _ := by
    intro n
    induction n with
    | zero => intro d hd; omega
    | succ n ih =>
        intro d hd
        rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hd | rfl
        · exact ih d hd
        have hrest : ∀ e ∈ (Finset.range M).erase d,
            realize L.L x y (LinearPaths.proj e x y G) ∈ E.F (d + 1) x y := by
          intro e he
          rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase he) with hed | hed
          · rw [L.realize_eq_zero_of_mem hL (ih e hed)]; exact zero_mem _
          · exact E.F_anti hed _ _ (L.realize_mem (LinearPaths.proj_mem G)).1
        by_cases hdM : d ∈ Finset.range M
        · have hsum : realize L.L x y G = realize L.L x y (LinearPaths.proj d x y G) +
              ∑ e ∈ (Finset.range M).erase d, realize L.L x y (LinearPaths.proj e x y G) := by
            conv_lhs => rw [hM]
            rw [map_sum, ← Finset.add_sum_erase _ _ hdM]
          have h1 : realize L.L x y (LinearPaths.proj d x y G) ∈ E.F (d + 1) x y := by
            have : realize L.L x y (LinearPaths.proj d x y G) =
                -∑ e ∈ (Finset.range M).erase d, realize L.L x y (LinearPaths.proj e x y G) := by
              rw [eq_neg_iff_add_eq_zero, ← hsum, hG]
            rw [this]; exact neg_mem (sum_mem hrest)
          obtain ⟨-, h2⟩ := L.realize_mem (LinearPaths.proj_mem (d := d) G)
          rw [E.σ_eq_zero h1] at h2
          exact hmem h2.symm
        · have : LinearPaths.proj d x y G = 0 := by
            conv_lhs => rw [hM]
            rw [map_sum]
            refine Finset.sum_eq_zero fun e he ↦ ?_
            rw [LinearPaths.proj_of_mem (LinearPaths.proj_mem G), if_neg]
            rintro rfl; exact hdM he
          rw [this]; exact zero_mem _
  rw [hM]
  exact sum_mem fun d _ ↦ hd (d + 1) d (by omega)

/-- **Fullness**: every morphism of `E` is realized. -/
theorem exists_realize_eq (L : Lifts E) {x y : V} (f : O x ⟶ O y) :
    ∃ G : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y, realize L.L x y G = f := by
  have key : ∀ j n, E.N ≤ n + j → ∀ (f : O x ⟶ O y), f ∈ E.F n x y →
      ∃ G : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y, realize L.L x y G = f := by
    intro j
    induction j with
    | zero =>
        intro n hn f hf
        have := E.F_anti (show E.N ≤ n by omega) x y hf
        rw [E.F_N, Submodule.mem_bot] at this
        exact ⟨0, by rw [map_zero, this]⟩
    | succ j ih =>
        intro n hn f hf
        obtain ⟨P, hP, hPf⟩ := E.σ_mem n x y f hf
        obtain ⟨m1, m2⟩ := L.realize_mem hP
        have h1 : f - realize L.L x y P ∈ E.F (n + 1) x y := by
          refine (E.σ_ker n x y _ (sub_mem hf m1)).1 ?_
          rw [map_sub, m2, ← hPf]; exact sub_self _
        obtain ⟨G, hG⟩ := ih (n + 1) (by omega) _ h1
        exact ⟨P + G, by rw [map_add, hG]; abel⟩
  exact key E.N 0 (by omega) f (by rw [E.F_zero]; trivial)

end Lifts

/-- **Proposition 5.4** (`prop:filtered-normal-form`), general form: for quadratic relations
`r_i` with every `D_{q-1}` (`q ≥ 3`) surjective, and a finite filtered category `E` with objects
the vertices and `gr E = C = kQ/(r)`, there are lifts of the arrows satisfying the relations, and
the induced functor `C → E` is full and faithful (an isomorphism of categories on the vertices)
and induces the given identification `gr E = C`. -/
theorem normalForm (E : FilteredId O s t r)
    (hr : ∀ i, r i ∈ LinearPaths.degreePart (k := k) 2 (s i) (t i))
    (hDsurj : ∀ q', 2 ≤ q' → ∀ g : ∀ i, (cl s t r).obj (LinearPaths.obj (s i)) ⟶
        (cl s t r).obj (LinearPaths.obj (t i)), (∀ i, g i ∈ Cdeg s t r (q' + 1) (s i) (t i)) →
      ∃ f : ∀ {x y : V}, (x ⟶ y) →
          ((cl s t r).obj (LinearPaths.obj x) ⟶ (cl s t r).obj (LinearPaths.obj y)),
        (∀ {x y : V} (a : x ⟶ y), f a ∈ Cdeg s t r q' x y) ∧ ∀ i, Dmap f i = g i) :
    ∃ L : Lifts E, (∀ i, L.error i = 0) ∧
      ∃ Φ : RelationCategory k (Rel s t r) ⥤ 𝓔, cl s t r ⋙ Φ = pathFunctor L.L ∧
        Φ.Full ∧ Φ.Faithful ∧
        ∀ (d : ℕ) {x y : V} (P : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y),
          P ∈ LinearPaths.degreePart (k := k) d x y →
          realize L.L x y P ∈ E.F d x y ∧ E.σ d x y (realize L.L x y P) = (cl s t r).map P := by
  -- successive corrections
  have hstep : ∀ n, ∃ L : Lifts E, ∀ i, L.error i ∈ E.F (n + 3) (s i) (t i) := by
    intro n
    induction n with
    | zero =>
        obtain ⟨L⟩ := Lifts.exists_lifts (E := E)
        exact ⟨L, fun i ↦ L.error_mem_three hr i⟩
    | succ n ih =>
        obtain ⟨L, hL⟩ := ih
        obtain ⟨f, hf, hD⟩ := hDsurj (n + 2) (by omega) (fun i ↦ E.σ (n + 3) _ _ (L.error i))
          (fun i ↦ E.σ_mem _ _ _ _ (hL i))
        obtain ⟨L', hL'⟩ := L.exists_correction (q' := n + 2) (by omega) hL f hf hD hr
        exact ⟨L', hL'⟩
  obtain ⟨L, hL⟩ := hstep E.N
  have hL0 : ∀ i, L.error i = 0 := fun i ↦ by
    have := E.F_anti (show E.N ≤ E.N + 3 by omega) _ _ (hL i)
    rwa [E.F_N, Submodule.mem_bot] at this
  let Φ : RelationCategory k (Rel s t r) ⥤ 𝓔 :=
    CategoryTheory.Quotient.lift _ (pathFunctor L.L) fun x y f₁ f₂ h ↦ by
      have h0 := L.realize_eq_zero_of_mem hL0 h
      rw [map_sub, sub_eq_zero] at h0
      exact h0
  have hΦ : cl s t r ⋙ Φ = pathFunctor L.L := CategoryTheory.Quotient.lift_spec _ _ _
  refine ⟨L, hL0, Φ, hΦ, ⟨fun {a a'} f ↦ ?_⟩, ⟨fun {a a'} f g h ↦ ?_⟩,
    fun d x y P hP ↦ L.realize_mem hP⟩
  · obtain ⟨G, hG⟩ := L.exists_realize_eq (x := a.as) (y := a'.as) f
    exact ⟨(cl s t r).map G, hG⟩
  · obtain ⟨F, rfl⟩ := (cl s t r).map_surjective (X := a.as) (Y := a'.as) f
    obtain ⟨G, rfl⟩ := (cl s t r).map_surjective (X := a.as) (Y := a'.as) g
    change realize L.L a.as a'.as F = realize L.L a.as a'.as G at h
    apply CategoryTheory.Quotient.sound
    change F - G ∈ (CategoricalIdeal.HomIdeal.linearSpan k (Rel s t r)).hom _ _
    exact L.mem_of_realize_eq_zero hL0 (by rw [map_sub, h, sub_self])

end GeneralNormalForm

end MultiplicativeBasisDeformations
