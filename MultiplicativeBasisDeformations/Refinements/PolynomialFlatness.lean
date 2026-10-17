import MultiplicativeBasisDeformations.Refinements.FlatPerturbationDim

/-!
# Corollary 12.4: polynomial mesh flatness

`deformation-refinements.tex` (`cor:polynomial-mesh-flatness`). Replace the higher
coefficients in Lemma 12.3 by elements of a polynomial ring. Every fixed path basis of `C` is a
basis of the resulting family over the polynomial ring, and it remains a basis after arbitrary
base change.

The proof is the source's: spanning holds over any coefficient ring (reduction by the original
relations); independence holds over the fraction field by Lemma 12.3, hence over the polynomial
ring; and the free presentation is stable under base change. We prove independence over any
integral domain `K` receiving `k`, and base change along any ring map `K → R`.

Coefficients are changed by `cmap φ`, which applies a ring map to every coefficient of a
morphism of the path category.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace FlatPert

open LinearPaths

universe u

variable {V : Type} [Quiver.{0} V]

/-! ### Changing coefficients -/

section CMap

variable {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)

/-- **Coefficientwise application of a ring map** `AQ → BQ`. -/
def cmap {x y : V} (g : Hm A x y) : Hm B x y :=
  ofFinsupp (Finsupp.mapRange φ φ.map_zero (toFinsupp g))

theorem cmap_zero {x y : V} : cmap φ (0 : Hm A x y) = 0 := by
  change Finsupp.mapRange φ φ.map_zero 0 = 0
  exact Finsupp.mapRange_zero

theorem cmap_add {x y : V} (g h : Hm A x y) : cmap φ (g + h) = cmap φ g + cmap φ h := by
  change Finsupp.mapRange φ φ.map_zero (toFinsupp g + toFinsupp h) = _
  exact Finsupp.mapRange_add (map_add φ) _ _

theorem cmap_smul {x y : V} (c : A) (g : Hm A x y) : cmap φ (c • g) = φ c • cmap φ g := by
  change Finsupp.mapRange φ φ.map_zero (c • toFinsupp g) =
    φ c • Finsupp.mapRange φ φ.map_zero (toFinsupp g)
  ext p
  simp

theorem cmap_path {x y : V} (p : Quiver.Path x y) : cmap φ (path (k := A) p) = path p := by
  change Finsupp.mapRange φ φ.map_zero (Finsupp.single p 1) = Finsupp.single p 1
  simp

/-- `cmap φ` as an additive map. -/
def cmapHom (x y : V) : Hm A x y →+ Hm B x y where
  toFun := cmap φ
  map_zero' := cmap_zero φ
  map_add' := cmap_add φ

theorem cmap_sub {x y : V} (g h : Hm A x y) : cmap φ (g - h) = cmap φ g - cmap φ h :=
  map_sub (cmapHom φ x y) g h

theorem cmap_sum {x y : V} {ι : Type*} (s : Finset ι) (g : ι → Hm A x y) :
    cmap φ (∑ i ∈ s, g i) = ∑ i ∈ s, cmap φ (g i) :=
  map_sum (cmapHom φ x y) g s

theorem cmap_comp {x y z : V} (g : Hm A x y) (h : Hm A y z) :
    cmap φ (g ≫ h) = cmap φ g ≫ cmap φ h := by
  induction g using induction_on with
  | h0 => simp [cmap_zero]
  | hadd a b ha hb => rw [Preadditive.add_comp, cmap_add, ha, hb, cmap_add, Preadditive.add_comp]
  | hsingle p c =>
    induction h using induction_on with
    | h0 => simp [cmap_zero]
    | hadd a b ha hb =>
      rw [Preadditive.comp_add, cmap_add, ha, hb, cmap_add, Preadditive.comp_add]
    | hsingle q d =>
      simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, path_comp_path, cmap_smul,
        cmap_path, map_mul]

theorem cmap_mem_of_span {x y : V} {s : Set (Hm A x y)} {t : Submodule B (Hm B x y)}
    (h : ∀ g ∈ s, cmap φ g ∈ t) {g : Hm A x y} (hg : g ∈ Submodule.span A s) : cmap φ g ∈ t := by
  induction hg using Submodule.span_induction with
  | mem g hg => exact h g hg
  | zero => rw [cmap_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [cmap_add]; exact add_mem ha hb
  | smul c a _ ha => rw [cmap_smul]; exact Submodule.smul_mem _ _ ha

theorem cmap_degreePart {d : ℕ} {x y : V} {g : Hm A x y} (hg : g ∈ degreePart (k := A) d x y) :
    cmap φ g ∈ degreePart (k := B) d x y := by
  refine cmap_mem_of_span φ ?_ hg
  rintro _ ⟨p, hp, rfl⟩
  rw [cmap_path]
  exact Submodule.subset_span ⟨p, hp, rfl⟩

theorem cmap_geSpan {d : ℕ} {x y : V} {g : Hm A x y} (hg : g ∈ geSpan A d x y) :
    cmap φ g ∈ geSpan B d x y := by
  refine cmap_mem_of_span φ ?_ hg
  rintro _ ⟨p, hp, rfl⟩
  rw [cmap_path]
  exact Submodule.subset_span ⟨p, hp, rfl⟩

/-- **The presentation with changed coefficients.** -/
abbrev Pres.map (P : Pres A V) : Pres B V where
  T := P.T
  fin := P.fin
  src := P.src
  deg := P.deg
  r x t := cmap φ (P.r x t)
  hom x t := cmap_degreePart φ (P.hom x t)
  two := P.two

variable (P : Pres A V)

theorem cmap_ctxSpan (ρ : ∀ x (t : P.T x), Hm A (P.src x t) x) {w y : V} {g : Hm A w y}
    (hg : g ∈ ctxSpan P ρ w y) :
    cmap φ g ∈ ctxSpan (P.map φ) (fun x t ↦ cmap φ (ρ x t)) w y := by
  refine cmap_mem_of_span φ ?_ hg
  rintro _ ⟨x, t, u, v, rfl⟩
  rw [cmap_comp, cmap_comp, cmap_path, cmap_path]
  exact Submodule.subset_span ⟨x, t, u, v, rfl⟩

variable [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [∀ x : V, Fintype (Σ y : V, y ⟶ x)]

theorem cmap_idealC {w y : V} {g : Hm A w y} (hg : g ∈ (idealC P).I w y) :
    cmap φ g ∈ (idealC (P.map φ)).I w y :=
  cmap_ctxSpan φ P P.r hg

variable (f : ∀ x (t : P.T x), Hm A (P.src x t) x)
  (hf : ∀ x t, f x t ∈ geSpan A (P.deg x t + 1) (P.src x t) x) (N : ℕ)

/-- The perturbation with changed coefficients. -/
def fmap : ∀ x (t : (P.map φ).T x), Hm B ((P.map φ).src x t) x := fun x t ↦ cmap φ (f x t)

include hf in
theorem hf_map : ∀ x t, fmap φ P f x t ∈ geSpan B ((P.map φ).deg x t + 1) ((P.map φ).src x t) x :=
  fun x t ↦ cmap_geSpan φ (hf x t)

theorem rf_map (x : V) (t : P.T x) : rf (P.map φ) (fmap φ P f) x t = cmap φ (rf P f x t) :=
  (cmap_sub φ _ _).symm

theorem cmap_idealB {w y : V} {g : Hm A w y} (hg : g ∈ (idealB P f hf N).I w y) :
    cmap φ g ∈ (idealB (P.map φ) (fmap φ P f) (hf_map φ P f hf) N).I w y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hg
  rw [cmap_add]
  refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (cmap_geSpan φ hb))
  have := cmap_ctxSpan φ P (rf P f) ha
  convert this using 2
  funext x t
  exact rf_map φ P f x t

theorem hN_map (hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length →
      path (k := A) p ∈ ctxSpan P P.r w y) :
    ∀ w y (p : Quiver.Path w y), N ≤ p.length → path (k := B) p ∈ ctxSpan (P.map φ) (P.map φ).r w y :=
  fun w y p hp ↦ cmap_path φ p ▸ cmap_ctxSpan φ P P.r (hN w y p hp)

end CMap

/-! ### Spanning and independence of path classes -/

section Classes

variable [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [∀ x : V, Fintype (Σ y : V, y ⟶ x)]

/-- **Spanning criterion**: path classes span `AQ/J` iff every path is a combination of them
modulo `J`. -/
theorem span_classes_eq_top_iff {A : Type*} [CommRing A] (J : IdealFam A V) {w y : V}
    {ι : Type*} (p : ι → Quiver.Path w y) :
    Submodule.span A (Set.range fun i ↦
        Submodule.Quotient.mk (p := J.I w y) (path (k := A) (p i))) = ⊤ ↔
      ∀ q : Quiver.Path w y,
        path (k := A) q ∈ Submodule.span A (Set.range fun i ↦ path (k := A) (p i)) ⊔ J.I w y := by
  set W := Submodule.span A (Set.range fun i ↦ path (k := A) (p i)) ⊔ J.I w y
  have hmap : Submodule.span A (Set.range fun i ↦
      Submodule.Quotient.mk (p := J.I w y) (path (k := A) (p i))) = W.map (J.I w y).mkQ := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq, Submodule.map_span,
      ← Set.range_comp]
    rfl
  have htop : W = ⊤ ↔ ∀ q : Quiver.Path w y, path (k := A) q ∈ W := by
    refine ⟨fun h q ↦ by rw [h]; trivial, fun h ↦ ?_⟩
    have hall : ∀ g : Hm A w y, g ∈ W := by
      intro g
      induction g using induction_on with
      | h0 => exact zero_mem _
      | hadd a b ha hb => exact add_mem ha hb
      | hsingle q c => exact Submodule.smul_mem _ c (h q)
    exact eq_top_iff.2 fun g _ ↦ hall g
  rw [hmap, ← htop]
  constructor
  · intro h
    have := Submodule.comap_map_mkQ (J.I w y) W
    rw [h, Submodule.comap_top] at this
    rw [eq_top_iff, this]
    exact sup_le le_sup_right le_rfl
  · intro h
    rw [h, Submodule.map_top, Submodule.range_mkQ]

variable {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)

/-- **Spanning passes along coefficient changes.** -/
theorem span_classes_map (JA : IdealFam A V) (JB : IdealFam B V)
    (hJ : ∀ w y (g : Hm A w y), g ∈ JA.I w y → cmap φ g ∈ JB.I w y) {w y : V} {ι : Type*}
    (p : ι → Quiver.Path w y)
    (h : Submodule.span A (Set.range fun i ↦
      Submodule.Quotient.mk (p := JA.I w y) (path (k := A) (p i))) = ⊤) :
    Submodule.span B (Set.range fun i ↦
      Submodule.Quotient.mk (p := JB.I w y) (path (k := B) (p i))) = ⊤ := by
  rw [span_classes_eq_top_iff] at h ⊢
  intro q
  obtain ⟨s, hs, i, hi, he⟩ := Submodule.mem_sup.1 (h q)
  rw [← cmap_path φ q, ← he, cmap_add]
  refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (hJ w y i hi))
  refine cmap_mem_of_span φ ?_ hs
  rintro _ ⟨j, rfl⟩
  rw [cmap_path]
  exact Submodule.subset_span ⟨j, rfl⟩

/-- **Independence descends along injective coefficient changes.** -/
theorem linInd_classes_comap (hφ : Function.Injective φ) (JA : IdealFam A V) (JB : IdealFam B V)
    (hJ : ∀ w y (g : Hm A w y), g ∈ JA.I w y → cmap φ g ∈ JB.I w y) {w y : V} {ι : Type*}
    [Fintype ι] (p : ι → Quiver.Path w y)
    (h : LinearIndependent B fun i ↦ Submodule.Quotient.mk (p := JB.I w y) (path (k := B) (p i))) :
    LinearIndependent A fun i ↦ Submodule.Quotient.mk (p := JA.I w y) (path (k := A) (p i)) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro c hc
  have hmem : ∑ i, c i • path (k := A) (p i) ∈ JA.I w y := by
    rw [← Submodule.Quotient.mk_eq_zero, ← hc, ← Submodule.mkQ_apply, map_sum]
    rfl
  have hB := hJ w y _ hmem
  rw [cmap_sum] at hB
  simp only [cmap_smul, cmap_path] at hB
  have h0 := h (fun i ↦ φ (c i)) (by
    rw [← (Submodule.Quotient.mk_eq_zero _).2 hB, ← Submodule.mkQ_apply, map_sum]
    rfl)
  intro i
  exact hφ (by rw [h0 i, map_zero])

end Classes

/-! ### Over a fraction field: Lemma 12.3 with extended coefficients -/

section Finite

variable [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  [Fintype V] [∀ x y : V, Fintype (x ⟶ y)]

/-- If path classes spanning `Q JA` always span `Q JB`, then `dim Q JB ≤ dim Q JA`. -/
theorem finrank_le_of_span {k : Type u} {F : Type*} [Field k] [Field F] (JA : IdealFam k V)
    (JB : IdealFam F V) (w y : V) [FiniteDimensional k (Q JA w y)]
    (hspan : ∀ {ι : Type u} (p : ι → Quiver.Path w y),
      Submodule.span k (Set.range fun i ↦
        Submodule.Quotient.mk (p := JA.I w y) (path (k := k) (p i))) = ⊤ →
      Submodule.span F (Set.range fun i ↦
        Submodule.Quotient.mk (p := JB.I w y) (path (k := F) (p i))) = ⊤) :
    Module.finrank F (Q JB w y) ≤ Module.finrank k (Q JA w y) := by
  classical
  obtain ⟨t, hts, hspan', hli⟩ := exists_linearIndependent k (Set.range fun q : Quiver.Path w y ↦
    Submodule.Quotient.mk (p := JA.I w y) (path (k := k) q))
  have htop : Submodule.span k t = ⊤ := by rw [hspan']; exact span_paths_eq_top JA w y
  have htfin : t.Finite := hli.finite
  haveI : Fintype t := htfin.fintype
  choose pth hpth using fun τ : t ↦ hts τ.2
  have hfam : (fun τ : t ↦ Submodule.Quotient.mk (p := JA.I w y) (path (k := k) (pth τ))) =
      Subtype.val := funext hpth
  have hA : Submodule.span k (Set.range fun τ : t ↦
      Submodule.Quotient.mk (p := JA.I w y) (path (k := k) (pth τ))) = ⊤ := by
    rw [hfam, Subtype.range_coe]; exact htop
  have hB := hspan pth hA
  have hcard : Module.finrank k (Q JA w y) = Fintype.card t := by
    have := finrank_span_eq_card hli
    rw [Subtype.range_coe] at this
    rw [← finrank_top, ← htop, this]
  calc Module.finrank F (Q JB w y)
      = Module.finrank F (Submodule.span F (Set.range fun τ : t ↦
          Submodule.Quotient.mk (p := JB.I w y) (path (k := F) (pth τ)))) := by
        rw [hB, finrank_top]
    _ ≤ Fintype.card t := finrank_range_le_card (R := F) _
    _ = _ := hcard.symm

/-- **Spanning of the perturbation from spanning of `C`, after a change of coefficients.** -/
theorem span_B_of_C {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (P : Pres A V) (N : ℕ)
    (hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length → path (k := A) p ∈ ctxSpan P P.r w y)
    (f : ∀ x (t : (P.map φ).T x), Hm B ((P.map φ).src x t) x)
    (hf : ∀ x t, f x t ∈ geSpan B ((P.map φ).deg x t + 1) ((P.map φ).src x t) x)
    {w y : V} {ι : Type*} (p : ι → Quiver.Path w y)
    (h : Submodule.span A (Set.range fun i ↦
      Submodule.Quotient.mk (p := (idealC P).I w y) (path (k := A) (p i))) = ⊤) :
    Submodule.span B (Set.range fun i ↦
      Submodule.Quotient.mk (p := (idealB (P.map φ) f hf N).I w y) (path (k := B) (p i))) = ⊤ := by
  have h1 := span_classes_map φ (idealC P) (idealC (P.map φ))
    (fun _ _ _ hg ↦ cmap_idealC φ P hg) p h
  have h2 := span_B (P.map φ) f hf N (hN_map φ P N hN) (Set.range p) (by
    rw [← Set.range_comp]; exact h1)
  rw [← Set.range_comp] at h2
  exact h2

variable {k : Type u} {K F : Type*} [Field k] [CommRing K] [Field F] (ι₀ : k →+* K) (j : K →+* F)
  (P : Pres k V) (N : ℕ)
  (hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length → path (k := k) p ∈ ctxSpan P P.r w y)
  (hC : ∀ w x, Function.Injective (relMap P (idealC P) P.r w x) ∧
      LinearMap.ker (alpha (idealC P) w x) ≤ LinearMap.range (relMap P (idealC P) P.r w x))
  (f : ∀ x (t : (P.map ι₀).T x), Hm K ((P.map ι₀).src x t) x)
  (hf : ∀ x t, f x t ∈ geSpan K ((P.map ι₀).deg x t + 1) ((P.map ι₀).src x t) x)

include hN hC in
/-- **Lemma 12.3 after extending coefficients to a field**: the perturbation over `F` has the
dimensions of `C` over `k`. -/
theorem finrank_B_field (w y : V) :
    Module.finrank F (Q (idealB ((P.map ι₀).map j) (fmap j (P.map ι₀) f)
      (hf_map j (P.map ι₀) f hf) N) w y) = Module.finrank k (Q (idealC P) w y) := by
  classical
  set PF := (P.map ι₀).map j
  set fF := fmap j (P.map ι₀) f
  have hfF := hf_map j (P.map ι₀) f hf
  have hNF := hN_map j (P.map ι₀) N (hN_map ι₀ P N hN)
  have hfdC := finiteDimensional_Q (idealC P) (geSpan_le_C P N hN)
  have hfdB := finiteDimensional_Q (idealB PF fF hfF N) (geSpan_le_B PF fF hfF N)
  set H : V → V → ℕ := fun w y ↦ Module.finrank k (Q (idealC P) w y)
  set HB : V → V → ℕ := fun w y ↦ Module.finrank F (Q (idealB PF fF hfF N) w y)
  set A : V → V → ℕ := fun y x ↦ Fintype.card (y ⟶ x)
  set R : V → V → ℕ := fun y x ↦ Fintype.card {t : P.T x // P.src x t = y}
  have hC' : ∀ w x, ∑ y, R y x * H w y + H w x = ∑ y, A y x * H w y + if w = x then 1 else 0 := by
    intro w x
    have := dim_C P N hN hC w x
    rwa [sum_rels P x (fun y ↦ H w y), sum_arrows x (fun y ↦ H w y)] at this
  have hB' : ∀ w x, ∑ y, A y x * HB w y + (if w = x then 1 else 0) ≤
      ∑ y, R y x * HB w y + HB w x := by
    intro w x
    have := dim_B PF fF hfF N hNF w x
    rw [sum_rels PF x (fun y ↦ HB w y), sum_arrows x (fun y ↦ HB w y)] at this
    exact this
  have hle : ∀ w y, HB w y ≤ H w y := fun w y ↦
    finrank_le_of_span (idealC P) (idealB PF fF hfF N) w y fun p hp ↦
      span_B_of_C j (P.map ι₀) N (hN_map ι₀ P N hN) fF hfF p
        (span_classes_map ι₀ (idealC P) (idealC (P.map ι₀))
          (fun _ _ _ hg ↦ cmap_idealC ι₀ P hg) p hp)
  exact congrFun (congrFun (matrix_arg A R H HB hC' hB' hle).1 w) y

include hN hC in
/-- **Independence over an integral domain** (`cor:polynomial-mesh-flatness`, first part): a path
basis of `C` is a basis of the perturbation with coefficients in any domain `K ⊇ k`. -/
theorem path_basis_domain [IsDomain K] {w y : V} {ι : Type*} [Fintype ι]
    (p : ι → Quiver.Path w y)
    (hli : LinearIndependent k fun i ↦
      Submodule.Quotient.mk (p := (idealC P).I w y) (path (k := k) (p i)))
    (hsp : Submodule.span k (Set.range fun i ↦
      Submodule.Quotient.mk (p := (idealC P).I w y) (path (k := k) (p i))) = ⊤) :
    (LinearIndependent K fun i ↦
      Submodule.Quotient.mk (p := (idealB (P.map ι₀) f hf N).I w y) (path (k := K) (p i))) ∧
    Submodule.span K (Set.range fun i ↦
      Submodule.Quotient.mk (p := (idealB (P.map ι₀) f hf N).I w y) (path (k := K) (p i))) = ⊤ := by
  classical
  refine ⟨?_, span_B_of_C ι₀ P N hN f hf p hsp⟩
  let F := FractionRing K
  let j : K →+* F := algebraMap K F
  have hj : Function.Injective j := IsFractionRing.injective K F
  refine linInd_classes_comap j hj _ _ (fun _ _ _ hg ↦ cmap_idealB j (P.map ι₀) f hf N hg) p ?_
  have hfF := hf_map j (P.map ι₀) f hf
  have hspF := span_B_of_C j (P.map ι₀) N (hN_map ι₀ P N hN) (fmap j (P.map ι₀) f) hfF p
    (span_classes_map ι₀ (idealC P) (idealC (P.map ι₀)) (fun _ _ _ hg ↦ cmap_idealC ι₀ P hg) p hsp)
  have hfdB := finiteDimensional_Q (idealB ((P.map ι₀).map j) (fmap j (P.map ι₀) f) hfF N)
    (geSpan_le_B _ _ hfF N)
  have hcard : Fintype.card ι = Module.finrank k (Q (idealC P) w y) := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli (by rw [hsp]))]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank (le_of_eq hspF.symm)
    (by rw [finrank_B_field ι₀ j P N hN hC f hf, hcard])

end Finite

/-! ### Base change -/

section BaseChange

variable [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  {K R : Type*} [CommRing K] [CommRing R] (φ : K →+* R) (P : Pres K V)
  (f : ∀ x (t : P.T x), Hm K (P.src x t) x)
  (hf : ∀ x t, f x t ∈ geSpan K (P.deg x t + 1) (P.src x t) x) (N : ℕ)

/-- **Base change of a free presentation** (`cor:polynomial-mesh-flatness`, second part): if the
classes of a path family are a basis of the perturbation over `K`, they are a basis of the
perturbation over `R` with coefficients changed along `φ : K → R`. -/
theorem path_basis_baseChange {w y : V} {ι : Type*} [Fintype ι] (p : ι → Quiver.Path w y)
    (hli : LinearIndependent K fun i ↦
      Submodule.Quotient.mk (p := (idealB P f hf N).I w y) (path (k := K) (p i)))
    (hsp : Submodule.span K (Set.range fun i ↦
      Submodule.Quotient.mk (p := (idealB P f hf N).I w y) (path (k := K) (p i))) = ⊤) :
    (LinearIndependent R fun i ↦
      Submodule.Quotient.mk (p := (idealB (P.map φ) (fmap φ P f) (hf_map φ P f hf) N).I w y)
        (path (k := R) (p i))) ∧
    Submodule.span R (Set.range fun i ↦
      Submodule.Quotient.mk (p := (idealB (P.map φ) (fmap φ P f) (hf_map φ P f hf) N).I w y)
        (path (k := R) (p i))) = ⊤ := by
  classical
  refine ⟨?_, span_classes_map φ _ _ (fun _ _ _ hg ↦ cmap_idealB φ P f hf N hg) p hsp⟩
  set IK := idealB P f hf N
  set IR := idealB (P.map φ) (fmap φ P f) (hf_map φ P f hf) N
  set b := Module.Basis.mk hli (by rw [hsp])
  -- the coordinates over `K` and over `R`
  set πK : Hm K w y →ₗ[K] (ι →₀ K) := b.repr.toLinearMap ∘ₗ (IK.I w y).mkQ
  set πR : Hm R w y →ₗ[R] (ι →₀ R) :=
    Finsupp.linearCombination R (fun q : Quiver.Path w y ↦
      Finsupp.mapRange φ φ.map_zero (πK (path q))) ∘ₗ (finsuppEquiv (k := R) w y).toLinearMap
  have hπR_path : ∀ q : Quiver.Path w y,
      πR (path q) = Finsupp.mapRange φ φ.map_zero (πK (path q)) := by
    intro q
    change Finsupp.linearCombination R _ (Finsupp.single q 1) = _
    rw [Finsupp.linearCombination_single, one_smul]
  have hπR : ∀ g : Hm K w y, πR (cmap φ g) = Finsupp.mapRange φ φ.map_zero (πK g) := by
    intro g
    induction g using induction_on with
    | h0 => rw [cmap_zero, map_zero, map_zero, Finsupp.mapRange_zero]
    | hadd a b ha hb => rw [cmap_add, map_add, ha, hb, map_add, Finsupp.mapRange_add (map_add φ)]
    | hsingle q c =>
      rw [cmap_smul, cmap_path, map_smul, hπR_path, map_smul]
      ext i
      simp
  have hπK : ∀ g ∈ IK.I w y, πK g = 0 := by
    intro g hg
    change b.repr ((IK.I w y).mkQ g) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hg, map_zero]
  have hker : IR.I w y ≤ LinearMap.ker πR := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨x, t, u, v, rfl⟩
      have e : path (k := R) u ≫ rf (P.map φ) (fmap φ P f) x t ≫ path v =
          cmap φ (path (k := K) u ≫ rf P f x t ≫ path v) := by
        rw [cmap_comp, cmap_comp, cmap_path, cmap_path]
        exact congrArg (fun z ↦ path u ≫ z ≫ path v) (rf_map φ P f x t)
      rw [SetLike.mem_coe, LinearMap.mem_ker, e, hπR,
        hπK _ (Submodule.mem_sup_left (Submodule.subset_span ⟨x, t, u, v, rfl⟩)),
        Finsupp.mapRange_zero]
    · rintro _ ⟨q, hq, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, ← cmap_path φ q, hπR,
        hπK _ (Submodule.mem_sup_right (Submodule.subset_span ⟨q, hq, rfl⟩)),
        Finsupp.mapRange_zero]
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hmem : ∑ i, c i • path (k := R) (p i) ∈ IR.I w y := by
    rw [← Submodule.Quotient.mk_eq_zero, ← hc, ← Submodule.mkQ_apply, map_sum]
    rfl
  have h0 := hker hmem
  rw [LinearMap.mem_ker, map_sum] at h0
  have hb : ∀ j, πK (path (p j)) = Finsupp.single j 1 := by
    intro j
    change b.repr (Submodule.Quotient.mk (path (p j))) = _
    rw [show (Submodule.Quotient.mk (path (k := K) (p j)) : Q IK w y) = b j from
      (Module.Basis.mk_apply hli _ j).symm, b.repr_self]
  simp only [map_smul, hπR_path, hb, Finsupp.mapRange_single, map_one] at h0
  have := congrArg (fun F : ι →₀ R ↦ F i) h0
  simpa [Finsupp.finsetSum_apply, Finsupp.single_apply] using this

end BaseChange

/-! ### Corollary 12.4 -/

section Polynomial

variable [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  [Fintype V] [∀ x y : V, Fintype (x ⟶ y)]

/-- **Corollary 12.4** (`cor:polynomial-mesh-flatness`): in the setting of Lemma 12.3, take the
higher terms `f` with coefficients in a polynomial ring `K = k[t_σ]`. Every path basis of `C` is a
basis of the family `B_K = KQ/(𝔪^{N+1}, r − f)` over `K`, and remains a basis after base change
along any ring map `K → R`. -/
theorem polynomial_flatness {k : Type u} [Field k] (P : Pres k V) (N : ℕ)
    (hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length → path (k := k) p ∈ ctxSpan P P.r w y)
    (hC : ∀ w x, Function.Injective (relMap P (idealC P) P.r w x) ∧
      LinearMap.ker (alpha (idealC P) w x) ≤ LinearMap.range (relMap P (idealC P) P.r w x))
    {σ : Type*}
    (f : ∀ x (t : (P.map (MvPolynomial.C : k →+* MvPolynomial σ k)).T x),
      Hm (MvPolynomial σ k) ((P.map MvPolynomial.C).src x t) x)
    (hf : ∀ x t, f x t ∈ geSpan (MvPolynomial σ k) ((P.map MvPolynomial.C).deg x t + 1)
      ((P.map MvPolynomial.C).src x t) x)
    {w y : V} {ι : Type*} [Fintype ι] (p : ι → Quiver.Path w y)
    (hli : LinearIndependent k fun i ↦
      Submodule.Quotient.mk (p := (idealC P).I w y) (path (k := k) (p i)))
    (hsp : Submodule.span k (Set.range fun i ↦
      Submodule.Quotient.mk (p := (idealC P).I w y) (path (k := k) (p i))) = ⊤) :
    ((LinearIndependent (MvPolynomial σ k) fun i ↦
      Submodule.Quotient.mk (p := (idealB (P.map MvPolynomial.C) f hf N).I w y)
        (path (k := MvPolynomial σ k) (p i))) ∧
    Submodule.span (MvPolynomial σ k) (Set.range fun i ↦
      Submodule.Quotient.mk (p := (idealB (P.map MvPolynomial.C) f hf N).I w y)
        (path (k := MvPolynomial σ k) (p i))) = ⊤) ∧
    ∀ {R : Type*} [CommRing R] (φ : MvPolynomial σ k →+* R),
      (LinearIndependent R fun i ↦
        Submodule.Quotient.mk (p := (idealB ((P.map MvPolynomial.C).map φ)
          (fmap φ (P.map MvPolynomial.C) f) (hf_map φ (P.map MvPolynomial.C) f hf) N).I w y)
          (path (k := R) (p i))) ∧
      Submodule.span R (Set.range fun i ↦
        Submodule.Quotient.mk (p := (idealB ((P.map MvPolynomial.C).map φ)
          (fmap φ (P.map MvPolynomial.C) f) (hf_map φ (P.map MvPolynomial.C) f hf) N).I w y)
          (path (k := R) (p i))) = ⊤ := by
  have hK := path_basis_domain MvPolynomial.C P N hN hC f hf p hli hsp
  exact ⟨hK, fun φ ↦ path_basis_baseChange φ (P.map MvPolynomial.C) f hf N p hK.1 hK.2⟩

end Polynomial

end FlatPert

end MultiplicativeBasisDeformations
