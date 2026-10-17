import MultiplicativeBasisDeformations.Foundations.RadicalFiltration
import MBDVendor.QSE.CategoryTheory.IyamaKrullSchmidtNormalForm
import MBDVendor.QSE.RepresentationTheory.AlmostSplitKernel

/-!
# Lemma 2.5: strict radical layers

Lemma 2.5 (`lem:strict-radical-layers`, `graded-category.tex`). Let
`J` be the radical of the category of finite-length modules and let
`a : U → Y` be a radical monomorphism such that `a + h` is monic for every
`h ∈ J²(U, Y)`. Then for every `W` and `n ≥ 1`,
`a ∘ z ∈ J^n(W, Y) ⇔ z ∈ J^{n-1}(W, U)`. Every direct sum of left almost split
inclusions satisfies the hypothesis.

This file proves the lemma in an additive category with kernels and binary
biproducts, for the categorical radical ideal `I` (the vendored `homIdeal`) and
its powers, under two hypotheses which hold for `mod A`:

* every object `Y` has a *right radical approximation*: a radical map
  `p : E → Y` through which every radical map into `Y` factors, with a radical
  monic kernel `i : T → E` such that every map in `I²(T, Z)` is `i ≫ q` with `q`
  radical (in the manuscript, `p` is the sum of the minimal right almost split
  maps of the summands of `Y`, with `rad P → P` at projective summands, and `i`
  is a sum of left almost split inclusions);
* the Krull–Schmidt normal form: every map becomes, after an isomorphism of its
  source, a row of a split monomorphism and a radical map (the manuscript's
  "split off the invertible blocks of `u`").

The proof is the manuscript's: the identity
`p ∘ J^n(W, E) = J^{n+1}(W, Y)` (`eq:right-radical-surjection`), splitting off
the given monomorphism, the complementary monomorphism `b` with the same
perturbation property, and induction on the radical degree for all such
monomorphisms simultaneously. In Lean composition is written `z ≫ a` for the
manuscript's `a ∘ z`, and the exponents are shifted: `z ≫ a ∈ I^{n+1}` implies
`z ∈ I^n`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE.CategoricalRadical MBDVendor.QSE.CategoricalIdeal

namespace MultiplicativeBasisDeformations.StrictLayers

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The `n`-th power of the categorical radical. -/
abbrev Ipow (n : ℕ) : HomIdeal C := HomIdeal.pow (homIdeal : HomIdeal C) n

theorem mem_Ipow_one_iff {X Y : C} (f : X ⟶ Y) :
    f ∈ (Ipow 1 : HomIdeal C).hom X Y ↔ IsRadicalMorphism f := by
  rw [Ipow, HomIdeal.pow_one, mem_homIdeal_iff]

/-- A radical map followed by a map of `I^n` lies in `I^{n+1}`. -/
theorem rad_comp_mem {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsRadicalMorphism f)
    {n : ℕ} (hg : g ∈ (Ipow n : HomIdeal C).hom Y Z) :
    f ≫ g ∈ (Ipow (n + 1) : HomIdeal C).hom X Z := by
  rw [Ipow, HomIdeal.pow_succ_eq_mul_pow]
  exact HomIdeal.comp_mem_mul ((mem_homIdeal_iff f).2 hf) hg

/-- A map of `I^n` followed by a radical map lies in `I^{n+1}`. -/
theorem comp_rad_mem {X Y Z : C} {n : ℕ} {f : X ⟶ Y}
    (hf : f ∈ (Ipow n : HomIdeal C).hom X Y) {g : Y ⟶ Z} (hg : IsRadicalMorphism g) :
    f ≫ g ∈ (Ipow (n + 1) : HomIdeal C).hom X Z := by
  rw [Ipow, HomIdeal.pow_succ]
  exact HomIdeal.comp_mem_mul hf ((mem_homIdeal_iff g).2 hg)

theorem rad_comp_rad_mem {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsRadicalMorphism f)
    (hg : IsRadicalMorphism g) : f ≫ g ∈ (Ipow 2 : HomIdeal C).hom X Z :=
  rad_comp_mem hf ((mem_Ipow_one_iff g).2 hg)

theorem mem_Ipow_of_succ {X Y : C} {n : ℕ} {f : X ⟶ Y}
    (hf : f ∈ (Ipow (n + 1) : HomIdeal C).hom X Y) : f ∈ (Ipow n : HomIdeal C).hom X Y :=
  HomIdeal.pow_succ_le_pow _ n X Y hf

/-- `1 + q` is invertible for a radical endomorphism `q`. -/
theorem isIso_one_add_of_rad {X : C} {q : X ⟶ X} (hq : IsRadicalMorphism q) :
    IsIso (𝟙 X + q) := by
  have h := hq (-𝟙 X)
  simpa using h

/-- A right radical approximation of `Y` (see the module docstring). -/
structure RightRadicalApprox (Y : C) where
  E : C
  p : E ⟶ Y
  T : C
  i : T ⟶ E
  p_rad : IsRadicalMorphism p
  factors : ∀ {W : C} (g : W ⟶ Y), IsRadicalMorphism g → ∃ g' : W ⟶ E, g' ≫ p = g
  i_p : i ≫ p = 0
  lift : ∀ {W : C} (w : W ⟶ E), w ≫ p = 0 → ∃ s : W ⟶ T, s ≫ i = w
  i_mono : Mono i
  i_rad : IsRadicalMorphism i
  sq : ∀ {Z : C} (g : T ⟶ Z), g ∈ (Ipow 2 : HomIdeal C).hom T Z →
    ∃ q : E ⟶ Z, IsRadicalMorphism q ∧ i ≫ q = g

variable [HasBinaryBiproducts C]

/-- The Krull–Schmidt split–radical normal form. -/
def HasSplitRadicalNormalForm (C : Type u) [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] : Prop :=
  ∀ {U E : C} (u : U ⟶ E), ∃ (Z U' : C) (e : U ≅ Z ⊞ U') (j : Z ⟶ E) (r : U' ⟶ E),
    IsSplitMono j ∧ IsRadicalMorphism r ∧ e.inv ≫ u = biprod.desc j r

namespace RightRadicalApprox

variable {Y : C} (P : RightRadicalApprox Y)

/-- `eq:right-radical-surjection`: every map of `I^{n+1}(W, Y)` is `w ≫ p` with
`w ∈ I^n(W, E)`. -/
theorem exists_lift_of_mem {W : C} {n : ℕ} {g : W ⟶ Y}
    (hg : g ∈ (Ipow (n + 1) : HomIdeal C).hom W Y) :
    ∃ w : W ⟶ P.E, w ∈ (Ipow n : HomIdeal C).hom W P.E ∧ w ≫ P.p = g := by
  rw [Ipow, HomIdeal.pow_succ] at hg
  induction hg using AddSubgroup.closure_induction with
  | mem h hh =>
      obtain ⟨M, u, v, hu, hv, rfl⟩ := hh
      obtain ⟨v', hv'⟩ := P.factors v ((mem_homIdeal_iff v).1 hv)
      exact ⟨u ≫ v', (Ipow n : HomIdeal C).postcomp v' hu, by rw [Category.assoc, hv']⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
      obtain ⟨w₁, hw₁, rfl⟩ := ha
      obtain ⟨w₂, hw₂, rfl⟩ := hb
      exact ⟨w₁ + w₂, add_mem hw₁ hw₂, by rw [Preadditive.add_comp]⟩
  | neg a _ ha =>
      obtain ⟨w, hw, rfl⟩ := ha
      exact ⟨-w, neg_mem hw, by rw [Preadditive.neg_comp]⟩

end RightRadicalApprox

/-- Splitting off: if `u ≫ p = a` with `a` having the perturbation property and
`p` radical, then `u` is a split monomorphism. -/
theorem isSplitMono_of_perturbation (hnf : HasSplitRadicalNormalForm C)
    {U E Y : C} (u : U ⟶ E) (p : E ⟶ Y) (hp : IsRadicalMorphism p)
    (hpert : ∀ h ∈ (Ipow 2 : HomIdeal C).hom U Y, Mono (u ≫ p + h)) :
    IsSplitMono u := by
  obtain ⟨Z, U', e, j, r, hj, hr, hu⟩ := hnf u
  -- the inclusion of `U'` into `U`
  let ι : U' ⟶ U := biprod.inr ≫ e.inv
  let h : U ⟶ Y := -(e.hom ≫ biprod.snd ≫ r ≫ p)
  have hh : h ∈ (Ipow 2 : HomIdeal C).hom U Y := by
    apply neg_mem
    exact (Ipow 2 : HomIdeal C).precomp _ ((Ipow 2 : HomIdeal C).precomp _
      (rad_comp_rad_mem hr hp))
  have hu' : u = e.hom ≫ biprod.desc j r := by
    rw [← hu]; simp
  have hzero : ι ≫ (u ≫ p + h) = 0 := by
    simp only [ι, h, hu', Preadditive.comp_add, Preadditive.comp_neg, Category.assoc,
      Iso.inv_hom_id_assoc, biprod.inr_desc_assoc, biprod.inr_snd_assoc]
    simp
  haveI := hpert h hh
  have hι : ι = 0 := by
    rw [← cancel_mono (u ≫ p + h)]
    simpa using hzero
  have hU' : IsZero U' := by
    rw [IsZero.iff_id_eq_zero]
    calc 𝟙 U' = ι ≫ e.hom ≫ biprod.snd := by simp [ι]
      _ = 0 := by rw [hι, zero_comp]
  have hsnd : (biprod.snd : Z ⊞ U' ⟶ U') = 0 := hU'.eq_of_tgt _ _
  obtain ⟨⟨ρ, hρ⟩⟩ := hj
  refine IsSplitMono.mk' ⟨ρ ≫ biprod.inl ≫ e.inv, ?_⟩
  rw [hu']
  have hfst : biprod.desc j r ≫ ρ = biprod.fst := by
    apply biprod.hom_ext'
    · simp [hρ]
    · exact hU'.eq_of_src _ _
  calc (e.hom ≫ biprod.desc j r) ≫ ρ ≫ biprod.inl ≫ e.inv
      = e.hom ≫ (biprod.fst ≫ biprod.inl) ≫ e.inv := by
        rw [← hfst]; simp only [Category.assoc]
    _ = e.hom ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ e.inv := by
        rw [hsnd]; simp
    _ = 𝟙 U := by rw [biprod.total]; simp

section Strict

variable [HasKernels C]

/-- **Lemma 2.5** (`lem:strict-radical-layers`), abstract form. Let `a : U ⟶ Y`
be radical with `a + h` monic for every `h ∈ I²(U, Y)`. Then
`z ≫ a ∈ I^{n+1}(W, Y)` implies `z ∈ I^n(W, U)`. -/
theorem strict (hnf : HasSplitRadicalNormalForm C)
    (approx : ∀ Y : C, RightRadicalApprox Y) :
    ∀ (n : ℕ) {U Y : C} (a : U ⟶ Y), IsRadicalMorphism a →
      (∀ h ∈ (Ipow 2 : HomIdeal C).hom U Y, Mono (a + h)) →
      ∀ {W : C} (z : W ⟶ U), z ≫ a ∈ (Ipow (n + 1) : HomIdeal C).hom W Y →
        z ∈ (Ipow n : HomIdeal C).hom W U := by
  intro n
  induction n with
  | zero =>
      intro U Y a _ _ W z _
      trivial
  | succ n ih =>
      intro U Y a ha hpert W z hz
      let P := approx Y
      obtain ⟨u, hu⟩ := P.factors a ha
      have hsplit : IsSplitMono u :=
        isSplitMono_of_perturbation hnf u P.p P.p_rad (by rw [hu]; exact hpert)
      obtain ⟨⟨ρ, hρ⟩⟩ := hsplit
      -- the complement `V = ker ρ`
      let V := kernel ρ
      let ιV : V ⟶ P.E := kernel.ι ρ
      have hρu : (𝟙 P.E - ρ ≫ u) ≫ ρ = 0 := by
        simp [Preadditive.sub_comp, Category.assoc, hρ]
      let πV : P.E ⟶ V := kernel.lift ρ (𝟙 P.E - ρ ≫ u) hρu
      have hπι : πV ≫ ιV = 𝟙 P.E - ρ ≫ u := kernel.lift_ι _ _ _
      have hιρ : ιV ≫ ρ = 0 := kernel.condition ρ
      have hιπ : ιV ≫ πV = 𝟙 V := by
        rw [← cancel_mono ιV, Category.assoc, hπι]
        simp [Preadditive.comp_sub, ← Category.assoc, hιρ]
      have huπ : u ≫ πV = 0 := by
        rw [← cancel_mono ιV, Category.assoc, hπι]
        simp [Preadditive.comp_sub, reassoc_of% hρ]
      have hdecomp : πV ≫ ιV + ρ ≫ u = 𝟙 P.E := by rw [hπι]; abel
      let f : V ⟶ Y := ιV ≫ P.p
      let b : P.T ⟶ V := P.i ≫ πV
      let c : P.T ⟶ U := P.i ≫ ρ
      have hf : IsRadicalMorphism f := isRadicalMorphism_precomp _ P.p_rad
      have hb_rad : IsRadicalMorphism b := isRadicalMorphism_postcomp _ P.i_rad
      have hc_rad : IsRadicalMorphism c := isRadicalMorphism_postcomp _ P.i_rad
      -- the complementary monomorphism has the perturbation property
      have hbpert : ∀ h ∈ (Ipow 2 : HomIdeal C).hom P.T V, Mono (b + h) := by
        intro h hh
        obtain ⟨q, hq, rfl⟩ := P.sq h hh
        let qV : V ⟶ V := ιV ≫ q
        let qU : U ⟶ V := u ≫ q
        have hqV : IsRadicalMorphism qV := isRadicalMorphism_precomp _ hq
        have hqU : IsRadicalMorphism qU := isRadicalMorphism_precomp _ hq
        haveI : IsIso (𝟙 V + qV) := isIso_one_add_of_rad hqV
        let a' : U ⟶ Y := a + -(qU ≫ inv (𝟙 V + qV) ≫ f)
        have ha'mem : -(qU ≫ inv (𝟙 V + qV) ≫ f) ∈ (Ipow 2 : HomIdeal C).hom U Y := by
          apply neg_mem
          rw [← Category.assoc]
          exact rad_comp_rad_mem (isRadicalMorphism_postcomp _ hqU) hf
        haveI ha' : Mono a' := hpert _ ha'mem
        apply Preadditive.mono_of_cancel_zero
        intro W t ht
        let t' : W ⟶ P.E := t ≫ P.i
        have ht'p : t' ≫ P.p = 0 := by simp [t', P.i_p]
        let tV : W ⟶ V := t' ≫ πV
        let tU : W ⟶ U := t' ≫ ρ
        have ht'split : t' = tV ≫ ιV + tU ≫ u := by
          simp only [tV, tU, Category.assoc, ← Preadditive.comp_add, hdecomp, Category.comp_id]
        have h0 : t' ≫ πV + t' ≫ q = 0 := by
          simpa [t', b, Preadditive.comp_add, Category.assoc] using ht
        have h1 : tV ≫ (𝟙 V + qV) = -(tU ≫ qU) := by
          have : tV + (tV ≫ ιV + tU ≫ u) ≫ q = 0 := by rw [← ht'split]; exact h0
          simp only [Preadditive.add_comp, Category.assoc] at this
          simp only [Preadditive.comp_add, Category.comp_id, qV, qU]
          rw [eq_neg_iff_add_eq_zero, ← this]
          abel
        have h2 : tV = -(tU ≫ qU ≫ inv (𝟙 V + qV)) := by
          calc tV = (tV ≫ (𝟙 V + qV)) ≫ inv (𝟙 V + qV) := by
                rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
            _ = _ := by rw [h1]; simp
        have h3 : tU ≫ a' = 0 := by
          have : t' ≫ P.p = tV ≫ f + tU ≫ a := by
            rw [ht'split, Preadditive.add_comp, Category.assoc, Category.assoc, ← hu]
            simp only [Category.assoc]
          rw [ht'p, h2] at this
          simp only [a', Preadditive.comp_add, Preadditive.comp_neg, Category.assoc]
          rw [add_comm]
          simpa [Category.assoc] using this.symm
        have htU : tU = 0 := (cancel_mono a').1 (by simpa using h3)
        have htV : tV = 0 := by rw [h2, htU]; simp
        have ht' : t' = 0 := by rw [ht'split, htU, htV]; simp
        haveI := P.i_mono
        exact (cancel_mono P.i).1 (by simpa [t'] using ht')
      -- the induction step
      obtain ⟨w, hw, hwp⟩ := P.exists_lift_of_mem (n := n + 1) hz
      have hker : (w - z ≫ u) ≫ P.p = 0 := by
        rw [Preadditive.sub_comp, hwp, Category.assoc, hu, sub_self]
      obtain ⟨s, hs⟩ := P.lift _ hker
      have hsb : s ≫ b = w ≫ πV := by
        change s ≫ P.i ≫ πV = _
        rw [← Category.assoc, hs, Preadditive.sub_comp, Category.assoc, huπ, comp_zero,
          sub_zero]
      have hsc : s ≫ c = w ≫ ρ - z := by
        change s ≫ P.i ≫ ρ = _
        rw [← Category.assoc, hs, Preadditive.sub_comp, Category.assoc, hρ, Category.comp_id]
      have hsmem : s ∈ (Ipow n : HomIdeal C).hom _ _ :=
        ih b hb_rad hbpert s (by rw [hsb]; exact (Ipow (n + 1) : HomIdeal C).postcomp _ hw)
      have hz' : z = w ≫ ρ - s ≫ c := by rw [hsc]; abel
      rw [hz']
      exact sub_mem ((Ipow (n + 1) : HomIdeal C).postcomp _ hw) (comp_rad_mem hsmem hc_rad)

/-- The reverse implication of Lemma 2.5: `z ∈ I^n` implies `z ≫ a ∈ I^{n+1}`
for radical `a`. -/
theorem comp_mem_of_mem {U Y W : C} {a : U ⟶ Y} (ha : IsRadicalMorphism a) {n : ℕ}
    {z : W ⟶ U} (hz : z ∈ (Ipow n : HomIdeal C).hom W U) :
    z ≫ a ∈ (Ipow (n + 1) : HomIdeal C).hom W Y :=
  comp_rad_mem hz ha

end Strict

/-- A left almost-split-type map `i` (every map of `I²` out of its source factors
as `i ≫ q` with `q` radical) satisfies the perturbation hypothesis of Lemma 2.5:
`i + h = i ≫ (1 + q)` is monic for every `h ∈ I²`. -/
theorem perturbation_of_factor {T E : C} (i : T ⟶ E) [Mono i]
    (hsq : ∀ (g : T ⟶ E), g ∈ (Ipow 2 : HomIdeal C).hom T E →
      ∃ q : E ⟶ E, IsRadicalMorphism q ∧ i ≫ q = g) :
    ∀ h ∈ (Ipow 2 : HomIdeal C).hom T E, Mono (i + h) := by
  intro h hh
  obtain ⟨q, hq, rfl⟩ := hsq h hh
  haveI := isIso_one_add_of_rad hq
  have : i + i ≫ q = i ≫ (𝟙 E + q) := by simp [Preadditive.comp_add]
  rw [this]
  infer_instance

end MultiplicativeBasisDeformations.StrictLayers

namespace MultiplicativeBasisDeformations.StrictLayers

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE.CategoricalRadical MBDVendor.QSE.CategoricalIdeal

universe v' u'

variable {C : Type u'} [Category.{v'} C] [Preadditive C] [HasBinaryBiproducts C] [HasKernels C]

namespace RightRadicalApprox

variable {Y : C} (P : RightRadicalApprox Y)

/-- The kernel map of a right radical approximation has the perturbation
property of Lemma 2.5. -/
theorem i_perturbation : ∀ h ∈ (Ipow 2 : HomIdeal C).hom P.T P.E, Mono (P.i + h) := by
  haveI := P.i_mono
  exact perturbation_of_factor P.i (fun g hg ↦ P.sq g hg)

/-- Injectivity on layers (Prop 2.6(1), first map): `z ≫ i ∈ I^{n+2}` implies
`z ∈ I^{n+1}`. -/
theorem layer_injective (hnf : HasSplitRadicalNormalForm C)
    (approx : ∀ Y : C, RightRadicalApprox Y) {W : C} {n : ℕ} (z : W ⟶ P.T)
    (hz : z ≫ P.i ∈ (Ipow (n + 2) : HomIdeal C).hom W P.E) :
    z ∈ (Ipow (n + 1) : HomIdeal C).hom W P.T :=
  strict hnf approx (n + 1) P.i P.i_rad P.i_perturbation z hz

/-- Exactness at the middle term on layers (Prop 2.6(1)): if `w ∈ I^{n+1}`
and `w ≫ p ∈ I^{n+3}`, then `w ≡ z ≫ i` modulo `I^{n+2}` for some `z ∈ I^n`. -/
theorem layer_exact (hnf : HasSplitRadicalNormalForm C)
    (approx : ∀ Y : C, RightRadicalApprox Y) {W : C} {n : ℕ} (w : W ⟶ P.E)
    (hw : w ∈ (Ipow (n + 1) : HomIdeal C).hom W P.E)
    (hwp : w ≫ P.p ∈ (Ipow (n + 3) : HomIdeal C).hom W Y) :
    ∃ z : W ⟶ P.T, z ∈ (Ipow n : HomIdeal C).hom W P.T ∧
      w - z ≫ P.i ∈ (Ipow (n + 2) : HomIdeal C).hom W P.E := by
  obtain ⟨w', hw', hw'p⟩ := P.exists_lift_of_mem (n := n + 2) hwp
  have hker : (w - w') ≫ P.p = 0 := by rw [Preadditive.sub_comp, hw'p, sub_self]
  obtain ⟨s, hs⟩ := P.lift _ hker
  refine ⟨s, ?_, ?_⟩
  · apply strict hnf approx n P.i P.i_rad P.i_perturbation s
    rw [hs]
    exact sub_mem hw (mem_Ipow_of_succ hw')
  · rw [hs]
    simpa using hw'

/-- The lowest degree (Prop 2.6(1)): `w ≫ p ∈ I²` implies `w ∈ I`. -/
theorem layer_exact_zero {W : C} (w : W ⟶ P.E)
    (hwp : w ≫ P.p ∈ (Ipow 2 : HomIdeal C).hom W Y) :
    w ∈ (Ipow 1 : HomIdeal C).hom W P.E := by
  obtain ⟨w', hw', hw'p⟩ := P.exists_lift_of_mem (n := 1) hwp
  have hker : (w - w') ≫ P.p = 0 := by rw [Preadditive.sub_comp, hw'p, sub_self]
  obtain ⟨s, hs⟩ := P.lift _ hker
  have hsi : s ≫ P.i ∈ (Ipow 1 : HomIdeal C).hom W P.E :=
    (mem_Ipow_one_iff _).2 (isRadicalMorphism_precomp _ P.i_rad)
  have : w = s ≫ P.i + w' := by rw [hs]; abel
  rw [this]
  exact add_mem hsi hw'

end RightRadicalApprox

end MultiplicativeBasisDeformations.StrictLayers
