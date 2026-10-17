import MultiplicativeBasisDeformations.Foundations.StrictLayers
import MBDVendor.QSE.CategoryTheory.IyamaKrullSchmidtNormalForm
import MBDVendor.Magnitude.CategoryTheory.RadicalMinimality
import MBDVendor.QSE.RepresentationTheory.AlmostSplitCofinite

/-!
# The Krull–Schmidt split–radical normal form

Proof of Lemma 2.5, "Split off the invertible blocks of `u` by Krull–Schmidt decomposition and
elementary row and column operations" (`graded-category.tex`), in any preadditive category
with finite biproducts whose objects are finite biproducts of nonzero objects with local
endomorphism rings (`hasSplitRadicalNormalForm_of_decomp`). The argument is the vendored one for
finite `τ`-categories (`MBDVendor.QSE.Iyama.splitRadicalForm_finBiproduct`), with the finite
skeleton replaced by this decomposition hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE.CategoricalRadical MBDVendor.QSE.Iyama
open scoped ZeroObject

namespace MultiplicativeBasisDeformations.StrictLayers

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C]

/-- A split–radical form of a map `k : X → M`. -/
structure SRF {X M : C} (k : X ⟶ M) where
  Z : C
  U : C
  e : X ≅ biprod Z U
  j : Z ⟶ M
  r : U ⟶ M
  s : M ⟶ Z
  j_s : j ≫ s = 𝟙 Z
  r_s : r ≫ s = 0
  r_rad : IsRadicalMorphism r
  map_eq : e.inv ≫ k = biprod.desc j r

/-- Transport along an isomorphism of sources. -/
def SRF.precomposeIso {X Y M : C} {q : Y ⟶ M} (h : SRF q) (e₀ : X ≅ Y) (k : X ⟶ M)
    (hk : e₀.inv ≫ k = q) : SRF k where
  Z := h.Z
  U := h.U
  e := e₀.trans h.e
  j := h.j
  r := h.r
  s := h.s
  j_s := h.j_s
  r_s := h.r_s
  r_rad := h.r_rad
  map_eq := by rw [Iso.trans_inv, Category.assoc, hk, h.map_eq]

theorem rad_desc {U V M : C} {a : U ⟶ M} {r : V ⟶ M} (ha : IsRadicalMorphism a)
    (hr : IsRadicalMorphism r) : IsRadicalMorphism (biprod.desc a r) := by
  rw [show biprod.desc a r = biprod.fst ≫ a + biprod.snd ≫ r by apply biprod.hom_ext' <;> simp]
  exact isRadicalMorphism_add (isRadicalMorphism_precomp _ ha) (isRadicalMorphism_precomp _ hr)

/-- **Adding one local summand** to a split–radical form. -/
def srf_biprod_local (P : C) [IsLocalRing (End P)] (hP : ¬ IsZero P) {Q M : C} (f : P ⟶ M)
    (q : Q ⟶ M) (hq : SRF q) : SRF (biprod.desc f q) := by
  let Z := hq.Z
  let U := hq.U
  let j := hq.j
  let r := hq.r
  let s := hq.s
  let eBase : biprod P Q ≅ biprod Z (biprod P U) := moveLeftPastFirstIso hq.e
  have hBase : eBase.inv ≫ biprod.desc f q = biprod.desc j (biprod.desc f r) :=
    moveLeftPastFirstIso_inv_desc hq.e f q j r hq.map_eq
  let c₁ : biprod P U ⟶ Z := biprod.desc (-(f ≫ s)) 0
  let a : P ⟶ M := -(f ≫ s) ≫ j + f
  have ha_s : a ≫ s = 0 := by
    dsimp only [a]
    rw [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc, hq.j_s, Category.comp_id,
      neg_add_cancel]
  have hc₁ : c₁ ≫ j + biprod.desc f r = biprod.desc a r := by
    apply biprod.hom_ext'
    · simp [c₁, a, Category.assoc]
    · simp [c₁]
  let e₁ : biprod P Q ≅ biprod Z (biprod P U) := eBase.trans (biprodShear c₁).symm
  have he₁ : e₁.inv ≫ biprod.desc f q = biprod.desc j (biprod.desc a r) := by
    dsimp only [e₁]
    rw [Iso.trans_inv, Iso.symm_inv, Category.assoc, hBase, biprodShear_hom_desc, hc₁]
  by_cases ha : IsRadicalMorphism a
  · refine
      { Z := Z
        U := biprod P U
        e := e₁
        j := j
        r := biprod.desc a r
        s := s
        j_s := hq.j_s
        r_s := ?_
        r_rad := rad_desc ha hq.r_rad
        map_eq := he₁ }
    apply biprod.hom_ext'
    · simpa [Category.assoc] using ha_s
    · simpa [Category.assoc] using hq.r_s
  · have hsplit : IsSplitMono a := by
      apply Classical.not_not.mp
      intro hnot
      exact ha ((MBDVendor.Magnitude.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
        hP a).2 hnot)
    letI : IsSplitMono a := hsplit
    let t : M ⟶ P := retraction a
    let t' : M ⟶ P := t - s ≫ j ≫ t
    have hj_t' : j ≫ t' = 0 := by
      dsimp only [t']
      rw [Preadditive.comp_sub]
      calc j ≫ t - j ≫ (s ≫ j ≫ t) = j ≫ t - (j ≫ s) ≫ j ≫ t := by simp only [Category.assoc]
        _ = 0 := by rw [hq.j_s, Category.id_comp, sub_self]
    have ha_t' : a ≫ t' = 𝟙 P := by
      dsimp only [t']
      rw [Preadditive.comp_sub]
      calc a ≫ t - a ≫ (s ≫ j ≫ t) = a ≫ t - (a ≫ s) ≫ j ≫ t := by simp only [Category.assoc]
        _ = a ≫ t := by rw [ha_s, zero_comp, sub_zero]
        _ = 𝟙 P := IsSplitMono.id a
    let j' : biprod Z P ⟶ M := biprod.desc j a
    let s' : M ⟶ biprod Z P := biprod.lift s t'
    have hj'_s' : j' ≫ s' = 𝟙 _ := by
      apply biprod.hom_ext'
      · apply biprod.hom_ext
        · simpa [j', s', Category.assoc] using hq.j_s
        · simpa [j', s', Category.assoc] using hj_t'
      · apply biprod.hom_ext
        · simpa [j', s', Category.assoc] using ha_s
        · simpa [j', s', Category.assoc] using ha_t'
    let c₂ : U ⟶ biprod Z P := -(r ≫ s')
    let r' : U ⟶ M := c₂ ≫ j' + r
    have hr'_s' : r' ≫ s' = 0 := by
      dsimp only [r', c₂]
      rw [Preadditive.add_comp, Category.assoc, hj'_s', Category.comp_id, neg_add_cancel]
    let eAssoc : biprod P Q ≅ biprod (biprod Z P) U := e₁.trans (biprod.associator Z P U).symm
    have heAssoc : eAssoc.inv ≫ biprod.desc f q = biprod.desc j' r := by
      dsimp only [eAssoc]
      rw [Iso.trans_inv, Iso.symm_inv, Category.assoc, he₁]
      exact associator_hom_desc_desc j a r
    let e₂ : biprod P Q ≅ biprod (biprod Z P) U := eAssoc.trans (biprodShear c₂).symm
    have he₂ : e₂.inv ≫ biprod.desc f q = biprod.desc j' r' := by
      dsimp only [e₂]
      rw [Iso.trans_inv, Iso.symm_inv, Category.assoc, heAssoc, biprodShear_hom_desc]
    refine
      { Z := biprod Z P
        U := U
        e := e₂
        j := j'
        r := r'
        s := s'
        j_s := hj'_s'
        r_s := hr'_s'
        r_rad := ?_
        map_eq := he₂ }
    have h := isRadicalMorphism_add (isRadicalMorphism_postcomp j' (isRadicalMorphism_postcomp s'
      (isRadicalMorphism_neg hq.r_rad))) hq.r_rad
    have e : r' = ((-r) ≫ s') ≫ j' + r := by
      simp only [r', c₂, Preadditive.neg_comp]
    rw [e]; exact h

/-- **Split–radical form** on a finite biproduct of local objects. -/
def srf_fin : ∀ (n : ℕ) (F : Fin n → C), (∀ i, ¬ IsZero (F i) ∧ IsLocalRing (End (F i))) →
    ∀ (M : C) (k : (⨁ F) ⟶ M), SRF k := by
  intro n
  induction n with
  | zero =>
      intro F _ M k
      have hk : k = 0 := by
        apply biproduct.hom_ext'
        intro i
        exact Fin.elim0 i
      exact
        { Z := 0
          U := ⨁ F
          e := isoZeroBiprod (isZero_zero C)
          j := 0
          r := k
          s := 0
          j_s := (isZero_zero C).eq_of_src _ _
          r_s := by simp
          r_rad := by rw [hk]; exact isRadicalMorphism_zero
          map_eq := by rw [hk]; apply biprod.hom_ext' <;> simp }
  | succ n ih =>
      intro F hF M k
      let eCons : (⨁ F) ≅ biprod (F 0) (⨁ fun i : Fin n ↦ F i.succ) := finBiproductConsIso F
      let k' : biprod (F 0) (⨁ fun i : Fin n ↦ F i.succ) ⟶ M := eCons.inv ≫ k
      let f : F 0 ⟶ M := biprod.inl ≫ k'
      let q : (⨁ fun i : Fin n ↦ F i.succ) ⟶ M := biprod.inr ≫ k'
      let hq : SRF q := ih (fun i ↦ F i.succ) (fun i ↦ hF i.succ) M q
      haveI := (hF 0).2
      let h' : SRF (biprod.desc f q) := srf_biprod_local (F 0) (hF 0).1 f q hq
      have hk' : eCons.inv ≫ k = biprod.desc f q := by
        change k' = biprod.desc f q
        symm
        apply biprod.hom_ext'
        · simp [f]
        · simp [q]
      exact h'.precomposeIso eCons k hk'

/-- **The Krull–Schmidt split–radical normal form** in a category whose objects are finite
biproducts of nonzero objects with local endomorphism rings. -/
theorem hasSplitRadicalNormalForm_of_decomp
    (hdec : ∀ X : C, ∃ (n : ℕ) (F : Fin n → C),
      (∀ i, ¬ IsZero (F i) ∧ IsLocalRing (End (F i))) ∧ Nonempty (X ≅ ⨁ F)) :
    HasSplitRadicalNormalForm C := by
  intro X M k
  obtain ⟨n, F, hF, ⟨eX⟩⟩ := hdec X
  let h := (srf_fin n F hF M (eX.inv ≫ k)).precomposeIso eX k rfl
  exact ⟨h.Z, h.U, h.e, h.j, h.r, IsSplitMono.mk' { retraction := h.s, id := h.j_s }, h.r_rad,
    h.map_eq⟩

/-! ### Right radical approximations from almost split maps -/

section Approx

open MBDVendor.QSE.CategoricalIdeal MBDVendor.Magnitude.CategoryTheory

theorem rad_finsum {X Y : C} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y))
    (h : ∀ i ∈ s, IsRadicalMorphism (f i)) : IsRadicalMorphism (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isRadicalMorphism_zero
  | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact isRadicalMorphism_add (h j (Finset.mem_insert_self _ _))
        (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

theorem rad_map {n : ℕ} {A B : Fin n → C} (f : ∀ j, A j ⟶ B j)
    (h : ∀ j, IsRadicalMorphism (f j)) : IsRadicalMorphism (biproduct.map f) := by
  have e : biproduct.map f = ∑ j, biproduct.π A j ≫ f j ≫ biproduct.ι B j := by
    apply biproduct.hom_ext'; intro k
    rw [biproduct.ι_map, Preadditive.comp_sum, Finset.sum_eq_single k]
    · rw [biproduct.ι_π_self_assoc]
    · intro l _ hlk; rw [← Category.assoc, biproduct.ι_π_ne _ (Ne.symm hlk), zero_comp]
    · simp
  rw [e]
  exact rad_finsum _ _ fun j _ ↦ isRadicalMorphism_precomp _ (isRadicalMorphism_postcomp _ (h j))

theorem rad_descB {n : ℕ} {A : Fin n → C} {Z : C} (f : ∀ j, A j ⟶ Z)
    (h : ∀ j, IsRadicalMorphism (f j)) : IsRadicalMorphism (biproduct.desc f) := by
  have e : biproduct.desc f = ∑ j, biproduct.π A j ≫ f j := by
    apply biproduct.hom_ext'; intro k
    rw [biproduct.ι_desc, Preadditive.comp_sum, Finset.sum_eq_single k]
    · rw [biproduct.ι_π_self_assoc]
    · intro l _ hlk; rw [← Category.assoc, biproduct.ι_π_ne _ (Ne.symm hlk), zero_comp]
    · simp
  rw [e]
  exact rad_finsum _ _ fun j _ ↦ isRadicalMorphism_precomp _ (h j)

/-- `sq` from the factorization of radical maps out of `T` through `i`. -/
theorem sq_of_factor {T E : C} (i : T ⟶ E)
    (hfac : ∀ {M : C} (u : T ⟶ M), IsRadicalMorphism u → ∃ b : E ⟶ M, i ≫ b = u)
    {Z : C} (g : T ⟶ Z) (hg : g ∈ (Ipow 2 : HomIdeal C).hom T Z) :
    ∃ q : E ⟶ Z, IsRadicalMorphism q ∧ i ≫ q = g := by
  rw [Ipow, HomIdeal.pow_succ] at hg
  induction hg using AddSubgroup.closure_induction with
  | mem h hh =>
      obtain ⟨M, u, v, hu, hv, rfl⟩ := hh
      rw [HomIdeal.pow_one, mem_homIdeal_iff] at hu
      obtain ⟨b, hb⟩ := hfac u hu
      exact ⟨b ≫ v, isRadicalMorphism_precomp b ((mem_homIdeal_iff v).1 hv),
        by rw [← Category.assoc, hb]⟩
  | zero => exact ⟨0, isRadicalMorphism_zero, by simp⟩
  | add a b _ _ ha hb =>
      obtain ⟨q₁, hq₁, rfl⟩ := ha
      obtain ⟨q₂, hq₂, rfl⟩ := hb
      exact ⟨q₁ + q₂, isRadicalMorphism_add hq₁ hq₂, by rw [Preadditive.comp_add]⟩
  | neg a _ ha =>
      obtain ⟨q, hq, rfl⟩ := ha
      exact ⟨-q, isRadicalMorphism_neg hq, by rw [Preadditive.comp_neg]⟩

/-- **Auslander–Reiten data at an indecomposable** (ordinary Auslander–Reiten theory, assumed by
the manuscript, `main.tex`): a right almost split map `p : E → Y` with kernel `i : T → E`,
where `T = 0` (projective `Y`, `p : rad P → P`) or `i` is left almost split from an
indecomposable `T` (the almost split sequence). -/
structure ARData (Y : C) where
  E : C
  T : C
  p : E ⟶ Y
  i : T ⟶ E
  ras : IsRightAlmostSplit p
  i_p : i ≫ p = 0
  lift : ∀ {W : C} (w : W ⟶ E), w ≫ p = 0 → ∃ s : W ⟶ T, s ≫ i = w
  mono : Mono i
  left : IsZero T ∨ (¬ IsZero T ∧ IsLocalRing (End T) ∧ IsLeftAlmostSplit i)

/-- A right radical approximation in which every radical map out of `T` factors through `i`. -/
structure Approx (Y : C) where
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
  fac : ∀ {M : C} (u : T ⟶ M), IsRadicalMorphism u → ∃ b : E ⟶ M, i ≫ b = u

/-- The right radical approximation. -/
def Approx.toRRA {Y : C} (P : Approx Y) : RightRadicalApprox Y where
  E := P.E
  p := P.p
  T := P.T
  i := P.i
  p_rad := P.p_rad
  factors := P.factors
  i_p := P.i_p
  lift := P.lift
  i_mono := P.i_mono
  i_rad := P.i_rad
  sq g hg := sq_of_factor P.i P.fac g hg

/-- The approximation of an indecomposable, from its Auslander–Reiten data. -/
def approxLocal {Y : C} [IsLocalRing (End Y)] (hY : ¬ IsZero Y) (D : ARData Y) : Approx Y where
  E := D.E
  p := D.p
  T := D.T
  i := D.i
  p_rad := (isRadicalMorphism_iff_not_isSplitEpi_of_local_end hY D.p).2 D.ras.not_isSplitEpi
  factors g hg := D.ras.factors g ((isRadicalMorphism_iff_not_isSplitEpi_of_local_end hY g).1 hg)
  i_p := D.i_p
  lift w hw := D.lift w hw
  i_mono := D.mono
  i_rad := by
    rcases D.left with h0 | ⟨hT, hloc, hl⟩
    · rw [h0.eq_of_src D.i 0]; exact isRadicalMorphism_zero
    · haveI := hloc
      exact (isRadicalMorphism_iff_not_isSplitMono_of_local_end hT D.i).2 hl.not_isSplitMono
  fac {M} u hu := by
    rcases D.left with h0 | ⟨hT, hloc, hl⟩
    · exact ⟨0, by rw [h0.eq_of_src u 0, h0.eq_of_src (D.i ≫ 0) 0]⟩
    · haveI := hloc
      exact hl.factors u ((isRadicalMorphism_iff_not_isSplitMono_of_local_end hT u).1 hu)

/-- **Approximations of a finite biproduct**: the sum of the approximations of the summands. -/
def approxBiproduct {n : ℕ} (F : Fin n → C) (P : ∀ j, Approx (F j)) : Approx (⨁ F) where
  E := ⨁ fun j ↦ (P j).E
  p := biproduct.map fun j ↦ (P j).p
  T := ⨁ fun j ↦ (P j).T
  i := biproduct.map fun j ↦ (P j).i
  p_rad := rad_map _ fun j ↦ (P j).p_rad
  factors {W} g hg := by
    choose g' hg' using fun j ↦ (P j).factors (g ≫ biproduct.π F j) (isRadicalMorphism_postcomp _ hg)
    refine ⟨biproduct.lift g', ?_⟩
    apply biproduct.hom_ext; intro j
    rw [Category.assoc, biproduct.map_π, biproduct.lift_π_assoc, hg']
  i_p := by
    apply biproduct.hom_ext; intro j
    rw [Category.assoc, biproduct.map_π, biproduct.map_π_assoc, (P j).i_p, comp_zero, zero_comp]
  lift {W} w hw := by
    have hj : ∀ j, (w ≫ biproduct.π _ j) ≫ (P j).p = 0 := fun j ↦ by
      rw [Category.assoc, ← biproduct.map_π (fun j ↦ (P j).p) j, ← Category.assoc, hw, zero_comp]
    choose s hs using fun j ↦ (P j).lift _ (hj j)
    refine ⟨biproduct.lift s, ?_⟩
    apply biproduct.hom_ext; intro j
    rw [Category.assoc, biproduct.map_π, biproduct.lift_π_assoc, hs]
  i_mono := by
    constructor
    intro W a b hab
    apply biproduct.hom_ext; intro j
    have h1 := congrArg (· ≫ biproduct.π _ j) hab
    simp only [Category.assoc, biproduct.map_π] at h1
    haveI := (P j).i_mono
    exact (cancel_mono (P j).i).1 (by simpa only [Category.assoc] using h1)
  i_rad := rad_map _ fun j ↦ (P j).i_rad
  fac {M} u hu := by
    choose b hb using fun j ↦ (P j).fac (biproduct.ι (fun j ↦ (P j).T) j ≫ u)
      (isRadicalMorphism_precomp _ hu)
    refine ⟨biproduct.desc b, ?_⟩
    apply biproduct.hom_ext'; intro j
    rw [biproduct.ι_map_assoc, biproduct.ι_desc, hb]

/-- Approximations transport along isomorphisms. -/
def Approx.ofIso {Y Y' : C} (P : Approx Y) (e : Y ≅ Y') : Approx Y' where
  E := P.E
  p := P.p ≫ e.hom
  T := P.T
  i := P.i
  p_rad := isRadicalMorphism_postcomp _ P.p_rad
  factors {W} g hg := by
    obtain ⟨g', hg'⟩ := P.factors (g ≫ e.inv) (isRadicalMorphism_postcomp _ hg)
    exact ⟨g', by rw [← Category.assoc, hg', Category.assoc, e.inv_hom_id, Category.comp_id]⟩
  i_p := by rw [← Category.assoc, P.i_p, zero_comp]
  lift {W} w hw := P.lift w (by
    rw [← cancel_mono e.hom, Category.assoc, hw, zero_comp])
  i_mono := P.i_mono
  i_rad := P.i_rad
  fac := P.fac

/-- **Lemma 2.5, last sentence**: every finite direct sum of left almost split inclusions out of
indecomposables (nonzero, local endomorphism ring) satisfies the perturbation hypothesis: `a + h` is
monic for every `h ∈ J²`. -/
theorem perturbation_biproduct_leftAlmostSplit {n : ℕ} {T E : Fin n → C} (i : ∀ j, T j ⟶ E j)
    [hmono : ∀ j, Mono (i j)] (hT : ∀ j, ¬ IsZero (T j) ∧ IsLocalRing (End (T j)))
    (hi : ∀ j, IsLeftAlmostSplit (i j)) :
    ∀ h ∈ (Ipow 2 : HomIdeal C).hom (⨁ T) (⨁ E), Mono (biproduct.map i + h) := by
  haveI : Mono (biproduct.map i) := by
    constructor
    intro W a b hab
    apply biproduct.hom_ext; intro j
    have h1 := congrArg (· ≫ biproduct.π _ j) hab
    simp only [Category.assoc, biproduct.map_π] at h1
    exact (cancel_mono (i j)).1 (by simpa only [Category.assoc] using h1)
  refine perturbation_of_factor _ fun g hg ↦ sq_of_factor _ (fun {M} u hu ↦ ?_) g hg
  have hb : ∀ j, ∃ b : E j ⟶ M, i j ≫ b = biproduct.ι T j ≫ u := fun j ↦ by
    haveI := (hT j).2
    exact (hi j).factors _ ((isRadicalMorphism_iff_not_isSplitMono_of_local_end (hT j).1 _).1
      (isRadicalMorphism_precomp _ hu))
  choose b hb using hb
  refine ⟨biproduct.desc b, ?_⟩
  apply biproduct.hom_ext'; intro j
  rw [biproduct.ι_map_assoc, biproduct.ι_desc, hb]

end Approx

/-! ### Lemma 2.5 in a Krull–Schmidt category with Auslander–Reiten theory -/

section KS

open MBDVendor.QSE.CategoricalIdeal

variable [HasKernels C]
  (hdec : ∀ X : C, ∃ (n : ℕ) (F : Fin n → C),
    (∀ i, ¬ IsZero (F i) ∧ IsLocalRing (End (F i))) ∧ Nonempty (X ≅ ⨁ F))
  (hAR : ∀ Y : C, ¬ IsZero Y → IsLocalRing (End Y) → Nonempty (ARData Y))

include hdec hAR in
/-- Every object has a right radical approximation. -/
theorem nonempty_approx (X : C) : Nonempty (RightRadicalApprox X) := by
  obtain ⟨n, F, hF, ⟨e⟩⟩ := hdec X
  have P : ∀ j, Approx (F j) := fun j ↦ by
    haveI := (hF j).2
    exact approxLocal (hF j).1 (hAR _ (hF j).1 (hF j).2).some
  exact ⟨((approxBiproduct F P).ofIso e.symm).toRRA⟩

include hdec hAR in
/-- **Lemma 2.5** (`lem:strict-radical-layers`) in a Krull–Schmidt category (objects are finite
biproducts of indecomposables with local endomorphism rings) with Auslander–Reiten theory
(right almost split maps at indecomposables, with kernel zero or left almost split): for a radical
`a : U → Y` with `a + h` monic for all `h ∈ J²(U, Y)`, `z ≫ a ∈ J^{n+1}` implies `z ∈ J^n`. -/
theorem strict_of_AR (n : ℕ) {U Y : C} (a : U ⟶ Y) (ha : IsRadicalMorphism a)
    (hpert : ∀ h ∈ (Ipow 2 : HomIdeal C).hom U Y, Mono (a + h)) {W : C} (z : W ⟶ U)
    (hz : z ≫ a ∈ (Ipow (n + 1) : HomIdeal C).hom W Y) : z ∈ (Ipow n : HomIdeal C).hom W U :=
  strict (hasSplitRadicalNormalForm_of_decomp hdec) (fun Y ↦ (nonempty_approx hdec hAR Y).some)
    n a ha hpert z hz

end KS

end MultiplicativeBasisDeformations.StrictLayers
