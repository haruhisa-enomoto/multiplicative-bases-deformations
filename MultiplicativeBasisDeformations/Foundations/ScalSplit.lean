module

public import MultiplicativeBasisDeformations.Foundations.WeightDivisibility

/-!
# Lemma 4.11(2): restriction of multiplicative weights over a source

`lem:source-basis-extension` (2) (`scalar-normalization.tex`): "Let `Scal(T)` denote the
group of multiplicative `k*`-valued weights on the nonzero morphism lines of `T`, meaning
assignments `d(r)` with `d(rr') = d(r)d(r')` whenever `rr' ≠ 0`. Restriction gives a split
surjection `Scal(T) → Scal(T')`, whose kernel is a product of copies of `k*`, one for each
connected component of `R`."

Here `T = S ∪ {s}` for a source `s` (`NzLine`, `Scal`, `res`). The kernel is identified with the
functions on the connected components of the support poset of `s` (`kerEquiv`): a weight trivial
on `T'` is determined by its values on the new lines `s → y`, which are constant along the
comparabilities. The splitting (`ext`, `res_ext`) is the source's: on each component the new
values are the object values of Lemma 4.9 (`ratio_of_mult`), normalized to one at a chosen root;
the normalization makes them unique, hence multiplicative in the weight.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace Thin

namespace ScalGroup

variable {k : Type u} [Field k] {O : Type v} [Category.{w} O] [Preadditive O] [Linear k O]

/-! ### Lines and weights -/

/-- A nonzero morphism line between objects of `S`. -/
structure NzLine (S : Set O) where
  o : O
  o' : O
  mem : o ∈ S
  mem' : o' ∈ S
  nz : ∃ f : o ⟶ o', f ≠ 0

/-- The line of a nonzero morphism. -/
def mkLine {S : Set O} {o o' : O} (h : o ∈ S) (h' : o' ∈ S) (f : o ⟶ o') (hf : f ≠ 0) : NzLine S :=
  ⟨o, o', h, h', f, hf⟩

theorem NzLine.ext' {S : Set O} {ℓ ℓ' : NzLine S} (h1 : ℓ.o = ℓ'.o) (h2 : ℓ.o' = ℓ'.o') : ℓ = ℓ' := by
  cases ℓ; cases ℓ'; simp only at h1 h2; subst h1 h2; rfl

theorem left_ne {o o' o'' : O} {f : o ⟶ o'} {g : o' ⟶ o''} (h : f ≫ g ≠ 0) : f ≠ 0 :=
  fun h0 ↦ h (by rw [h0, Limits.zero_comp])

theorem right_ne {o o' o'' : O} {f : o ⟶ o'} {g : o' ⟶ o''} (h : f ≫ g ≠ 0) : g ≠ 0 :=
  fun h0 ↦ h (by rw [h0, Limits.comp_zero])

variable (k) in
/-- **`Scal(S)`**: multiplicative `k*`-valued weights on the nonzero lines of `S`. -/
def Scal (S : Set O) : Subgroup (NzLine S → kˣ) where
  carrier := {d | ∀ (o o' o'' : O) (h : o ∈ S) (h' : o' ∈ S) (h'' : o'' ∈ S) (f : o ⟶ o')
    (g : o' ⟶ o'') (hfg : f ≫ g ≠ 0), d (mkLine h h'' (f ≫ g) hfg) =
      d (mkLine h h' f (left_ne hfg)) * d (mkLine h' h'' g (right_ne hfg))}
  mul_mem' {a b} ha hb o o' o'' h h' h'' f g hfg := by
    simp only [Pi.mul_apply, ha o o' o'' h h' h'' f g hfg, hb o o' o'' h h' h'' f g hfg]
    exact mul_mul_mul_comm _ _ _ _
  one_mem' o o' o'' h h' h'' f g hfg := by simp
  inv_mem' {a} ha o o' o'' h h' h'' f g hfg := by
    simp only [Pi.inv_apply, ha o o' o'' h h' h'' f g hfg, mul_inv]

theorem scal_mul {S : Set O} (d : Scal k S) {o o' o'' : O} (h : o ∈ S) (h' : o' ∈ S)
    (h'' : o'' ∈ S) (f : o ⟶ o') (g : o' ⟶ o'') (hfg : f ≫ g ≠ 0) :
    (d : NzLine S → kˣ) (mkLine h h'' (f ≫ g) hfg) =
      (d : NzLine S → kˣ) (mkLine h h' f (left_ne hfg)) * (d : NzLine S → kˣ) (mkLine h' h'' g (right_ne hfg)) :=
  d.2 o o' o'' h h' h'' f g hfg

/-- Lines of a subset are lines of the set. -/
def NzLine.incl {S S' : Set O} (hS : S' ⊆ S) (ℓ : NzLine S') : NzLine S :=
  ⟨ℓ.o, ℓ.o', hS ℓ.mem, hS ℓ.mem', ℓ.nz⟩

variable (k) in
/-- **Restriction** `Scal(S) → Scal(S')`. -/
def res {S S' : Set O} (hS : S' ⊆ S) : Scal k S →* Scal k S' where
  toFun d := ⟨fun ℓ ↦ (d : NzLine S → kˣ) (ℓ.incl hS), fun o o' o'' h h' h'' f g hfg ↦
    d.2 o o' o'' (hS h) (hS h') (hS h'') f g hfg⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem res_apply {S S' : Set O} (hS : S' ⊆ S) (d : Scal k S) (ℓ : NzLine S') :
    ((res k hS d : Scal k S') : NzLine S' → kˣ) ℓ = (d : NzLine S → kˣ) (ℓ.incl hS) := rfl

/-! ### Over a source -/

section Source

open Classical

variable (hT : IsThin k O) (s : O) (S : Finset O) (hsS : s ∉ S)
  (hsrc : ∀ o ∈ S, ∀ f : o ⟶ s, f = 0)

/-- `T = T' ∪ {s}`. -/
abbrev Tset : Set O := insert s (S : Set O)

theorem sub_T : (S : Set O) ⊆ Tset s S := Set.subset_insert _ _

/-- The support poset of the source. -/
abbrev Sp := SupP s (supp s S) (fvec s)

/-- The connected components of the support poset (the components of `R`). -/
def compSetoid : Setoid (Sp s S) := Relation.EqvGen.setoid supLe

/-- The set of components. -/
abbrev Comp := Quotient (compSetoid s S)

theorem supp_sub {y : O} (hy : y ∈ supp s S) : y ∈ S := (Finset.mem_filter.1 hy).1

/-- The new line `s → y`. -/
def newLine (y : Sp s S) : NzLine (Tset s S) :=
  mkLine (Set.mem_insert s _) (Set.mem_insert_of_mem _ (Finset.mem_coe.2 (supp_sub s S y.2)))
    (fvec s y.1) (fvec_ne s S y.2)

include hsS in
theorem ne_s_of_mem {y : O} (hy : y ∈ S) : y ≠ s := fun h ↦ hsS (h ▸ hy)

/-- The values of a weight on the new lines. -/
def onNew (d : Scal k (Tset s S)) (y : Sp s S) : kˣ := (d : NzLine (Tset s S) → kˣ) (newLine s S y)

include hT in
/-- In the kernel, the new values are constant along comparabilities. -/
theorem onNew_le (d : Scal k (Tset s S)) (hd : res k (sub_T s S) d = 1) {a b : Sp s S}
    (hab : supLe a b) : onNew s S d b = onNew s S d a := by
  rcases hab with rfl | ⟨g, hg⟩
  · rfl
  have hm := scal_mul d (Set.mem_insert s _)
    (Set.mem_insert_of_mem _ (Finset.mem_coe.2 (supp_sub s S a.2)))
    (Set.mem_insert_of_mem _ (Finset.mem_coe.2 (supp_sub s S b.2))) (fvec s a.1) g hg
  have h1 : (d : NzLine (Tset s S) → kˣ) (mkLine (Finset.mem_coe.2 (supp_sub s S a.2) |>
      Set.mem_insert_of_mem _) (Set.mem_insert_of_mem _ (Finset.mem_coe.2 (supp_sub s S b.2))) g
      (right_ne hg)) = 1 := by
    have := congrArg (fun e : Scal k (S : Set O) ↦ (e : NzLine (S : Set O) → kˣ)
      (mkLine (Finset.mem_coe.2 (supp_sub s S a.2)) (Finset.mem_coe.2 (supp_sub s S b.2)) g
        (right_ne hg))) hd
    exact this
  rw [h1, mul_one] at hm
  unfold onNew
  rw [show newLine s S b = mkLine _ _ (fvec s a.1 ≫ g) hg from NzLine.ext' rfl rfl, hm]
  rfl

include hT in
/-- The kernel values, on components. -/
def kerToComp (d : (res k (sub_T s S)).ker) : Comp s S → kˣ :=
  Quotient.lift (onNew s S d.1) fun a b hab ↦ by
    induction hab with
    | rel a b h => exact (onNew_le hT s S d.1 d.2 h).symm
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- The weight with prescribed values on the new lines and trivial on `T'`. -/
def dfun (κ : Comp s S → kˣ) (ℓ : NzLine (Tset s S)) : kˣ :=
  if h : ℓ.o = s ∧ ℓ.o' ∈ supp s S then κ ⟦⟨ℓ.o', h.2⟩⟧ else 1

theorem mem_S_of_ne {o : O} (h : o ∈ Tset s S) (hs : o ≠ s) : o ∈ S :=
  Finset.mem_coe.1 ((Set.mem_insert_iff.1 h).resolve_left hs)

theorem dfun_new (κ : Comp s S → kˣ) {y : O} (hy : y ∈ supp s S) (ℓ : NzLine (Tset s S))
    (h1 : ℓ.o = s) (h2 : ℓ.o' = y) : dfun s S κ ℓ = κ ⟦⟨y, hy⟩⟧ := by
  unfold dfun
  rw [dif_pos ⟨h1, h2 ▸ hy⟩]
  congr 2
  exact Subtype.ext h2

theorem dfun_old (κ : Comp s S → kˣ) (ℓ : NzLine (Tset s S)) (h : ¬ (ℓ.o = s ∧ ℓ.o' ∈ supp s S)) :
    dfun s S κ ℓ = 1 := by
  unfold dfun; rw [dif_neg h]

include hT hsS hsrc in
theorem dfun_mem (κ : Comp s S → kˣ) : dfun s S κ ∈ Scal k (Tset s S) := by
  intro o o' o'' h h' h'' f g hfg
  have hsupp : s ∉ supp s S := fun hm ↦ hsS (supp_sub s S hm)
  by_cases ho : o = s
  · by_cases ho' : o' = s
    · rw [dfun_old s S κ (mkLine h h' f _) (fun h ↦ hsupp (ho' ▸ h.2)), one_mul]
      exact congrArg _ (NzLine.ext' (ho.trans ho'.symm) rfl)
    · have ho'S := mem_S_of_ne s S h' ho'
      by_cases ho'' : o'' = s
      · exfalso; subst ho''; exact (right_ne hfg) (hsrc o' ho'S g)
      have ho''S := mem_S_of_ne s S h'' ho''
      have hf : (ho ▸ f : s ⟶ o') ≠ 0 := by subst ho; exact left_ne hfg
      have hfg' : (ho ▸ f : s ⟶ o') ≫ g ≠ 0 := by subst ho; exact hfg
      have hm' : o' ∈ supp s S := Finset.mem_filter.2 ⟨ho'S, _, hf⟩
      have hm'' : o'' ∈ supp s S := Finset.mem_filter.2 ⟨ho''S, _, hfg'⟩
      rw [dfun_new s S κ hm'' _ ho rfl, dfun_new s S κ hm' _ ho rfl,
        dfun_old s S κ (mkLine h' h'' g _) (fun h ↦ ho' h.1), mul_one]
      congr 1
      obtain ⟨c, hc⟩ := exists_smul hT (fvec_ne s S hm') (ho ▸ f)
      have hle : supLe (s := s) (P := supp s S) (fv := fvec s) ⟨o', hm'⟩ ⟨o'', hm''⟩ := by
        right
        refine ⟨g, fun h0 ↦ hfg' ?_⟩
        rw [hc, Linear.smul_comp, h0, smul_zero]
      exact Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hle))
  · have hoS := mem_S_of_ne s S h ho
    have ho' : o' ≠ s := fun e ↦ by subst e; exact left_ne hfg (hsrc o hoS f)
    rw [dfun_old s S κ _ (fun h ↦ ho h.1), dfun_old s S κ _ (fun h ↦ ho h.1),
      dfun_old s S κ _ (fun h ↦ ho' h.1), mul_one]

include hT hsS hsrc in
/-- The kernel element with prescribed values on the components. -/
def compToKer (κ : Comp s S → kˣ) : (res k (sub_T s S)).ker :=
  ⟨⟨dfun s S κ, dfun_mem hT s S hsS hsrc κ⟩, by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    funext ℓ
    change dfun s S κ (ℓ.incl (sub_T s S)) = 1
    rw [dfun, dif_neg]
    rintro ⟨h1, -⟩
    exact ne_s_of_mem s S hsS (Finset.mem_coe.1 ℓ.mem) h1⟩

include hT in
/-- A weight is one on the line of an object to itself. -/
theorem scal_diag {S' : Set O} (d : Scal k S') (ℓ : NzLine S') (h : ℓ.o' = ℓ.o) :
    (d : NzLine S' → kˣ) ℓ = 1 := by
  obtain ⟨f, hf⟩ := ℓ.nz
  have hid : (𝟙 ℓ.o : ℓ.o ⟶ ℓ.o) ≠ 0 := by
    obtain ⟨c, hc⟩ := hT.endo ℓ.o (f ≫ eqToHom h)
    intro h0
    apply hf
    have : f = (f ≫ eqToHom h) ≫ eqToHom h.symm := by simp
    rw [this, hc, h0, smul_zero, Limits.zero_comp]
  have hid2 : (𝟙 ℓ.o ≫ 𝟙 ℓ.o : ℓ.o ⟶ ℓ.o) ≠ 0 := by rwa [Category.comp_id]
  have hm := scal_mul d ℓ.mem ℓ.mem ℓ.mem (𝟙 ℓ.o) (𝟙 ℓ.o) hid2
  have e1 : ℓ = mkLine ℓ.mem ℓ.mem (𝟙 ℓ.o ≫ 𝟙 ℓ.o) hid2 := NzLine.ext' rfl h
  have e2 : mkLine ℓ.mem ℓ.mem (𝟙 ℓ.o) (left_ne hid2) = mkLine ℓ.mem ℓ.mem (𝟙 ℓ.o ≫ 𝟙 ℓ.o) hid2 :=
    NzLine.ext' rfl rfl
  have e3 : mkLine ℓ.mem ℓ.mem (𝟙 ℓ.o) (right_ne hid2) = mkLine ℓ.mem ℓ.mem (𝟙 ℓ.o ≫ 𝟙 ℓ.o) hid2 :=
    NzLine.ext' rfl rfl
  rw [e2] at hm
  try rw [e3] at hm
  rw [e1]
  have := mul_left_cancel (a := (d : NzLine S' → kˣ) (mkLine ℓ.mem ℓ.mem (𝟙 ℓ.o ≫ 𝟙 ℓ.o) hid2))
    (hm.symm.trans (mul_one _).symm)
  exact this

include hT hsS hsrc in
/-- **The kernel of restriction is a product of copies of `k*`, one for each connected component
of the support poset.** -/
def kerEquiv : (res k (sub_T s S)).ker ≃* (Comp s S → kˣ) where
  toFun := kerToComp hT s S
  invFun := compToKer hT s S hsS hsrc
  left_inv d := by
    apply Subtype.ext; apply Subtype.ext
    funext ℓ
    change dfun s S (kerToComp hT s S d) ℓ = (d.1 : NzLine (Tset s S) → kˣ) ℓ
    unfold dfun
    split_ifs with h
    · change onNew s S d.1 _ = _
      exact congrArg _ (NzLine.ext' h.1.symm rfl : newLine s S ⟨ℓ.o', h.2⟩ = ℓ)
    · by_cases hos : ℓ.o = s
      · have ho's : ℓ.o' = s := by
          by_contra hne
          obtain ⟨f, hf⟩ := ℓ.nz
          refine h ⟨hos, Finset.mem_filter.2 ⟨mem_S_of_ne s S ℓ.mem' hne, ?_⟩⟩
          exact ⟨eqToHom hos.symm ≫ f, by simpa using hf⟩
        exact (scal_diag hT d.1 ℓ (ho's.trans hos.symm)).symm
      · have hoS := mem_S_of_ne s S ℓ.mem hos
        have ho' : ℓ.o' ≠ s := by
          intro e
          obtain ⟨f, hf⟩ := ℓ.nz
          exact hf (by have := hsrc ℓ.o hoS (f ≫ eqToHom e); simpa using this)
        have ho'S := mem_S_of_ne s S ℓ.mem' ho'
        have hk := d.2
        rw [MonoidHom.mem_ker] at hk
        have := congrArg (fun e : Scal k (S : Set O) ↦ (e : NzLine (S : Set O) → kˣ)
          ⟨ℓ.o, ℓ.o', Finset.mem_coe.2 hoS, Finset.mem_coe.2 ho'S, ℓ.nz⟩) hk
        exact this.symm
  right_inv κ := by
    funext q
    induction q using Quotient.ind with
    | _ y =>
      change dfun s S κ (newLine s S y) = κ ⟦y⟧
      rw [dfun, dif_pos ⟨rfl, y.2⟩]
      rfl
  map_mul' d e := by
    funext q
    induction q using Quotient.ind with
    | _ y => rfl

/-! ### The splitting -/

/-- The old line `a → b` of a comparability in the support poset. -/
def oldLine (a b : Sp s S) (g : a.1 ⟶ b.1) (hg : g ≠ 0) : NzLine (S : Set O) :=
  mkLine (Finset.mem_coe.2 (supp_sub s S a.2)) (Finset.mem_coe.2 (supp_sub s S b.2)) g hg

/-- **Normalized object values** for a weight `d` on `T'`: they change by `d` along every
comparability, and are one at the chosen root of each component. -/
def IsNormVal (d : Scal k (S : Set O)) (ζ : Sp s S → kˣ) : Prop :=
  (∀ (a b : Sp s S) (g : a.1 ⟶ b.1) (hg : fvec s a.1 ≫ g ≠ 0),
    ζ b = ζ a * (d : NzLine (S : Set O) → kˣ) (oldLine s S a b g (right_ne hg))) ∧
  ∀ q : Comp s S, ζ q.out = 1

include hT in
theorem normVal_unique {d : Scal k (S : Set O)} {ζ ζ' : Sp s S → kˣ} (h : IsNormVal s S d ζ)
    (h' : IsNormVal s S d ζ') : ζ = ζ' := by
  have hinv : ∀ a b : Sp s S, (compSetoid s S) a b → ζ a / ζ' a = ζ b / ζ' b := by
    intro a b hab
    induction hab with
    | rel a b hr =>
        rcases hr with rfl | ⟨g, hg⟩
        · rfl
        rw [h.1 a b g hg, h'.1 a b g hg, mul_div_mul_right_eq_div]
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  funext y
  have hy : (compSetoid s S) y (Quotient.out (⟦y⟧ : Comp s S)) :=
    Quotient.exact (Quotient.out_eq _).symm
  have := hinv _ _ hy
  rw [h.2, h'.2, div_one] at this
  exact div_eq_one.1 this

open Classical in
include hT in
theorem exists_normVal [Infinite k]
    (hrep : SupRepFinite hT (s := s) (P := supp s S) (fv := fvec s) (fun _ hy ↦ fvec_ne s S hy))
    (d : Scal k (S : Set O)) : ∃ ζ, IsNormVal s S d ζ := by
  let _ : PartialOrder (Sp s S) := supOrder hT (fun _ hy ↦ fvec_ne s S hy)
  let _ : LocallyFiniteOrder (Sp s S) := Fintype.toLocallyFiniteOrder
  -- the multiplicative function on comparabilities
  let μ : Sp s S → Sp s S → k := fun a b ↦
    if h : a ≠ b ∧ ∃ g : a.1 ⟶ b.1, fvec s a.1 ≫ g ≠ 0 then
      ((d : NzLine (S : Set O) → kˣ) (oldLine s S a b h.2.choose (right_ne h.2.choose_spec)) : k)
    else 1
  have hμline : ∀ (a b : Sp s S) (g : a.1 ⟶ b.1) (hg : fvec s a.1 ≫ g ≠ 0), a ≠ b →
      μ a b = ((d : NzLine (S : Set O) → kˣ) (oldLine s S a b g (right_ne hg)) : k) := by
    intro a b g hg hne
    simp only [μ]
    rw [dif_pos ⟨hne, g, hg⟩]
    rfl
  have hμ0 : ∀ a b : Sp s S, a ≤ b → μ a b ≠ 0 := by
    intro a b _
    simp only [μ]
    split_ifs
    · exact Units.ne_zero _
    · exact one_ne_zero
  have hμmul : ∀ a b c : Sp s S, a ≤ b → b ≤ c → μ a c = μ a b * μ b c := by
    intro a b c hab hbc
    rcases hab with rfl | ⟨g, hg⟩
    · simp [μ]
    rcases hbc with rfl | ⟨g', hg'⟩
    · simp [μ]
    by_cases hab' : a = b
    · subst hab'; simp [μ]
    by_cases hbc' : b = c
    · subst hbc'; simp [μ]
    have hgg : fvec s a.1 ≫ g ≫ g' ≠ 0 := by
      obtain ⟨c₁, hc₁⟩ := exists_smul hT (fvec_ne s S b.2) (fvec s a.1 ≫ g)
      have hc0 : c₁ ≠ 0 := by rintro rfl; rw [zero_smul] at hc₁; exact hg hc₁
      rw [← Category.assoc, hc₁, Linear.smul_comp]
      exact smul_ne_zero hc0 hg'
    have hac : a ≠ c := by
      rintro rfl
      exact hab' (supLe_antisymm hT (Or.inr ⟨g, hg⟩) (Or.inr ⟨g', hg'⟩))
    rw [hμline a c (g ≫ g') hgg hac, hμline a b g hg hab', hμline b c g' hg' hbc', ← Units.val_mul]
    congr 1
    have := scal_mul d (Finset.mem_coe.2 (supp_sub s S a.2)) (Finset.mem_coe.2 (supp_sub s S b.2))
      (Finset.mem_coe.2 (supp_sub s S c.2)) g g' (right_ne hgg)
    exact this
  obtain ⟨Z, hZ0, hZ⟩ := ratio_of_mult hrep μ hμ0 hμmul
  let av : Sp s S → kˣ := fun y ↦ (Units.mk0 (Z y) (hZ0 y))⁻¹
  refine ⟨fun y ↦ av y / av (Quotient.out (⟦y⟧ : Comp s S)), fun a b g hg ↦ ?_, fun q ↦ ?_⟩
  · have hle : supLe a b := Or.inr ⟨g, hg⟩
    have hq : (⟦a⟧ : Comp s S) = ⟦b⟧ := Quotient.sound (Relation.EqvGen.rel _ _ hle)
    beta_reduce
    rw [hq]
    by_cases hab : a = b
    · subst hab
      rw [scal_diag hT d _ rfl, mul_one]
    · have h1 := hZ a b hle
      rw [hμline a b g hg hab] at h1
      apply Units.ext
      simp only [av, Units.val_div_eq_div_val, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_mk0]
      rw [h1]
      have := hZ0 a; have := hZ0 b
      field_simp
  · beta_reduce
    rw [show (⟦q.out⟧ : Comp s S) = q from Quotient.out_eq q, div_self']

variable [Infinite k]
  (hrep : SupRepFinite hT (s := s) (P := supp s S) (fv := fvec s) (fun _ hy ↦ fvec_ne s S hy))

/-- The chosen normalized object values. -/
def zeta (d : Scal k (S : Set O)) : Sp s S → kˣ := (exists_normVal hT s S hrep d).choose

theorem zeta_spec (d : Scal k (S : Set O)) : IsNormVal s S d (zeta hT s S hrep d) :=
  (exists_normVal hT s S hrep d).choose_spec

theorem zeta_mul (d e : Scal k (S : Set O)) :
    zeta hT s S hrep (d * e) = zeta hT s S hrep d * zeta hT s S hrep e := by
  refine normVal_unique hT s S (zeta_spec hT s S hrep _) ⟨fun a b g hg ↦ ?_, fun q ↦ ?_⟩
  · simp only [Pi.mul_apply, (zeta_spec hT s S hrep d).1 a b g hg,
      (zeta_spec hT s S hrep e).1 a b g hg]
    change _ = _ * ((d : NzLine (S : Set O) → kˣ) _ * (e : NzLine (S : Set O) → kˣ) _)
    exact mul_mul_mul_comm _ _ _ _
  · simp only [Pi.mul_apply, (zeta_spec hT s S hrep d).2 q, (zeta_spec hT s S hrep e).2 q, mul_one]

/-- The extended weight: normalized object values on the new lines. -/
def extFun (d : Scal k (S : Set O)) (ℓ : NzLine (Tset s S)) : kˣ :=
  if h : ℓ.o = s ∧ ℓ.o' ∈ supp s S then zeta hT s S hrep d ⟨ℓ.o', h.2⟩
  else if h' : ℓ.o ∈ S ∧ ℓ.o' ∈ S then
    (d : NzLine (S : Set O) → kˣ) ⟨ℓ.o, ℓ.o', Finset.mem_coe.2 h'.1, Finset.mem_coe.2 h'.2, ℓ.nz⟩
  else 1

theorem extFun_new (d : Scal k (S : Set O)) {y : O} (hy : y ∈ supp s S) (ℓ : NzLine (Tset s S))
    (h1 : ℓ.o = s) (h2 : ℓ.o' = y) : extFun hT s S hrep d ℓ = zeta hT s S hrep d ⟨y, hy⟩ := by
  unfold extFun
  rw [dif_pos ⟨h1, h2 ▸ hy⟩]
  congr 1
  exact Subtype.ext h2

include hsS in
theorem extFun_old (d : Scal k (S : Set O)) (ℓ : NzLine (Tset s S)) (h1 : ℓ.o ∈ S) (h2 : ℓ.o' ∈ S) :
    extFun hT s S hrep d ℓ =
      (d : NzLine (S : Set O) → kˣ) ⟨ℓ.o, ℓ.o', Finset.mem_coe.2 h1, Finset.mem_coe.2 h2, ℓ.nz⟩ := by
  unfold extFun
  rw [dif_neg (fun h ↦ ne_s_of_mem s S hsS h1 h.1), dif_pos ⟨h1, h2⟩]

include hsS in
theorem extFun_ss (d : Scal k (S : Set O)) (ℓ : NzLine (Tset s S)) (h1 : ℓ.o = s) (h2 : ℓ.o' = s) :
    extFun hT s S hrep d ℓ = 1 := by
  unfold extFun
  rw [dif_neg (fun h ↦ hsS (supp_sub s S (by have := h.2; rw [h2] at this; exact this))),
    dif_neg (fun h ↦ hsS (h1 ▸ h.1))]

include hsS hsrc in
theorem extFun_mem (d : Scal k (S : Set O)) : extFun hT s S hrep d ∈ Scal k (Tset s S) := by
  intro o o' o'' h h' h'' f g hfg
  by_cases ho : o = s
  · by_cases ho' : o' = s
    · rw [extFun_ss hT s S hsS hrep d (mkLine h h' f _) ho ho', one_mul]
      exact congrArg _ (NzLine.ext' (ho.trans ho'.symm) rfl)
    · have ho'S := mem_S_of_ne s S h' ho'
      by_cases ho'' : o'' = s
      · exfalso; subst ho''; exact (right_ne hfg) (hsrc o' ho'S g)
      have ho''S := mem_S_of_ne s S h'' ho''
      have hf : (ho ▸ f : s ⟶ o') ≠ 0 := by subst ho; exact left_ne hfg
      have hfg' : (ho ▸ f : s ⟶ o') ≫ g ≠ 0 := by subst ho; exact hfg
      have hm' : o' ∈ supp s S := Finset.mem_filter.2 ⟨ho'S, _, hf⟩
      have hm'' : o'' ∈ supp s S := Finset.mem_filter.2 ⟨ho''S, _, hfg'⟩
      rw [extFun_new hT s S hrep d hm'' _ ho rfl, extFun_new hT s S hrep d hm' _ ho rfl,
        extFun_old hT s S hsS hrep d (mkLine h' h'' g _) ho'S ho''S]
      obtain ⟨c, hc⟩ := exists_smul hT (fvec_ne s S hm') (ho ▸ f)
      have hg : fvec s o' ≫ g ≠ 0 := by
        intro h0
        apply hfg'
        rw [hc, Linear.smul_comp, h0, smul_zero]
      exact (zeta_spec hT s S hrep d).1 ⟨o', hm'⟩ ⟨o'', hm''⟩ g hg
  · have hoS := mem_S_of_ne s S h ho
    have ho' : o' ≠ s := fun e ↦ by subst e; exact left_ne hfg (hsrc o hoS f)
    have ho'' : o'' ≠ s := fun e ↦ by subst e; exact hfg (hsrc o hoS _)
    have ho'S := mem_S_of_ne s S h' ho'
    have ho''S := mem_S_of_ne s S h'' ho''
    rw [extFun_old hT s S hsS hrep d _ hoS ho''S, extFun_old hT s S hsS hrep d _ hoS ho'S,
      extFun_old hT s S hsS hrep d _ ho'S ho''S]
    exact d.2 o o' o'' (Finset.mem_coe.2 hoS) (Finset.mem_coe.2 ho'S) (Finset.mem_coe.2 ho''S)
      f g hfg

include hsS hsrc in
/-- **The splitting** `Scal(T') → Scal(T)`. -/
def ext : Scal k (S : Set O) →* Scal k (Tset s S) where
  toFun d := ⟨extFun hT s S hrep d, extFun_mem hT s S hsS hsrc hrep d⟩
  map_one' := by
    apply Subtype.ext; funext ℓ
    change extFun hT s S hrep 1 ℓ = 1
    have h1 : zeta hT s S hrep 1 = 1 := by
      have := zeta_mul hT s S hrep 1 1
      rw [mul_one] at this
      exact (mul_eq_left.1 this.symm)
    unfold extFun
    split_ifs <;> simp [h1]; rfl
  map_mul' d e := by
    apply Subtype.ext; funext ℓ
    change extFun hT s S hrep (d * e) ℓ = extFun hT s S hrep d ℓ * extFun hT s S hrep e ℓ
    unfold extFun
    split_ifs <;> simp [zeta_mul]; rfl

include hsS hsrc in
theorem res_ext (d : Scal k (S : Set O)) : res k (sub_T s S) (ext hT s S hsS hsrc hrep d) = d := by
  apply Subtype.ext; funext ℓ
  change extFun hT s S hrep d (ℓ.incl (sub_T s S)) = _
  rw [extFun_old hT s S hsS hrep d _ (Finset.mem_coe.1 ℓ.mem) (Finset.mem_coe.1 ℓ.mem')]
  rfl

include hT hrep hsS hsrc in
/-- **Lemma 4.11(2)** (`lem:source-basis-extension`): for a source `s` of `T = T' ∪ {s}`,
restriction `Scal(T) → Scal(T')` is a split surjection, and its kernel is a product of copies of
`k*`, one for each connected component of the support poset of `s` (the components of `R`). -/
theorem sourceScalSplit :
    (∃ e : Scal k (S : Set O) →* Scal k (Tset s S), ∀ d, res k (sub_T s S) (e d) = d) ∧
      Function.Surjective (res k (sub_T s S)) ∧
      Nonempty ((res k (sub_T s S)).ker ≃* (Comp s S → kˣ)) :=
  ⟨⟨ext hT s S hsS hsrc hrep, res_ext hT s S hsS hsrc hrep⟩,
    fun d ↦ ⟨ext hT s S hsS hsrc hrep d, res_ext hT s S hsS hsrc hrep d⟩,
    ⟨kerEquiv hT s S hsS hsrc⟩⟩

end Source

end ScalGroup

end Thin

end MultiplicativeBasisDeformations
