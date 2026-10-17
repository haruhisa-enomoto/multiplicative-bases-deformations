import MultiplicativeBasisDeformations.Foundations.PosetWeights

/-!
# Thin directed categories and the extension of multiplicative bases

Abstract form of Subsection 4.4 (`scalar-normalization.tex`). A
`k`-linear category is *thin* if its Hom spaces have dimension at most one,
its endomorphisms are scalars, and it is directed (no nonzero morphisms both
ways between distinct objects). A *multiplicative basis* on a set of objects
chooses a nonzero vector on each nonzero line, identities on objects, and is
closed under composition up to zero.

Lemma 4.11(1) (`lem:source-basis-extension`): a multiplicative basis on a
finite set extends over a source. The proof is the source's: choose `f_y` in
`T(s, y)`, write `f_y b_{yz} = μ_{yz} f_z`, express `μ` through object values by
Lemma 4.9 on the support poset of Lemma 4.10, and rescale the `f_y`. The
representation-finiteness of the incidence algebra of the support poset is a
hypothesis here; it is supplied by Lemma 4.10 for the graded covering category
(`SupportPoset.lean`). Sinks are sources of the opposite category.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace Thin

variable {k : Type u} [Field k] {O : Type v} [Category.{w} O] [Preadditive O] [Linear k O]

variable (k O) in
/-- A thin directed `k`-linear category. -/
structure IsThin : Prop where
  fin : ∀ o o' : O, FiniteDimensional k (o ⟶ o')
  thin : ∀ o o' : O, Module.finrank k (o ⟶ o') ≤ 1
  endo : ∀ (o : O) (f : o ⟶ o), ∃ c : k, f = c • 𝟙 o
  dir : ∀ (o o' : O), o ≠ o' → ∀ (f : o ⟶ o') (g : o' ⟶ o), f ≠ 0 → g = 0

variable (hT : IsThin k O)

include hT in
/-- Every morphism is a multiple of a nonzero one. -/
theorem exists_smul {o o' : O} {f : o ⟶ o'} (hf : f ≠ 0) (g : o ⟶ o') : ∃ c : k, g = c • f := by
  haveI := hT.fin o o'
  have h1 : Module.finrank k (o ⟶ o') = 1 :=
    le_antisymm (hT.thin o o') (Module.finrank_pos_iff_exists_ne_zero.2 ⟨f, hf⟩)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' f hf).1 h1 g
  exact ⟨c, hc.symm⟩

/-- A multiplicative basis on a set of objects. -/
structure MultBasis (S : Set O) (β : ∀ o o' : O, o ⟶ o') : Prop where
  ne_zero : ∀ o ∈ S, ∀ o' ∈ S, ∀ f : o ⟶ o', f ≠ 0 → β o o' ≠ 0
  id : ∀ o ∈ S, β o o = 𝟙 o
  mul : ∀ o ∈ S, ∀ o' ∈ S, ∀ o'' ∈ S, β o o' ≫ β o' o'' = 0 ∨ β o o' ≫ β o' o'' = β o o''

include hT in
/-- A nonzero composite through basis vectors is the basis vector. -/
theorem MultBasis.comp_eq {S : Set O} {β : ∀ o o' : O, o ⟶ o'} (hβ : MultBasis S β)
    {o o' o'' : O} (h : o ∈ S) (h' : o' ∈ S) (h'' : o'' ∈ S) (hne : β o o' ≫ β o' o'' ≠ 0) :
    β o o' ≫ β o' o'' = β o o'' :=
  (hβ.mul o h o' h' o'' h'').resolve_left hne

/-! ### The support poset of a source -/

section Support

variable (s : O) (P : Finset O) (fv : ∀ y : O, s ⟶ y)

/-- The support poset: `y ≤ z` if some morphism `y → z` acts nonzero on `f_y`. -/
def SupP (_s : O) (P : Finset O) (_fv : ∀ y : O, _s ⟶ y) : Type v := {y : O // y ∈ P}

instance : Fintype (SupP s P fv) := inferInstanceAs (Fintype {y : O // y ∈ P})

open Classical in
instance : DecidableEq (SupP s P fv) := inferInstanceAs (DecidableEq {y : O // y ∈ P})

variable {s P fv}

/-- The order relation. -/
def supLe (y z : SupP s P fv) : Prop := y = z ∨ ∃ g : y.1 ⟶ z.1, fv y.1 ≫ g ≠ 0

variable (hfv : ∀ y ∈ P, fv y ≠ 0)

include hT hfv in
theorem supLe_trans {y z w : SupP s P fv} (h₁ : supLe y z) (h₂ : supLe z w) : supLe y w := by
  rcases h₁ with rfl | ⟨g, hg⟩
  · exact h₂
  rcases h₂ with rfl | ⟨g', hg'⟩
  · exact Or.inr ⟨g, hg⟩
  · right
    obtain ⟨c, hc⟩ := exists_smul hT (hfv z.1 z.2) (fv y.1 ≫ g)
    refine ⟨g ≫ g', ?_⟩
    rw [← Category.assoc, hc, Linear.smul_comp]
    have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc; exact hg hc
    exact smul_ne_zero hc0 hg'

include hT in
theorem supLe_antisymm {y z : SupP s P fv} (h₁ : supLe y z) (h₂ : supLe z y) : y = z := by
  rcases h₁ with h | ⟨g, hg⟩
  · exact h
  rcases h₂ with h | ⟨g', hg'⟩
  · exact h.symm
  by_contra hne
  have hne' : y.1 ≠ z.1 := fun h ↦ hne (Subtype.ext h)
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg
  have := hT.dir y.1 z.1 hne' g g' hg0
  rw [this] at hg'; simp at hg'

/-- The support poset as a partial order. -/
def supOrder : PartialOrder (SupP s P fv) where
  le := supLe
  le_refl y := Or.inl rfl
  le_trans _ _ _ h₁ h₂ := supLe_trans hT hfv h₁ h₂
  le_antisymm _ _ h₁ h₂ := supLe_antisymm hT h₁ h₂

open Classical in
/-- The incidence algebra of the support poset, or of its dual, is
representation-finite (supplied by Lemma 4.10). -/
def SupRepFinite : Prop :=
  letI : PartialOrder (SupP s P fv) := supOrder hT hfv
  letI : LocallyFiniteOrder (SupP s P fv) := Fintype.toLocallyFiniteOrder
  IsRepresentationFinite k (IncidenceAlgebra k (SupP s P fv)) ∨
    IsRepresentationFinite k (IncidenceAlgebra k (SupP s P fv)ᵒᵈ)

end Support

/-! ### Lemma 4.11(1): extension over a source -/

section Extension

open Classical in
/-- The coefficient of `g` along a nonzero `f`. -/
def coef {o o' : O} (f g : o ⟶ o') : k := if h : f ≠ 0 then Classical.choose (exists_smul hT h g) else 0

theorem coef_spec {o o' : O} {f : o ⟶ o'} (hf : f ≠ 0) (g : o ⟶ o') : g = coef hT f g • f := by
  unfold coef
  rw [dif_pos hf]
  exact Classical.choose_spec (exists_smul hT hf g)

theorem coef_eq {o o' : O} {f g : o ⟶ o'} (hf : f ≠ 0) {c : k} (h : g = c • f) :
    coef hT f g = c := by
  have h1 := coef_spec hT hf g
  have h2 : c • f = coef hT f g • f := h.symm.trans h1
  exact (smul_left_injective k hf h2).symm

theorem coef_add {o o' : O} {f : o ⟶ o'} (hf : f ≠ 0) (g g' : o ⟶ o') :
    coef hT f (g + g') = coef hT f g + coef hT f g' := by
  apply coef_eq hT hf
  rw [add_smul, ← coef_spec hT hf, ← coef_spec hT hf]

theorem coef_smul {o o' : O} {f : o ⟶ o'} (hf : f ≠ 0) (c : k) (g : o ⟶ o') :
    coef hT f (c • g) = c * coef hT f g := by
  apply coef_eq hT hf
  rw [mul_smul, ← coef_spec hT hf]

theorem coef_zero {o o' : O} {f : o ⟶ o'} (hf : f ≠ 0) : coef hT f 0 = 0 :=
  coef_eq hT hf (by rw [zero_smul])

theorem coef_self {o o' : O} {f : o ⟶ o'} (hf : f ≠ 0) : coef hT f f = 1 :=
  coef_eq hT hf (by rw [one_smul])

theorem coef_sum {o o' : O} {f : o ⟶ o'} (hf : f ≠ 0) {κ : Type*} (t : Finset κ)
    (g : κ → (o ⟶ o')) : coef hT f (∑ i ∈ t, g i) = ∑ i ∈ t, coef hT f (g i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [coef_zero hT hf]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, coef_add hT hf, ih]

/-- Coefficients multiply along composites. -/
theorem coef_comp {o o' o'' o''' : O} {f : o ⟶ o'} {f' : o ⟶ o''} (hf : f ≠ 0) (hf' : f' ≠ 0)
    (g : o' ⟶ o'') (g' : o'' ⟶ o''') {f'' : o ⟶ o'''} (hf'' : f'' ≠ 0) :
    coef hT f'' (f ≫ g ≫ g') = coef hT f' (f ≫ g) * coef hT f'' (f' ≫ g') := by
  apply coef_eq hT hf''
  generalize hc : coef hT f' (f ≫ g) = c
  generalize hc' : coef hT f'' (f' ≫ g') = c'
  have e1 : f ≫ g = c • f' := hc ▸ coef_spec hT hf' (f ≫ g)
  have e2 : f' ≫ g' = c' • f'' := hc' ▸ coef_spec hT hf'' (f' ≫ g')
  rw [← Category.assoc, e1, Linear.smul_comp, e2, smul_smul]

/-- Coefficients multiply along composites, on the right. -/
theorem coef_comp_right {o o' o'' t : O} {f : o ⟶ t} {f' : o' ⟶ t} {f'' : o'' ⟶ t}
    (hf' : f' ≠ 0) (hf'' : f'' ≠ 0) (g : o'' ⟶ o') (g' : o' ⟶ o) :
    coef hT f'' (g ≫ g' ≫ f) = coef hT f' (g' ≫ f) * coef hT f'' (g ≫ f') := by
  apply coef_eq hT hf''
  generalize hc : coef hT f' (g' ≫ f) = c
  generalize hc' : coef hT f'' (g ≫ f') = c'
  have e1 : g' ≫ f = c • f' := hc ▸ coef_spec hT hf' (g' ≫ f)
  have e2 : g ≫ f' = c' • f'' := hc' ▸ coef_spec hT hf'' (g ≫ f')
  rw [e1, Linear.comp_smul, e2, smul_smul, mul_comm]

variable [Infinite k] (s : O) (S : Finset O) (hsS : s ∉ S) (hsrc : ∀ o ∈ S, ∀ f : o ⟶ s, f = 0)
  (β : ∀ o o' : O, o ⟶ o') (hβ : MultBasis (S : Set O) β)

open Classical in
/-- The support of `T(s, -)` in `S`. -/
def supp : Finset O := S.filter fun y ↦ ∃ f : s ⟶ y, f ≠ 0

open Classical in
/-- Chosen nonzero vectors `f_y ∈ T(s, y)`. -/
def fvec (y : O) : s ⟶ y := if h : ∃ f : s ⟶ y, f ≠ 0 then Classical.choose h else 0

theorem fvec_ne {y : O} (hy : y ∈ supp s S) : fvec s y ≠ 0 := by
  classical
  have h := (Finset.mem_filter.1 hy).2
  unfold fvec; rw [dif_pos h]; exact Classical.choose_spec h

theorem zero_of_not_supp {y : O} (hyS : y ∈ S) (hy : y ∉ supp s S) (f : s ⟶ y) : f = 0 := by
  classical
  by_contra hf
  exact hy (Finset.mem_filter.2 ⟨hyS, f, hf⟩)

include hT hsS hsrc hβ in
/-- **Lemma 4.11(1)** (`lem:source-basis-extension`): a multiplicative basis on
`S` extends over a source `s`. -/
theorem extend_source
    (hrep : SupRepFinite hT (s := s) (P := supp s S) (fv := fvec s) (fun y hy ↦ fvec_ne s S hy)) :
    ∃ β' : ∀ o o' : O, o ⟶ o', MultBasis (insert s (S : Set O)) β' ∧
      ∀ o ∈ S, ∀ o' ∈ S, β' o o' = β o o' := by
  classical
  set P := supp s S with hPdef
  let fv : ∀ y : O, s ⟶ y := fvec s
  have hfv : ∀ y ∈ P, fv y ≠ 0 := fun y hy ↦ fvec_ne s S hy
  have hPS : ∀ y ∈ P, y ∈ S := fun y hy ↦ (Finset.mem_filter.1 hy).1
  letI : PartialOrder (SupP s P fv) := supOrder hT hfv
  letI : LocallyFiniteOrder (SupP s P fv) := Fintype.toLocallyFiniteOrder
  -- the scalars `μ`
  let μ : O → O → k := fun y z ↦ coef hT (fv z) (fv y ≫ β y z)
  have hμ : ∀ y : O, ∀ z ∈ P, fv y ≫ β y z = μ y z • fv z :=
    fun y z hz ↦ coef_spec hT (hfv z hz) _
  have hle : ∀ a b : SupP s P fv, a ≤ b → fv a.1 ≫ β a.1 b.1 ≠ 0 := by
    intro a b hab
    rcases hab with rfl | ⟨g, hg⟩
    · rw [hβ.id _ (hPS _ a.2), Category.comp_id]; exact hfv _ a.2
    · have hg0 : g ≠ 0 := by rintro rfl; simp at hg
      have hb0 := hβ.ne_zero _ (hPS _ a.2) _ (hPS _ b.2) g hg0
      obtain ⟨c, hc⟩ := exists_smul hT hb0 g
      intro h
      rw [hc, Linear.comp_smul, h, smul_zero] at hg
      exact hg rfl
  have hμ0 : ∀ a b : SupP s P fv, a ≤ b → μ a.1 b.1 ≠ 0 := by
    intro a b hab h0
    have := hμ a.1 b.1 b.2
    rw [h0, zero_smul] at this
    exact hle a b hab this
  have hμmul : ∀ a b c : SupP s P fv, a ≤ b → b ≤ c → μ a.1 c.1 = μ a.1 b.1 * μ b.1 c.1 := by
    intro a b c hab hbc
    have hcomp : β a.1 b.1 ≫ β b.1 c.1 ≠ 0 := by
      intro h
      have h1 : fv a.1 ≫ β a.1 b.1 ≫ β b.1 c.1 = (μ a.1 b.1 * μ b.1 c.1) • fv c.1 := by
        rw [← Category.assoc, hμ a.1 b.1 b.2, Linear.smul_comp, hμ b.1 c.1 c.2, smul_smul]
      rw [h, Limits.comp_zero] at h1
      exact smul_ne_zero (mul_ne_zero (hμ0 a b hab) (hμ0 b c hbc)) (hfv _ c.2) h1.symm
    have h1 : fv a.1 ≫ β a.1 b.1 ≫ β b.1 c.1 = (μ a.1 b.1 * μ b.1 c.1) • fv c.1 := by
      rw [← Category.assoc, hμ a.1 b.1 b.2, Linear.smul_comp, hμ b.1 c.1 c.2, smul_smul]
    rw [MultBasis.comp_eq hT hβ (hPS _ a.2) (hPS _ b.2) (hPS _ c.2) hcomp, hμ a.1 c.1 c.2] at h1
    exact smul_left_injective k (hfv _ c.2) h1
  -- Lemma 4.9 on the support poset
  obtain ⟨Z₀, hZ₀, hμZ₀⟩ := ratio_of_mult hrep (fun a b : SupP s P fv ↦ μ a.1 b.1) hμ0 hμmul
  let Z : O → k := fun y ↦ if h : y ∈ P then Z₀ (show SupP s P fv from ⟨y, h⟩) else 1
  have hZ0 : ∀ y, Z y ≠ 0 := by
    intro y; simp only [Z]; split_ifs
    · exact hZ₀ _
    · exact one_ne_zero
  have hμZ : ∀ a b : SupP s P fv, a ≤ b → μ a.1 b.1 = Z a.1 / Z b.1 := by
    intro a b hab
    rw [hμZ₀ a b hab]
    simp only [Z, dif_pos a.2, dif_pos b.2]
    rfl
  let fv' : ∀ y : O, s ⟶ y := fun y ↦ (Z y)⁻¹ • fv y
  have hfv' : ∀ a b : SupP s P fv, a ≤ b → fv' a.1 ≫ β a.1 b.1 = fv' b.1 := by
    intro a b hab
    simp only [fv', Linear.smul_comp]
    rw [hμ a.1 b.1 b.2, smul_smul, hμZ a b hab]
    congr 1
    field_simp [hZ0 a.1, hZ0 b.1]
  have hnle : ∀ a b : SupP s P fv, ¬ a ≤ b → fv a.1 ≫ β a.1 b.1 = 0 := by
    intro a b hab
    by_contra h
    exact hab (Or.inr ⟨β a.1 b.1, h⟩)
  -- the extended basis
  let tail : ∀ o' : O, s ⟶ o' := fun o' ↦
    if ho' : o' = s then eqToHom ho'.symm else if o' ∈ P then fv' o' else 0
  let β' : ∀ o o' : O, o ⟶ o' := fun o o' ↦
    if ho : o = s then eqToHom ho ≫ tail o' else if o' = s then 0 else β o o'
  have hβs : ∀ o', β' s o' = tail o' := fun o' ↦ by simp [β']
  have hβn : ∀ o o', o ≠ s → β' o o' = if o' = s then 0 else β o o' := fun o o' ho ↦ by
    simp [β', ho]
  have htails : tail s = 𝟙 s := by simp [tail]
  have htailP : ∀ y, y ≠ s → y ∈ P → tail y = fv' y := fun y hy hP ↦ by simp [tail, hy, hP]
  have htailN : ∀ y, y ≠ s → y ∉ P → tail y = 0 := fun y hy hP ↦ by simp [tail, hy, hP]
  have hSs : ∀ o ∈ S, o ≠ s := fun o ho h ↦ hsS (h ▸ ho)
  refine ⟨β', ⟨?_, ?_, ?_⟩, fun o ho o' ho' ↦ ?_⟩
  · -- nonzero lines
    intro o ho o' ho' f hf
    rcases ho with ho | ho
    · subst o
      rw [hβs]
      by_cases h' : o' = s
      · subst o'; rw [htails]
        intro h1; apply hf; rw [← Category.comp_id f, h1, Limits.comp_zero]
      · have ho'S : o' ∈ S := by rcases ho' with h | h; exact absurd h h'; exact h
        have hP : o' ∈ P := Finset.mem_filter.2 ⟨ho'S, f, hf⟩
        rw [htailP o' h' hP]
        exact smul_ne_zero (inv_ne_zero (hZ0 o')) (hfv o' hP)
    · rw [hβn o o' (hSs o ho)]
      rcases ho' with ho' | ho'
      · subst o'; exact absurd (hsrc o ho f) hf
      · rw [if_neg (hSs o' ho')]; exact hβ.ne_zero o ho o' ho' f hf
  · intro o ho
    rcases ho with ho | ho
    · subst o; rw [hβs, htails]
    · rw [hβn o o (hSs o ho), if_neg (hSs o ho), hβ.id o ho]
  · intro o ho o' ho' o'' ho''
    by_cases hos : o = s
    · subst o
      rw [hβs, hβs]
      by_cases ho's : o' = s
      · subst o'; rw [htails, Category.id_comp]; exact Or.inr (hβs o'')
      · have ho'S : o' ∈ S := by rcases ho' with h | h; exact absurd h ho's; exact h
        rw [hβn o' o'' ho's]
        by_cases ho''s : o'' = s
        · subst o''; simp
        · have ho''S : o'' ∈ S := by rcases ho'' with h | h; exact absurd h ho''s; exact h
          rw [if_neg ho''s]
          by_cases hP' : o' ∈ P
          · rw [htailP o' ho's hP']
            by_cases hP'' : o'' ∈ P
            · rw [htailP o'' ho''s hP'']
              let a : SupP s P fv := show SupP s P fv from ⟨o', hP'⟩
              let b : SupP s P fv := show SupP s P fv from ⟨o'', hP''⟩
              by_cases hle : a ≤ b
              · exact Or.inr (hfv' a b hle)
              · left
                have h0 : fv o' ≫ β o' o'' = 0 := hnle a b hle
                simp only [fv', Linear.smul_comp]
                rw [h0, smul_zero]
            · rw [htailN o'' ho''s hP'']
              left
              exact zero_of_not_supp s S ho''S hP'' _
          · rw [htailN o' ho's hP', Limits.zero_comp]; exact Or.inl rfl
    · rw [hβn o o' hos]
      by_cases ho's : o' = s
      · rw [if_pos ho's, Limits.zero_comp]; exact Or.inl rfl
      · rw [if_neg ho's, hβn o' o'' ho's, hβn o o'' hos]
        by_cases ho''s : o'' = s
        · rw [if_pos ho''s, if_pos ho''s, Limits.comp_zero]; exact Or.inl rfl
        · rw [if_neg ho''s, if_neg ho''s]
          have hoS : o ∈ S := by rcases ho with h | h; exact absurd h hos; exact h
          have ho'S : o' ∈ S := by rcases ho' with h | h; exact absurd h ho's; exact h
          have ho''S : o'' ∈ S := by rcases ho'' with h | h; exact absurd h ho''s; exact h
          exact hβ.mul o hoS o' ho'S o'' ho''S
  · rw [hβn o o' (hSs o ho), if_neg (hSs o' ho')]

end Extension

end Thin

end MultiplicativeBasisDeformations
