import MultiplicativeBasisDeformations.Foundations.ThinCategory

/-!
# Lemma 4.12: exhaustion by sources and sinks

`lem:cover-exhaustion` (`scalar-normalization.tex`): "There is an
increasing sequence of finite convex full subcategories of `L` with union `L`,
each obtained from the previous one by adding a source or a sink. […]
Consequently `L` has a multiplicative basis."

This file proves the abstract form for a thin directed category with a height
function, finitely many outgoing lines at each object and countably many
objects. Sinks are sources of the opposite category (`extend_sink`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory Opposite

namespace MultiplicativeBasisDeformations

universe u v w

namespace Thin

variable {k : Type u} [Field k] {O : Type v} [Category.{w} O] [Preadditive O] [Linear k O]

/-! ### The opposite category -/

/-- The opposite of a `k`-linear category is `k`-linear. -/
def opLinear : Linear k Oᵒᵖ where
  homModule X Y :=
    { smul := fun c f ↦ (c • f.unop).op
      one_smul := fun f ↦ Quiver.Hom.unop_inj (one_smul k f.unop)
      mul_smul := fun c d f ↦ Quiver.Hom.unop_inj (mul_smul c d f.unop)
      smul_zero := fun c ↦ Quiver.Hom.unop_inj (smul_zero c)
      smul_add := fun c f g ↦ Quiver.Hom.unop_inj (smul_add c f.unop g.unop)
      add_smul := fun c d f ↦ Quiver.Hom.unop_inj (add_smul c d f.unop)
      zero_smul := fun f ↦ Quiver.Hom.unop_inj (zero_smul k f.unop) }
  smul_comp X Y Z r f g := Quiver.Hom.unop_inj (Linear.comp_smul _ _ _ g.unop r f.unop)
  comp_smul X Y Z f r g := Quiver.Hom.unop_inj (Linear.smul_comp _ _ _ r g.unop f.unop)

attribute [local instance] opLinear

theorem unop_smul {X Y : Oᵒᵖ} (c : k) (f : X ⟶ Y) : (c • f).unop = c • f.unop := rfl

/-- `unop` as a linear equivalence. -/
def unopLinearEquiv (X Y : Oᵒᵖ) : (X ⟶ Y) ≃ₗ[k] (unop Y ⟶ unop X) where
  toFun f := f.unop
  invFun g := g.op
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem isThin_op (hT : IsThin k O) : IsThin k Oᵒᵖ where
  fin X Y := by
    haveI := hT.fin (unop Y) (unop X)
    exact LinearEquiv.finiteDimensional (unopLinearEquiv X Y).symm
  thin X Y := by
    haveI := hT.fin (unop Y) (unop X)
    rw [(unopLinearEquiv X Y).finrank_eq]
    exact hT.thin _ _
  endo X f := by
    obtain ⟨c, hc⟩ := hT.endo (unop X) f.unop
    exact ⟨c, Quiver.Hom.unop_inj (by rw [unop_smul]; simpa using hc)⟩
  dir X Y hXY f g hf := Quiver.Hom.unop_inj
    (hT.dir (unop Y) (unop X) (fun h ↦ hXY (unop_injective h.symm)) f.unop g.unop
      (fun h0 ↦ hf (Quiver.Hom.unop_inj h0)))

/-- The opposite of a family of basis vectors. -/
def opβ (β : ∀ o o' : O, o ⟶ o') : ∀ X Y : Oᵒᵖ, X ⟶ Y := fun X Y ↦ (β (unop Y) (unop X)).op

theorem multBasis_op {S : Set O} {β : ∀ o o' : O, o ⟶ o'} (hβ : MultBasis S β) :
    MultBasis (unop ⁻¹' S) (opβ β) where
  ne_zero X hX Y hY f hf h := hβ.ne_zero _ hY _ hX f.unop (fun h0 ↦ hf (Quiver.Hom.unop_inj h0))
    (Quiver.Hom.op_inj h)
  id X hX := Quiver.Hom.unop_inj (hβ.id _ hX)
  mul X hX Y hY Z hZ := by
    rcases hβ.mul _ hZ _ hY _ hX with h | h
    · left; exact Quiver.Hom.unop_inj h
    · right; exact Quiver.Hom.unop_inj h

theorem multBasis_unop {S : Set O} {β : ∀ X Y : Oᵒᵖ, X ⟶ Y}
    (hβ : MultBasis (unop ⁻¹' S) β) :
    MultBasis S (fun o o' ↦ (β (op o') (op o)).unop) where
  ne_zero o ho o' ho' f hf h := hβ.ne_zero (op o') ho' (op o) ho f.op
    (fun h0 ↦ hf (Quiver.Hom.op_inj h0)) (Quiver.Hom.unop_inj h)
  id o ho := by
    have := hβ.id (op o) ho
    rw [this]; rfl
  mul o ho o' ho' o'' ho'' := by
    rcases hβ.mul (op o'') ho'' (op o') ho' (op o) ho with h | h
    · left; exact Quiver.Hom.op_inj h
    · right; exact Quiver.Hom.op_inj h

/-- `op` as an embedding. -/
def opEmb : O ↪ Oᵒᵖ := ⟨op, op_injective⟩

theorem coe_map_op (S : Finset O) : ((S.map opEmb : Finset Oᵒᵖ) : Set Oᵒᵖ) = unop ⁻¹' (S : Set O) := by
  ext X
  simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Set.mem_preimage]
  constructor
  · rintro ⟨o, ho, rfl⟩; exact ho
  · intro h; exact ⟨unop X, h, rfl⟩

variable (hT : IsThin k O)

include hT in
/-- **Lemma 4.11(1) for a sink**: a source of the opposite category. -/
theorem extend_sink [Infinite k] (t : O) (S : Finset O) (htS : t ∉ S)
    (hsnk : ∀ o ∈ S, ∀ f : t ⟶ o, f = 0) (β : ∀ o o' : O, o ⟶ o') (hβ : MultBasis (S : Set O) β)
    (hrep : SupRepFinite (isThin_op hT) (s := op t) (P := supp (op t) (S.map opEmb))
      (fv := fvec (op t)) (fun y hy ↦ fvec_ne (op t) (S.map opEmb) hy)) :
    ∃ β' : ∀ o o' : O, o ⟶ o', MultBasis (insert t (S : Set O)) β' ∧
      ∀ o ∈ S, ∀ o' ∈ S, β' o o' = β o o' := by
  have hT' := isThin_op hT
  have hβ' : MultBasis ((S.map opEmb : Finset Oᵒᵖ) : Set Oᵒᵖ) (opβ β) := by
    rw [coe_map_op]; exact multBasis_op hβ
  have htS' : op t ∉ S.map opEmb := by
    intro h; rw [Finset.mem_map] at h
    obtain ⟨o, ho, ho'⟩ := h
    exact htS (op_injective ho' ▸ ho)
  have hsrc : ∀ X ∈ S.map opEmb, ∀ f : X ⟶ op t, f = 0 := by
    intro X hX f
    rw [Finset.mem_map] at hX
    obtain ⟨o, ho, rfl⟩ := hX
    exact Quiver.Hom.unop_inj (hsnk o ho f.unop)
  obtain ⟨β'', hβ'', hagree⟩ := extend_source hT' (op t) (S.map opEmb) htS' hsrc (opβ β) hβ' hrep
  have hset : (insert (op t) ((S.map opEmb : Finset Oᵒᵖ) : Set Oᵒᵖ)) =
      unop ⁻¹' (insert t (S : Set O)) := by
    rw [coe_map_op]; ext X; simp [Set.mem_insert_iff, unop_eq_iff_eq_op]
  rw [hset] at hβ''
  refine ⟨_, multBasis_unop hβ'', fun o ho o' ho' ↦ ?_⟩
  have := hagree (op o') (Finset.mem_map_of_mem _ ho') (op o) (Finset.mem_map_of_mem _ ho)
  rw [this]; rfl

/-! ### Chains and convex sets -/

section Chains

/-- A nonzero line between distinct objects. -/
def Rl (o o' : O) : Prop := o ≠ o' ∧ ∃ f : o ⟶ o', f ≠ 0

/-- The chain order. -/
def Le (o o' : O) : Prop := Relation.ReflTransGen (Rl) o o'

variable (hgt : O → ℤ) (hR : ∀ o o', Rl o o' → hgt o < hgt o')

include hR in
theorem le_hgt {a b : O} (h : Le a b) : hgt a ≤ hgt b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact ih.trans (hR _ _ hbc).le

include hR in
theorem lt_hgt {a b : O} (h : Le a b) (hne : a ≠ b) : hgt a < hgt b := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hac, hcb⟩
  · exact absurd h hne
  · exact lt_of_lt_of_le (hR _ _ hac) (le_hgt hgt hR hcb)

include hR in
theorem le_antisymm' {a b : O} (h₁ : Le a b) (h₂ : Le b a) : a = b := by
  by_contra hne
  have := lt_hgt hgt hR h₁ hne
  have := le_hgt hgt hR h₂
  omega

/-- A convex set. -/
def Convex (T : Set O) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, ∀ c, Le a c → Le c b → c ∈ T

variable (hsucc : ∀ o : O, {o' | Rl o o'}.Finite)

include hR hsucc in
/-- **Intervals are finite.** -/
theorem interval_finite (b : O) : ∀ (n : ℕ) (a : O), hgt b - hgt a < n →
    {c | Le a c ∧ Le c b}.Finite := by
  intro n
  induction n with
  | zero =>
      intro a ha
      refine Set.Finite.subset Set.finite_empty fun c hc ↦ ?_
      have := (le_hgt hgt hR hc.1).trans (le_hgt hgt hR hc.2)
      push_cast at ha
      omega
  | succ n ih =>
      intro a ha
      have hsub : {c | Le a c ∧ Le c b} ⊆
          {a} ∪ ⋃ a' ∈ {o' | Rl a o'}, {c | Le a' c ∧ Le c b} := by
        rintro c ⟨hac, hcb⟩
        rcases Relation.ReflTransGen.cases_head hac with h | ⟨a', haa', ha'c⟩
        · left; exact h.symm
        · right; exact Set.mem_biUnion haa' ⟨ha'c, hcb⟩
      refine Set.Finite.subset ((Set.finite_singleton a).union ((hsucc a).biUnion fun a' haa' ↦ ?_)) hsub
      by_cases hle : hgt a' ≤ hgt b
      · exact ih a' (by have := hR _ _ haa'; omega)
      · refine Set.Finite.subset (Set.finite_empty) fun c hc ↦ ?_
        exact absurd ((le_hgt hgt hR hc.1).trans (le_hgt hgt hR hc.2)) hle

/-- The convex hull of a finite set. -/
def hull (F : Finset O) : Set O := {c | ∃ a ∈ F, ∃ b ∈ F, Le a c ∧ Le c b}

include hR hsucc in
theorem hull_finite (F : Finset O) : (hull F).Finite := by
  have : hull F = ⋃ a ∈ F, ⋃ b ∈ F, {c | Le a c ∧ Le c b} := by
    ext c
    constructor
    · rintro ⟨a, ha, b, hb, h⟩
      exact Set.mem_biUnion (Finset.mem_coe.2 ha) (Set.mem_biUnion (Finset.mem_coe.2 hb) h)
    · intro h
      simp only [Set.mem_iUnion, exists_prop] at h
      obtain ⟨a, ha, b, hb, h⟩ := h
      exact ⟨a, ha, b, hb, h⟩
  rw [this]
  exact Set.Finite.biUnion F.finite_toSet fun a _ ↦ Set.Finite.biUnion F.finite_toSet fun b _ ↦
    interval_finite hgt hR hsucc b ((hgt b - hgt a).toNat + 1) a (by omega)

theorem hull_convex (F : Finset O) : Convex (hull F) := by
  rintro a ⟨a₀, ha₀, -, -, ha₀a, -⟩ b ⟨-, -, b₀, hb₀, -, hbb₀⟩ c hac hcb
  exact ⟨a₀, ha₀, b₀, hb₀, ha₀a.trans hac, hcb.trans hbb₀⟩

theorem subset_hull (F : Finset O) : (F : Set O) ⊆ hull F := fun a ha ↦
  ⟨a, ha, a, ha, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem hull_mono {F F' : Finset O} (h : F ⊆ F') : hull F ⊆ hull F' := by
  rintro c ⟨a, ha, b, hb, hac, hcb⟩
  exact ⟨a, h ha, b, h hb, hac, hcb⟩

end Chains

/-! ### Choosing the next object -/

section StepObj

variable (hgt : O → ℤ) (hR : ∀ o o', Rl o o' → hgt o < hgt o')

include hR in
/-- **One step, objects only**: a missing object which is a source or a sink for
`T`, keeping convexity. -/
theorem step_obj (T T' : Finset O) (hTT' : T ⊆ T') (hne : T ≠ T') (hT1 : Convex (T : Set O))
    (hT2 : Convex (T' : Set O)) :
    ∃ c ∈ T', c ∉ T ∧ Convex (insert c (T : Set O)) ∧
      ((∀ o ∈ T, ∀ f : o ⟶ c, f = 0) ∨ (∀ o ∈ T, ∀ f : c ⟶ o, f = 0)) := by
  classical
  have hD : (T' \ T).Nonempty := by
    rw [Finset.sdiff_nonempty]; exact fun h ↦ hne (Finset.Subset.antisymm hTT' h)
  by_cases hA : ∃ c ∈ T' \ T, ∃ t ∈ T, Le c t
  · -- a missing object below `T`, of maximal height: a source
    let B := (T' \ T).filter fun c ↦ ∃ t ∈ T, Le c t
    have hBne : B.Nonempty := by
      obtain ⟨c, hc, ht⟩ := hA; exact ⟨c, Finset.mem_filter.2 ⟨hc, ht⟩⟩
    obtain ⟨c, hcB, hmax⟩ := Finset.exists_max_image B hgt hBne
    obtain ⟨hcD, t₀, ht₀, hct₀⟩ := Finset.mem_filter.1 hcB
    obtain ⟨hcT', hcT⟩ := Finset.mem_sdiff.1 hcD
    have hsrc : ∀ o ∈ T, ∀ f : o ⟶ c, f = 0 := by
      intro o ho f
      by_contra hf
      have hoc : o ≠ c := fun h ↦ hcT (h ▸ ho)
      exact hcT (hT1 o ho t₀ ht₀ c (Relation.ReflTransGen.single ⟨hoc, f, hf⟩) hct₀)
    refine ⟨c, hcT', hcT, ?_, Or.inl hsrc⟩
    rintro a (rfl | ha) b (rfl | hb) d had hdb
    · exact Or.inl (le_antisymm' hgt hR had hdb).symm
    · by_cases hdc : d = a
      · exact Or.inl hdc
      · right
        by_contra hdT
        have hdD : d ∈ T' \ T := Finset.mem_sdiff.2 ⟨hT2 a hcT' b (hTT' hb) d had hdb, hdT⟩
        have := hmax d (Finset.mem_filter.2 ⟨hdD, b, hb, hdb⟩)
        have := lt_hgt hgt hR had (Ne.symm hdc)
        omega
    · right; exact hT1 a ha t₀ ht₀ d had (hdb.trans hct₀)
    · right; exact hT1 a ha b hb d had hdb
  by_cases hB : ∃ c ∈ T' \ T, ∃ t ∈ T, Le t c
  · -- a missing object above `T`, of minimal height: a sink
    let B := (T' \ T).filter fun c ↦ ∃ t ∈ T, Le t c
    have hBne : B.Nonempty := by
      obtain ⟨c, hc, ht⟩ := hB; exact ⟨c, Finset.mem_filter.2 ⟨hc, ht⟩⟩
    obtain ⟨c, hcB, hmin⟩ := Finset.exists_min_image B hgt hBne
    obtain ⟨hcD, t₀, ht₀, ht₀c⟩ := Finset.mem_filter.1 hcB
    obtain ⟨hcT', hcT⟩ := Finset.mem_sdiff.1 hcD
    have hsnk : ∀ o ∈ T, ∀ f : c ⟶ o, f = 0 := by
      intro o ho f
      by_contra hf
      have hco : c ≠ o := fun h ↦ hcT (h ▸ ho)
      exact hA ⟨c, hcD, o, ho, Relation.ReflTransGen.single ⟨hco, f, hf⟩⟩
    refine ⟨c, hcT', hcT, ?_, Or.inr hsnk⟩
    rintro a (rfl | ha) b (rfl | hb) d had hdb
    · exact Or.inl (le_antisymm' hgt hR had hdb).symm
    · exact absurd ⟨a, hcD, b, hb, had.trans hdb⟩ hA
    · by_cases hdc : d = b
      · exact Or.inl hdc
      · right
        by_contra hdT
        have hdD : d ∈ T' \ T := Finset.mem_sdiff.2 ⟨hT2 a (hTT' ha) b hcT' d had hdb, hdT⟩
        have := hmin d (Finset.mem_filter.2 ⟨hdD, a, ha, had⟩)
        have := lt_hgt hgt hR hdb hdc
        omega
    · right; exact hT1 a ha b hb d had hdb
  · -- an object incomparable with `T`: a source
    obtain ⟨c, hcD⟩ := hD
    obtain ⟨hcT', hcT⟩ := Finset.mem_sdiff.1 hcD
    have hsrc : ∀ o ∈ T, ∀ f : o ⟶ c, f = 0 := by
      intro o ho f
      by_contra hf
      have hoc : o ≠ c := fun h ↦ hcT (h ▸ ho)
      exact hB ⟨c, hcD, o, ho, Relation.ReflTransGen.single ⟨hoc, f, hf⟩⟩
    refine ⟨c, hcT', hcT, ?_, Or.inl hsrc⟩
    rintro a (rfl | ha) b (rfl | hb) d had hdb
    · exact Or.inl (le_antisymm' hgt hR had hdb).symm
    · exact absurd ⟨a, hcD, b, hb, had.trans hdb⟩ hA
    · exact absurd ⟨b, hcD, a, ha, had.trans hdb⟩ hB
    · right; exact hT1 a ha b hb d had hdb

end StepObj

/-! ### Adding one object at a time -/

section Build

variable [Infinite k] (hT : IsThin k O) (hgt : O → ℤ) (hR : ∀ o o', Rl o o' → hgt o < hgt o')
  (hsrcRep : ∀ (s : O) (S : Finset O), SupRepFinite hT (s := s) (P := supp s S)
    (fv := fvec s) (fun y hy ↦ fvec_ne s S hy))
  (hsnkRep : ∀ (t : O) (S : Finset O), SupRepFinite (isThin_op hT) (s := op t)
    (P := supp (op t) (S.map opEmb)) (fv := fvec (op t)) (fun y hy ↦ fvec_ne (op t) (S.map opEmb) hy))

include hR hsrcRep hsnkRep in
/-- **One step**: add a source, a sink, or an isolated object, keeping convexity
(`scalar-normalization.tex`). -/
theorem step (T T' : Finset O) (hTT' : T ⊆ T') (hne : T ≠ T') (hT1 : Convex (T : Set O))
    (hT2 : Convex (T' : Set O)) (β : ∀ o o' : O, o ⟶ o') (hβ : MultBasis (T : Set O) β) :
    ∃ c ∈ T', c ∉ T ∧ Convex (insert c (T : Set O)) ∧
      ∃ β' : ∀ o o' : O, o ⟶ o', MultBasis (insert c (T : Set O)) β' ∧
        ∀ o ∈ T, ∀ o' ∈ T, β' o o' = β o o' := by
  classical
  have hD : (T' \ T).Nonempty := by
    rw [Finset.sdiff_nonempty]; exact fun h ↦ hne (Finset.Subset.antisymm hTT' h)
  by_cases hA : ∃ c ∈ T' \ T, ∃ t ∈ T, Le c t
  · -- a missing object below `T`, of maximal height: a source
    let B := (T' \ T).filter fun c ↦ ∃ t ∈ T, Le c t
    have hBne : B.Nonempty := by
      obtain ⟨c, hc, ht⟩ := hA; exact ⟨c, Finset.mem_filter.2 ⟨hc, ht⟩⟩
    obtain ⟨c, hcB, hmax⟩ := Finset.exists_max_image B hgt hBne
    obtain ⟨hcD, t₀, ht₀, hct₀⟩ := Finset.mem_filter.1 hcB
    obtain ⟨hcT', hcT⟩ := Finset.mem_sdiff.1 hcD
    have hsrc : ∀ o ∈ T, ∀ f : o ⟶ c, f = 0 := by
      intro o ho f
      by_contra hf
      have hoc : o ≠ c := fun h ↦ hcT (h ▸ ho)
      exact hcT (hT1 o ho t₀ ht₀ c (Relation.ReflTransGen.single ⟨hoc, f, hf⟩) hct₀)
    refine ⟨c, hcT', hcT, ?_, extend_source hT c T hcT hsrc β hβ (hsrcRep c T)⟩
    rintro a (rfl | ha) b (rfl | hb) d had hdb
    · exact Or.inl (le_antisymm' hgt hR had hdb).symm
    · by_cases hdc : d = a
      · exact Or.inl hdc
      · right
        by_contra hdT
        have hdD : d ∈ T' \ T := Finset.mem_sdiff.2 ⟨hT2 a hcT' b (hTT' hb) d had hdb, hdT⟩
        have := hmax d (Finset.mem_filter.2 ⟨hdD, b, hb, hdb⟩)
        have := lt_hgt hgt hR had (Ne.symm hdc)
        omega
    · right; exact hT1 a ha t₀ ht₀ d had (hdb.trans hct₀)
    · right; exact hT1 a ha b hb d had hdb
  by_cases hB : ∃ c ∈ T' \ T, ∃ t ∈ T, Le t c
  · -- a missing object above `T`, of minimal height: a sink
    let B := (T' \ T).filter fun c ↦ ∃ t ∈ T, Le t c
    have hBne : B.Nonempty := by
      obtain ⟨c, hc, ht⟩ := hB; exact ⟨c, Finset.mem_filter.2 ⟨hc, ht⟩⟩
    obtain ⟨c, hcB, hmin⟩ := Finset.exists_min_image B hgt hBne
    obtain ⟨hcD, t₀, ht₀, ht₀c⟩ := Finset.mem_filter.1 hcB
    obtain ⟨hcT', hcT⟩ := Finset.mem_sdiff.1 hcD
    have hsnk : ∀ o ∈ T, ∀ f : c ⟶ o, f = 0 := by
      intro o ho f
      by_contra hf
      have hco : c ≠ o := fun h ↦ hcT (h ▸ ho)
      exact hA ⟨c, hcD, o, ho, Relation.ReflTransGen.single ⟨hco, f, hf⟩⟩
    refine ⟨c, hcT', hcT, ?_, extend_sink hT c T hcT hsnk β hβ (hsnkRep c T)⟩
    rintro a (rfl | ha) b (rfl | hb) d had hdb
    · exact Or.inl (le_antisymm' hgt hR had hdb).symm
    · exact absurd ⟨a, hcD, b, hb, had.trans hdb⟩ hA
    · by_cases hdc : d = b
      · exact Or.inl hdc
      · right
        by_contra hdT
        have hdD : d ∈ T' \ T := Finset.mem_sdiff.2 ⟨hT2 a (hTT' ha) b hcT' d had hdb, hdT⟩
        have := hmin d (Finset.mem_filter.2 ⟨hdD, a, ha, had⟩)
        have := lt_hgt hgt hR hdb hdc
        omega
    · right; exact hT1 a ha b hb d had hdb
  · -- an object incomparable with `T`: a source
    obtain ⟨c, hcD⟩ := hD
    obtain ⟨hcT', hcT⟩ := Finset.mem_sdiff.1 hcD
    have hsrc : ∀ o ∈ T, ∀ f : o ⟶ c, f = 0 := by
      intro o ho f
      by_contra hf
      have hoc : o ≠ c := fun h ↦ hcT (h ▸ ho)
      exact hB ⟨c, hcD, o, ho, Relation.ReflTransGen.single ⟨hoc, f, hf⟩⟩
    refine ⟨c, hcT', hcT, ?_, extend_source hT c T hcT hsrc β hβ (hsrcRep c T)⟩
    rintro a (rfl | ha) b (rfl | hb) d had hdb
    · exact Or.inl (le_antisymm' hgt hR had hdb).symm
    · exact absurd ⟨a, hcD, b, hb, had.trans hdb⟩ hA
    · exact absurd ⟨b, hcD, a, ha, had.trans hdb⟩ hB
    · right; exact hT1 a ha b hb d had hdb

include hR hsrcRep hsnkRep in
/-- Filling a finite convex set from a smaller one. -/
theorem fill [DecidableEq O] : ∀ (n : ℕ) (T T' : Finset O), (T' \ T).card = n → T ⊆ T' →
    Convex (T : Set O) → Convex (T' : Set O) → ∀ β : ∀ o o' : O, o ⟶ o',
      MultBasis (T : Set O) β → ∃ β' : ∀ o o' : O, o ⟶ o', MultBasis (T' : Set O) β' ∧
        ∀ o ∈ T, ∀ o' ∈ T, β' o o' = β o o' := by
  intro n
  induction n with
  | zero =>
      intro T T' hcard hTT' _ _ β hβ
      have : T = T' := Finset.Subset.antisymm hTT' (Finset.sdiff_eq_empty_iff_subset.1
        (Finset.card_eq_zero.1 hcard))
      subst this
      exact ⟨β, hβ, fun _ _ _ _ ↦ rfl⟩
  | succ n ih =>
      intro T T' hcard hTT' hT1 hT2 β hβ
      have hne : T ≠ T' := by rintro rfl; simp at hcard
      obtain ⟨c, hcT', hcT, hconv, β₁, hβ₁, hagree₁⟩ :=
        step hT hgt hR hsrcRep hsnkRep T T' hTT' hne hT1 hT2 β hβ
      have hcard' : (T' \ insert c T).card = n := by
        rw [Finset.sdiff_insert, Finset.card_erase_of_mem (Finset.mem_sdiff.2 ⟨hcT', hcT⟩),
          hcard]
        simp
      obtain ⟨β', hβ', hagree'⟩ := ih (insert c T) T' hcard'
        (Finset.insert_subset hcT' hTT') (by rw [Finset.coe_insert]; exact hconv) hT2 β₁
        (by rw [Finset.coe_insert]; exact hβ₁)
      refine ⟨β', hβ', fun o ho o' ho' ↦ ?_⟩
      rw [hagree' o (Finset.mem_insert_of_mem ho) o' (Finset.mem_insert_of_mem ho'),
        hagree₁ o ho o' ho']

variable (hsucc : ∀ o : O, {o' | Rl o o'}.Finite)

/-- The finite convex sets of the exhaustion. -/
def exT [DecidableEq O] (e : ℕ → O) (n : ℕ) : Finset O :=
  (hull_finite hgt hR hsucc ((Finset.range (n + 1)).image e)).toFinset

theorem coe_exT [DecidableEq O] (e : ℕ → O) (n : ℕ) :
    (exT hgt hR hsucc e n : Set O) = hull ((Finset.range (n + 1)).image e) := by
  simp [exT]

theorem exT_mono [DecidableEq O] (e : ℕ → O) (n : ℕ) :
    exT hgt hR hsucc e n ⊆ exT hgt hR hsucc e (n + 1) := by
  intro x hx
  rw [← Finset.mem_coe, coe_exT] at hx ⊢
  refine hull_mono ?_ hx
  intro y hy
  simp only [Finset.mem_image, Finset.mem_range] at hy ⊢
  obtain ⟨i, hi, rfl⟩ := hy
  exact ⟨i, by omega, rfl⟩

theorem exT_convex [DecidableEq O] (e : ℕ → O) (n : ℕ) : Convex (exT hgt hR hsucc e n : Set O) := by
  rw [coe_exT]; exact hull_convex _

theorem mem_exT [DecidableEq O] (e : ℕ → O) (n : ℕ) : e n ∈ exT hgt hR hsucc e n := by
  rw [← Finset.mem_coe, coe_exT]
  exact subset_hull _ (Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (by omega), rfl⟩))

include hR hsrcRep hsnkRep in
theorem exists_next [DecidableEq O] (e : ℕ → O) (n : ℕ) (β : ∀ o o' : O, o ⟶ o')
    (hβ : MultBasis (exT hgt hR hsucc e n : Set O) β) :
    ∃ β' : ∀ o o' : O, o ⟶ o', MultBasis (exT hgt hR hsucc e (n + 1) : Set O) β' ∧
      ∀ o ∈ exT hgt hR hsucc e n, ∀ o' ∈ exT hgt hR hsucc e n, β' o o' = β o o' :=
  fill hT hgt hR hsrcRep hsnkRep _ _ _ rfl (exT_mono hgt hR hsucc e n) (exT_convex hgt hR hsucc e n)
    (exT_convex hgt hR hsucc e (n + 1)) β hβ

include hR hsrcRep hsnkRep in
theorem exists_first [DecidableEq O] (e : ℕ → O) :
    ∃ β' : ∀ o o' : O, o ⟶ o', MultBasis (exT hgt hR hsucc e 0 : Set O) β' := by
  obtain ⟨β', hβ', -⟩ := fill hT hgt hR hsrcRep hsnkRep _ ∅ _ rfl (Finset.empty_subset _)
    (by intro a ha; simp at ha) (exT_convex hgt hR hsucc e 0) (fun _ _ ↦ 0)
    ⟨fun o ho ↦ by simp at ho, fun o ho ↦ by simp at ho, fun o ho ↦ by simp at ho⟩
  exact ⟨β', hβ'⟩

/-- The sequence of bases. -/
def basSeq [DecidableEq O] (e : ℕ → O) :
    ∀ n : ℕ, {β : ∀ o o' : O, o ⟶ o' // MultBasis (exT hgt hR hsucc e n : Set O) β}
  | 0 => ⟨_, Classical.choose_spec (exists_first hT hgt hR hsrcRep hsnkRep hsucc e)⟩
  | n + 1 => ⟨_, (Classical.choose_spec
      (exists_next hT hgt hR hsrcRep hsnkRep hsucc e n (basSeq e n).1 (basSeq e n).2)).1⟩

theorem basSeq_succ [DecidableEq O] (e : ℕ → O) (n : ℕ) :
    ∀ o ∈ exT hgt hR hsucc e n, ∀ o' ∈ exT hgt hR hsucc e n,
      (basSeq hT hgt hR hsrcRep hsnkRep hsucc e (n + 1)).1 o o' =
        (basSeq hT hgt hR hsrcRep hsnkRep hsucc e n).1 o o' :=
  (Classical.choose_spec (exists_next hT hgt hR hsrcRep hsnkRep hsucc e n
    (basSeq hT hgt hR hsrcRep hsnkRep hsucc e n).1
    (basSeq hT hgt hR hsrcRep hsnkRep hsucc e n).2)).2

theorem exT_mono' [DecidableEq O] (e : ℕ → O) {n m : ℕ} (h : n ≤ m) :
    exT hgt hR hsucc e n ⊆ exT hgt hR hsucc e m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (exT_mono hgt hR hsucc e _)

theorem basSeq_agree [DecidableEq O] (e : ℕ → O) {n m : ℕ} (h : n ≤ m) :
    ∀ o ∈ exT hgt hR hsucc e n, ∀ o' ∈ exT hgt hR hsucc e n,
      (basSeq hT hgt hR hsrcRep hsnkRep hsucc e m).1 o o' =
        (basSeq hT hgt hR hsrcRep hsnkRep hsucc e n).1 o o' := by
  induction h with
  | refl => exact fun _ _ _ _ ↦ rfl
  | step hnm ih =>
      intro o ho o' ho'
      rw [basSeq_succ hT hgt hR hsrcRep hsnkRep hsucc e _ o (exT_mono' hgt hR hsucc e hnm ho)
        o' (exT_mono' hgt hR hsucc e hnm ho'), ih o ho o' ho']

include hR hsrcRep hsnkRep hsucc in
/-- **Lemma 4.12** (`lem:cover-exhaustion`): a thin directed category with a
height, finitely many outgoing lines at each object and countably many objects
has a multiplicative basis. -/
theorem exists_multBasis (e : ℕ → O) (he : Function.Surjective e) :
    ∃ β : ∀ o o' : O, o ⟶ o', MultBasis Set.univ β := by
  classical
  let idx : O → ℕ := fun o ↦ Classical.choose (he o)
  have hidx : ∀ o, e (idx o) = o := fun o ↦ Classical.choose_spec (he o)
  have hmem : ∀ o n, idx o ≤ n → o ∈ exT hgt hR hsucc e n := fun o n h ↦ by
    have := exT_mono' hgt hR hsucc e h (mem_exT hgt hR hsucc e (idx o))
    rwa [hidx] at this
  let B := fun n ↦ (basSeq hT hgt hR hsrcRep hsnkRep hsucc e n)
  refine ⟨fun o o' ↦ (B (max (idx o) (idx o'))).1 o o', ⟨?_, ?_, ?_⟩⟩
  · intro o _ o' _ f hf
    exact (B _).2.ne_zero o (hmem o _ (le_max_left _ _)) o' (hmem o' _ (le_max_right _ _)) f hf
  · intro o _
    exact (B _).2.id o (hmem o _ (le_max_left _ _))
  · intro o _ o' _ o'' _
    let N := max (idx o) (max (idx o') (idx o''))
    have h1 : (B (max (idx o) (idx o'))).1 o o' = (B N).1 o o' :=
      (basSeq_agree hT hgt hR hsrcRep hsnkRep hsucc e (by omega) o
        (hmem o _ (le_max_left _ _)) o' (hmem o' _ (le_max_right _ _))).symm
    have h2 : (B (max (idx o') (idx o''))).1 o' o'' = (B N).1 o' o'' :=
      (basSeq_agree hT hgt hR hsrcRep hsnkRep hsucc e (by omega) o'
        (hmem o' _ (le_max_left _ _)) o'' (hmem o'' _ (le_max_right _ _))).symm
    have h3 : (B (max (idx o) (idx o''))).1 o o'' = (B N).1 o o'' :=
      (basSeq_agree hT hgt hR hsrcRep hsnkRep hsucc e (by omega) o
        (hmem o _ (le_max_left _ _)) o'' (hmem o'' _ (le_max_right _ _))).symm
    rw [h1, h2, h3]
    exact (B N).2.mul o (hmem o N (by omega)) o' (hmem o' N (by omega)) o'' (hmem o'' N (by omega))

end Build

end Thin

end MultiplicativeBasisDeformations
