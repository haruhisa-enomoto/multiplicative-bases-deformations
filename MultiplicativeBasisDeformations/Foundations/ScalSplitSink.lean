module

public import MultiplicativeBasisDeformations.Foundations.ScalSplit

/-!
# Lemma 4.11(2) for a sink

`lem:source-basis-extension` (`scalar-normalization.tex`): "Both assertions hold dually for
a sink." For a sink `t` of `T = T' ∪ {t}`, `op t` is a source of the opposite category. Weights
on `S ⊆ O` and on the corresponding set of `Oᵒᵖ` correspond (`opScal`: a line `f : o → o'` is the
line `f.op : op o' → op o`), compatibly with restriction (`res_opScal`), so the split surjection
over a source (`sourceScalSplit`) transports to `sinkScalSplit`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory Opposite

namespace MultiplicativeBasisDeformations

universe u v w

namespace Thin

namespace ScalGroup

variable {k : Type u} [Field k] {O : Type v} [Category.{w} O] [Preadditive O] [Linear k O]

attribute [local instance] opLinear

section Op

variable {S : Set O} {S' : Set Oᵒᵖ} (h : ∀ X, X ∈ S' ↔ unop X ∈ S)

/-- A line of `Oᵒᵖ` as a line of `O`. -/
def lineOp (ℓ : NzLine S') : NzLine S :=
  ⟨unop ℓ.o', unop ℓ.o, (h _).1 ℓ.mem', (h _).1 ℓ.mem, by
    obtain ⟨f, hf⟩ := ℓ.nz
    exact ⟨f.unop, fun h0 ↦ hf (Quiver.Hom.unop_inj (by rw [h0]; rfl))⟩⟩

/-- A line of `O` as a line of `Oᵒᵖ`. -/
def lineUnop (ℓ : NzLine S) : NzLine S' :=
  ⟨op ℓ.o', op ℓ.o, (h _).2 ℓ.mem', (h _).2 ℓ.mem, by
    obtain ⟨f, hf⟩ := ℓ.nz
    exact ⟨f.op, fun h0 ↦ hf (Quiver.Hom.op_inj (by rw [h0]; rfl))⟩⟩

theorem lineOp_lineUnop (ℓ : NzLine S) : lineOp h (lineUnop h ℓ) = ℓ := NzLine.ext' rfl rfl

theorem lineUnop_lineOp (ℓ : NzLine S') : lineUnop h (lineOp h ℓ) = ℓ := NzLine.ext' rfl rfl

variable (k) in
/-- Weights on `S` as weights on the opposite set. -/
def opScalHom : Scal k S →* Scal k S' where
  toFun d := ⟨fun ℓ ↦ (d : NzLine S → kˣ) (lineOp h ℓ), by
    intro X X' X'' hX hX' hX'' f g hfg
    have hfg' : g.unop ≫ f.unop ≠ 0 := fun h0 ↦ hfg (Quiver.Hom.unop_inj (by
      rw [unop_comp, h0]; rfl))
    have e := scal_mul d ((h _).1 hX'') ((h _).1 hX') ((h _).1 hX) g.unop f.unop hfg'
    dsimp only
    rw [show lineOp h (mkLine hX hX'' (f ≫ g) hfg) = mkLine _ _ _ hfg' from NzLine.ext' rfl rfl,
      show lineOp h (mkLine hX hX' f (left_ne hfg)) = mkLine _ _ _ (right_ne hfg') from
        NzLine.ext' rfl rfl,
      show lineOp h (mkLine hX' hX'' g (right_ne hfg)) = mkLine _ _ _ (left_ne hfg') from
        NzLine.ext' rfl rfl, e, mul_comm]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable (k) in
/-- Weights on the opposite set as weights on `S`. -/
def unopScalHom : Scal k S' →* Scal k S where
  toFun d := ⟨fun ℓ ↦ (d : NzLine S' → kˣ) (lineUnop h ℓ), by
    intro o o' o'' ho ho' ho'' f g hfg
    have hfg' : g.op ≫ f.op ≠ 0 := fun h0 ↦ hfg (Quiver.Hom.op_inj (by
      rw [op_comp, h0]; rfl))
    have e := scal_mul d ((h _).2 ho'') ((h _).2 ho') ((h _).2 ho) g.op f.op hfg'
    dsimp only
    rw [show lineUnop h (mkLine ho ho'' (f ≫ g) hfg) = mkLine _ _ _ hfg' from NzLine.ext' rfl rfl,
      show lineUnop h (mkLine ho ho' f (left_ne hfg)) = mkLine _ _ _ (right_ne hfg') from
        NzLine.ext' rfl rfl,
      show lineUnop h (mkLine ho' ho'' g (right_ne hfg)) = mkLine _ _ _ (left_ne hfg') from
        NzLine.ext' rfl rfl, e, mul_comm]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable (k) in
/-- **Weights on `S` are weights on the opposite set.** -/
def opScal : Scal k S ≃* Scal k S' where
  toFun := opScalHom k h
  invFun := unopScalHom k h
  left_inv d := Subtype.ext (funext fun ℓ ↦ by
    change (d : NzLine S → kˣ) (lineOp h (lineUnop h ℓ)) = _
    rw [lineOp_lineUnop])
  right_inv d := Subtype.ext (funext fun ℓ ↦ by
    change (d : NzLine S' → kˣ) (lineUnop h (lineOp h ℓ)) = _
    rw [lineUnop_lineOp])
  map_mul' _ _ := rfl

end Op

theorem res_opScal {S₁ S₂ : Set O} {S₁' S₂' : Set Oᵒᵖ} (hS : S₁ ⊆ S₂) (hS' : S₁' ⊆ S₂')
    (h₁ : ∀ X, X ∈ S₁' ↔ unop X ∈ S₁) (h₂ : ∀ X, X ∈ S₂' ↔ unop X ∈ S₂) (d : Scal k S₂) :
    res k hS' (opScal k h₂ d) = opScal k h₁ (res k hS d) :=
  Subtype.ext (funext fun _ ↦ congrArg (d : NzLine S₂ → kˣ) (NzLine.ext' rfl rfl))

section Sink

open Classical

variable [Infinite k] (hT : IsThin k O) (t : O) (S : Finset O) (htS : t ∉ S)
  (hsnk : ∀ o ∈ S, ∀ f : t ⟶ o, f = 0)
  (hrep : SupRepFinite (isThin_op hT) (s := op t) (P := supp (op t) (S.map opEmb))
    (fv := fvec (op t)) (fun y hy ↦ fvec_ne (op t) (S.map opEmb) hy))

include hT htS hsnk hrep in
/-- **Lemma 4.11(2) for a sink**: restriction `Scal(T) → Scal(T')` is a split surjection, with
kernel `k*` to the power of the components of the support poset of the sink (a source of the
opposite category). -/
theorem sinkScalSplit :
    (∃ e : Scal k (S : Set O) →* Scal k (insert t (S : Set O)),
        ∀ d, res k (Set.subset_insert t (S : Set O)) (e d) = d) ∧
      Function.Surjective (res k (Set.subset_insert t (S : Set O))) ∧
      Nonempty ((res k (Set.subset_insert t (S : Set O))).ker ≃*
        (Comp (op t) (S.map opEmb) → kˣ)) := by
  have hT' := isThin_op hT
  have htS' : op t ∉ S.map opEmb := by
    intro h; rw [Finset.mem_map] at h
    obtain ⟨o, ho, ho'⟩ := h
    exact htS (op_injective ho' ▸ ho)
  have hsrc : ∀ X ∈ S.map opEmb, ∀ f : X ⟶ op t, f = 0 := by
    intro X hX f
    rw [Finset.mem_map] at hX
    obtain ⟨o, ho, rfl⟩ := hX
    exact Quiver.Hom.unop_inj (hsnk o ho f.unop)
  obtain ⟨⟨e', he'⟩, -, ⟨κ⟩⟩ := sourceScalSplit hT' (op t) (S.map opEmb) htS' hsrc hrep
  have h₁ : ∀ X, X ∈ ((S.map opEmb : Finset Oᵒᵖ) : Set Oᵒᵖ) ↔ unop X ∈ (S : Set O) := by
    intro X; rw [coe_map_op]; rfl
  have h₂ : ∀ X, X ∈ Tset (op t) (S.map opEmb) ↔ unop X ∈ insert t (S : Set O) := by
    intro X
    simp only [Tset, Set.mem_insert_iff, h₁]
    constructor
    · rintro (rfl | hX); exacts [Or.inl rfl, Or.inr hX]
    · rintro (hX | hX)
      · exact Or.inl (by rw [← hX, op_unop])
      · exact Or.inr hX
  let Φ₁ := opScal k h₁
  let Φ₂ := opScal k h₂
  have nat : ∀ d, res k (sub_T (op t) (S.map opEmb)) (Φ₂ d) =
      Φ₁ (res k (Set.subset_insert t (S : Set O)) d) := fun d ↦
    res_opScal (Set.subset_insert t (S : Set O)) (sub_T (op t) (S.map opEmb)) h₁ h₂ d
  have hres : ∀ d, res k (Set.subset_insert t (S : Set O)) d =
      Φ₁.symm (res k (sub_T (op t) (S.map opEmb)) (Φ₂ d)) := fun d ↦ by
    rw [nat, MulEquiv.symm_apply_apply]
  let e : Scal k (S : Set O) →* Scal k (insert t (S : Set O)) :=
    Φ₂.symm.toMonoidHom.comp (e'.comp Φ₁.toMonoidHom)
  have hsec : ∀ d, res k (Set.subset_insert t (S : Set O)) (e d) = d := fun d ↦ by
    rw [hres]
    change Φ₁.symm (res k _ (Φ₂ (Φ₂.symm (e' (Φ₁ d))))) = d
    rw [MulEquiv.apply_symm_apply, he', MulEquiv.symm_apply_apply]
  refine ⟨⟨e, hsec⟩, fun d ↦ ⟨e d, hsec d⟩, ⟨?_⟩⟩
  have hker : ∀ d, d ∈ (res k (Set.subset_insert t (S : Set O))).ker ↔
      Φ₂ d ∈ (res k (sub_T (op t) (S.map opEmb))).ker := fun d ↦ by
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, nat, MulEquiv.map_eq_one_iff]
  refine MulEquiv.trans ?_ κ
  exact {
    toFun := fun d ↦ ⟨Φ₂ d.1, (hker d.1).1 d.2⟩
    invFun := fun d ↦ ⟨Φ₂.symm d.1, (hker _).2 (by rw [MulEquiv.apply_symm_apply]; exact d.2)⟩
    left_inv := fun d ↦ Subtype.ext (MulEquiv.symm_apply_apply _ _)
    right_inv := fun d ↦ Subtype.ext (MulEquiv.apply_symm_apply _ _)
    map_mul' := fun a b ↦ Subtype.ext (map_mul Φ₂ a.1 b.1) }

end Sink

end ScalGroup

end Thin

end MultiplicativeBasisDeformations
