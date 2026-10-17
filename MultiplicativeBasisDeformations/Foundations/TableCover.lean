import MultiplicativeBasisDeformations.Foundations.TableAlg
import MultiplicativeBasisDeformations.Foundations.CategoryAlgebraCorners
import MultiplicativeBasisDeformations.Foundations.FullIdempotent

/-!
# Corners, repeated labels and graded covers of ray tables (Lemma 4.7 for `kP`)

* `restrict P W`: the full subtable on a set `W` of vertices; its linearization is the
  idempotent corner of `kP` at `∑_{x ∈ W} e_x` (`restrictEquiv`), so it is
  representation-finite with `kP` (Lemma 3.1(1)).
* `infl P v`: repeated labels `v : κ → V`; representation-finite with `kP` by Morita
  equivalence through a full idempotent (as in Lemma 4.7, first step).
* `cover P γ v g`: the full subcategory of the graded covering category on the objects
  `(v i, g i)`, for a grading `γ` of the rays; representation-finite with `kP` by the split
  transfer of Lemma 4.6 (`lem:homogeneous-projection`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

variable {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R]

namespace Mult

variable (P : Mult V R) (k : Type u) [Field k]

/-! ### Restriction to a set of vertices -/

section Restrict

variable (W : Finset V)

/-- Vertices in `W`. -/
abbrev RV := {x : V // x ∈ W}

/-- Rays with both endpoints in `W`. -/
abbrev RR := {r : R // P.src r ∈ W ∧ P.tgt r ∈ W}

/-- The product of rays with endpoints in `W`. -/
def mulW (r s : RR P W) : Option (RR P W) :=
  (P.mul r.1 s.1).pmap (fun t ht ↦ (⟨t, ht⟩ : RR P W)) fun t ht ↦
    ⟨by rw [P.mul_src _ _ _ ht]; exact r.2.1, by rw [P.mul_tgt _ _ _ ht]; exact s.2.2⟩

theorem mulW_val (r s : RR P W) : (P.mulW W r s).map Subtype.val = P.mul r.1 s.1 := by
  simp only [mulW, Option.map_pmap, Option.pmap_eq_map, Option.map_id']

theorem mulW_eq_some {r s t : RR P W} (h : P.mulW W r s = some t) : P.mul r.1 s.1 = some t.1 := by
  rw [← mulW_val, h]; rfl

theorem mulW_eq_some_iff {r s t : RR P W} : P.mulW W r s = some t ↔ P.mul r.1 s.1 = some t.1 := by
  refine ⟨P.mulW_eq_some W, fun h ↦ ?_⟩
  have := P.mulW_val W r s
  rw [h] at this
  obtain ⟨t', ht', ht'e⟩ := Option.map_eq_some_iff.1 this
  rw [ht', Subtype.ext ht'e]

/-- **The full subtable on `W`.** -/
def restrict : Mult (RV W) (RR P W) where
  src r := ⟨P.src r.1, r.2.1⟩
  tgt r := ⟨P.tgt r.1, r.2.2⟩
  e x := ⟨P.e x.1, by rw [P.src_e]; exact x.2, by rw [P.tgt_e]; exact x.2⟩
  src_e x := Subtype.ext (P.src_e x.1)
  tgt_e x := Subtype.ext (P.tgt_e x.1)
  mul := P.mulW W
  mul_src r s t h := Subtype.ext (P.mul_src _ _ _ (P.mulW_eq_some W h))
  mul_tgt r s t h := Subtype.ext (P.mul_tgt _ _ _ (P.mulW_eq_some W h))
  mul_mid r s t h := Subtype.ext (P.mul_mid _ _ _ (P.mulW_eq_some W h))
  e_mul r := (P.mulW_eq_some_iff W).2 (P.e_mul r.1)
  mul_e r := (P.mulW_eq_some_iff W).2 (P.mul_e r.1)
  assoc r s u := by
    apply Option.map_injective Subtype.val_injective
    rw [Option.map_bind, Option.map_bind]
    change (P.mulW W r s).bind (fun t ↦ (P.mulW W t u).map Subtype.val) =
      (P.mulW W s u).bind (fun t ↦ (P.mulW W r t).map Subtype.val)
    simp only [mulW_val]
    have h1 : ∀ x : Option (RR P W), x.bind (fun t ↦ P.mul t.1 u.1) =
        (x.map Subtype.val).bind (fun t ↦ P.mul t u.1) := fun x ↦ by cases x <;> rfl
    have h2 : ∀ x : Option (RR P W), x.bind (fun t ↦ P.mul r.1 t.1) =
        (x.map Subtype.val).bind (fun t ↦ P.mul r.1 t) := fun x ↦ by cases x <;> rfl
    rw [h1, h2, mulW_val, mulW_val]
    exact P.assoc r.1 s.1 u.1

/-- The idempotent `∑_{x ∈ W} e_x`. -/
def eW : P.Lin k := ∑ x ∈ W, P.b k (P.e x)

/-- The inclusion of the full subtable. -/
def inclW : (P.restrict W).Lin k →ₗ[k] P.Lin k :=
  ((P.restrict W).basis k).constr k fun r ↦ P.b k r.1

theorem inclW_b (r : RR P W) : P.inclW k W ((P.restrict W).b k r) = P.b k r.1 := by
  rw [inclW, ← Mult.basis_apply, Module.Basis.constr_basis]

theorem restrict_b_mul (r s : RR P W) :
    (P.restrict W).b k r * (P.restrict W).b k s = (P.mulW W r s).elim 0 ((P.restrict W).b k) :=
  (P.restrict W).b_mul k r s

theorem inclW_mul (x y : (P.restrict W).Lin k) :
    P.inclW k W (x * y) = P.inclW k W x * P.inclW k W y := by
  have h : (LinearMap.mul k _).compr₂ (P.inclW k W) =
      (LinearMap.mul k (P.Lin k)).compl₁₂ (P.inclW k W) (P.inclW k W) := by
    refine LinearMap.ext_basis ((P.restrict W).basis k) ((P.restrict W).basis k) fun r s ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
      Mult.basis_apply, inclW_b, Mult.b_mul]
    rw [show (P.restrict W).mul r s = P.mulW W r s from rfl, ← P.mulW_val W r s]
    cases P.mulW W r s with
    | none => simp
    | some t => simp only [Option.elim_some, Option.map_some, inclW_b]
  exact congrArg (fun B ↦ B x y) h

theorem inclW_one : P.inclW k W 1 = P.eW k W := by
  rw [← (P.restrict W).sum_b_e k, map_sum]
  simp only [inclW_b]
  rw [eW, ← Finset.sum_coe_sort W]
  rfl

theorem isIdempotentElem_eW : IsIdempotentElem (P.eW k W) := by
  rw [IsIdempotentElem, ← inclW_one, ← inclW_mul, mul_one]

theorem eW_mul_b (r : R) : P.eW k W * P.b k r = if P.src r ∈ W then P.b k r else 0 := by
  rw [eW, Finset.sum_mul]
  simp only [Mult.b_e_mul]
  rw [Finset.sum_ite_eq']

theorem b_mul_eW (r : R) : P.b k r * P.eW k W = if P.tgt r ∈ W then P.b k r else 0 := by
  rw [eW, Finset.mul_sum]
  simp only [Mult.b_mul_e]
  rw [Finset.sum_ite_eq']

theorem inclW_injective : Function.Injective (P.inclW k W) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply ((P.restrict W).basis k).repr.injective
  ext r
  have h := congrArg (fun y ↦ (P.basis k).repr y r.1) hx
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply] at h
  rw [← ((P.restrict W).basis k).sum_repr x, map_sum] at h
  simp only [map_smul, ← Mult.basis_apply, inclW_b, map_sum, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.smul_apply, Mult.basis_apply, Mult.basis_repr_b, smul_eq_mul,
    mul_ite, mul_one, mul_zero] at h
  rw [Finset.sum_eq_single r (fun r' _ hr' ↦ if_neg (fun h' ↦ hr' (Subtype.ext h')))
    (fun h' ↦ absurd (Finset.mem_univ r) h'), if_pos rfl] at h
  simpa using h

theorem mem_range_inclW (y : P.Lin k) (hy : P.eW k W * y * P.eW k W = y) :
    ∃ x, P.inclW k W x = y := by
  let c := (P.basis k).repr y
  have hy2 : y = ∑ r, c r • (if P.src r ∈ W ∧ P.tgt r ∈ W then P.b k r else 0) := by
    conv_lhs => rw [← hy, ← (P.basis k).sum_repr y]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [mul_smul_comm, smul_mul_assoc, Mult.basis_apply, eW_mul_b]
    by_cases h1 : P.src r ∈ W <;> by_cases h2 : P.tgt r ∈ W <;> simp [c, h1, h2, b_mul_eW]
  refine ⟨∑ r : RR P W, c r.1 • (P.restrict W).b k r, ?_⟩
  rw [map_sum, hy2]
  simp only [map_smul, inclW_b]
  simp only [smul_ite, smul_zero]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun r ↦ by simp) (fun r ↦ c r • P.b k r)).symm

/-- **The full subtable is the idempotent corner.** -/
def restrictEquiv : (P.restrict W).Lin k ≃ₐ[k] (P.isIdempotentElem_eW k W).Corner :=
  cornerEquivOf (P.isIdempotentElem_eW k W) (P.inclW k W) (P.inclW_mul k W)
    (P.inclW_one k W) (P.inclW_injective k W) (P.mem_range_inclW k W)

/-- **Representation-finiteness passes to full subtables** (Lemma 3.1(1)). -/
theorem restrict_isRepresentationFinite (h : IsRepresentationFinite k (P.Lin k)) :
    IsRepresentationFinite k ((P.restrict W).Lin k) := by
  have := corner_finite (k := k) (P.isIdempotentElem_eW k W)
  exact isRepresentationFinite_of_algEquiv (P.restrictEquiv k W).symm
    (corner_isRepresentationFinite_of (P.isIdempotentElem_eW k W) h)

end Restrict

/-! ### Repeated labels -/

section Infl

variable {κ : Type} [Fintype κ] [DecidableEq κ] (v : κ → V)

/-- Rays between labelled objects. -/
abbrev IR := {t : κ × κ × R // P.src t.2.2 = v t.1 ∧ P.tgt t.2.2 = v t.2.1}

/-- The product of labelled rays. -/
def mulI (t t' : IR P v) : Option (IR P v) :=
  if h : t.1.2.1 = t'.1.1 then
    (P.mul t.1.2.2 t'.1.2.2).pmap (fun m hm ↦ (⟨(t.1.1, t'.1.2.1, m), hm⟩ : IR P v)) fun m hm ↦
      ⟨by rw [P.mul_src _ _ _ hm]; exact t.2.1, by rw [P.mul_tgt _ _ _ hm]; exact t'.2.2⟩
  else none

theorem mulI_val (t t' : IR P v) : (P.mulI v t t').map Subtype.val =
    if t.1.2.1 = t'.1.1 then (P.mul t.1.2.2 t'.1.2.2).map (fun m ↦ (t.1.1, t'.1.2.1, m))
    else none := by
  unfold mulI
  split_ifs with h
  · simp only [Option.map_pmap, Option.pmap_eq_map]
  · rfl

theorem mulI_eq_some {t t' t'' : IR P v} (h : P.mulI v t t' = some t'') :
    t.1.2.1 = t'.1.1 ∧ P.mul t.1.2.2 t'.1.2.2 = some t''.1.2.2 ∧ t''.1.1 = t.1.1 ∧
      t''.1.2.1 = t'.1.2.1 := by
  have := P.mulI_val v t t'
  rw [h] at this
  split_ifs at this with hm
  · obtain ⟨m, hm', hme⟩ := Option.map_eq_some_iff.1 this.symm
    have h1 := congrArg Prod.fst hme
    have h2 := congrArg (fun p ↦ p.2.1) hme
    have h3 := congrArg (fun p ↦ p.2.2) hme
    simp only at h1 h2 h3
    exact ⟨hm, by rw [hm', h3], h1.symm, h2.symm⟩
  · exact absurd this (by simp)

theorem mulI_eq_some_iff {t t' t'' : IR P v} : P.mulI v t t' = some t'' ↔
    t.1.2.1 = t'.1.1 ∧ P.mul t.1.2.2 t'.1.2.2 = some t''.1.2.2 ∧ t''.1.1 = t.1.1 ∧
      t''.1.2.1 = t'.1.2.1 := by
  refine ⟨P.mulI_eq_some v, fun ⟨h1, h2, h3, h4⟩ ↦ ?_⟩
  have := P.mulI_val v t t'
  rw [if_pos h1, h2] at this
  obtain ⟨t₀, ht₀, ht₀e⟩ := Option.map_eq_some_iff.1 this
  rw [ht₀]
  congr 1
  apply Subtype.ext
  rw [ht₀e]
  ext <;> simp [h3, h4]

/-- **Repeated labels.** -/
def infl : Mult κ (IR P v) where
  src t := t.1.1
  tgt t := t.1.2.1
  e i := ⟨(i, i, P.e (v i)), P.src_e _, P.tgt_e _⟩
  src_e _ := rfl
  tgt_e _ := rfl
  mul := P.mulI v
  mul_src _ _ _ h := (P.mulI_eq_some v h).2.2.1
  mul_tgt _ _ _ h := (P.mulI_eq_some v h).2.2.2
  mul_mid _ _ _ h := (P.mulI_eq_some v h).1
  e_mul t := (P.mulI_eq_some_iff v).2 ⟨rfl, by have := P.e_mul t.1.2.2; rwa [t.2.1] at this,
    rfl, rfl⟩
  mul_e t := (P.mulI_eq_some_iff v).2 ⟨rfl, by have := P.mul_e t.1.2.2; rwa [t.2.2] at this,
    rfl, rfl⟩
  assoc t t' t'' := by
    apply Option.map_injective Subtype.val_injective
    rw [Option.map_bind, Option.map_bind]
    change (P.mulI v t t').bind (fun s ↦ (P.mulI v s t'').map Subtype.val) =
      (P.mulI v t' t'').bind (fun s ↦ (P.mulI v t s).map Subtype.val)
    simp only [mulI_val]
    have hA := P.assoc t.1.2.2 t'.1.2.2 t''.1.2.2
    by_cases h1 : t.1.2.1 = t'.1.1 <;> by_cases h2 : t'.1.2.1 = t''.1.1
    · have e1 : ∀ x : Option (IR P v), P.mulI v t t' = x → x.bind (fun s ↦ if s.1.2.1 = t''.1.1
          then (P.mul s.1.2.2 t''.1.2.2).map (fun m ↦ (s.1.1, t''.1.2.1, m)) else none) =
          ((P.mul t.1.2.2 t'.1.2.2).bind (fun m ↦ P.mul m t''.1.2.2)).map
            (fun m ↦ (t.1.1, t''.1.2.1, m)) := by
        intro x hx
        cases x with
        | none =>
          have := P.mulI_val v t t'
          rw [hx, if_pos h1] at this
          simp only [Option.map_none] at this
          rw [Option.map_eq_none_iff.1 this.symm]; rfl
        | some s =>
          obtain ⟨-, hs2, hs3, hs4⟩ := P.mulI_eq_some v hx
          simp only [Option.bind_some, hs4, if_pos h2, hs2, hs3]
      have e2 : ∀ x : Option (IR P v), P.mulI v t' t'' = x → x.bind (fun s ↦ if t.1.2.1 = s.1.1
          then (P.mul t.1.2.2 s.1.2.2).map (fun m ↦ (t.1.1, s.1.2.1, m)) else none) =
          ((P.mul t'.1.2.2 t''.1.2.2).bind (fun m ↦ P.mul t.1.2.2 m)).map
            (fun m ↦ (t.1.1, t''.1.2.1, m)) := by
        intro x hx
        cases x with
        | none =>
          have := P.mulI_val v t' t''
          rw [hx, if_pos h2] at this
          simp only [Option.map_none] at this
          rw [Option.map_eq_none_iff.1 this.symm]; rfl
        | some s =>
          obtain ⟨-, hs2, hs3, hs4⟩ := P.mulI_eq_some v hx
          simp only [Option.bind_some, hs3, if_pos h1, hs2, hs4]
      rw [e1 _ rfl, e2 _ rfl, hA]
    · have : P.mulI v t' t'' = none := by
        cases h : P.mulI v t' t'' with
        | none => rfl
        | some s => exact absurd (P.mulI_eq_some v h).1 h2
      rw [this, Option.bind_none]
      cases h : P.mulI v t t' with
      | none => rfl
      | some s =>
        obtain ⟨-, -, -, hs4⟩ := P.mulI_eq_some v h
        simp only [Option.bind_some, hs4, if_neg h2]
    · have : P.mulI v t t' = none := by
        cases h : P.mulI v t t' with
        | none => rfl
        | some s => exact absurd (P.mulI_eq_some v h).1 h1
      rw [this, Option.bind_none]
      cases h : P.mulI v t' t'' with
      | none => rfl
      | some s =>
        obtain ⟨-, -, hs3, -⟩ := P.mulI_eq_some v h
        simp only [Option.bind_some, hs3, if_neg h1]
    · have : P.mulI v t t' = none := by
        cases h : P.mulI v t t' with
        | none => rfl
        | some s => exact absurd (P.mulI_eq_some v h).1 h1
      rw [this, Option.bind_none]
      have : P.mulI v t' t'' = none := by
        cases h : P.mulI v t' t'' with
        | none => rfl
        | some s => exact absurd (P.mulI_eq_some v h).1 h2
      rw [this, Option.bind_none]

theorem infl_mul_val (t t' : IR P v) : ((P.infl v).mul t t').map Subtype.val =
    if t.1.2.1 = t'.1.1 then (P.mul t.1.2.2 t'.1.2.2).map (fun m ↦ (t.1.1, t'.1.2.1, m))
    else none := P.mulI_val v t t'

/-- A labelled ray. -/
def lr (i j : κ) (r : R) (h1 : P.src r = v i) (h2 : P.tgt r = v j) : IR P v := ⟨(i, j, r), h1, h2⟩

theorem infl_b_mul_b (i j l : κ) (r s : R) (h1 h2 h3 h4) (t : R) (ht : P.mul r s = some t) :
    (P.infl v).b k (P.lr v i j r h1 h2) * (P.infl v).b k (P.lr v j l s h3 h4) =
      (P.infl v).b k (P.lr v i l t (by rw [P.mul_src _ _ _ ht]; exact h1)
        (by rw [P.mul_tgt _ _ _ ht]; exact h4)) := by
  apply Mult.b_mul_of_some
  exact (P.mulI_eq_some_iff v).2 ⟨rfl, ht, rfl, rfl⟩

/-- Vertices hit by the labels. -/
def Wv : Finset V := Finset.univ.image v

/-- A chosen label of a hit vertex. -/
def sec (x : RV (Wv v)) : κ := (Finset.mem_image.1 x.2).choose

theorem v_sec (x : RV (Wv v)) : v (sec v x) = x.1 := (Finset.mem_image.1 x.2).choose_spec.2

theorem mem_Wv (i : κ) : v i ∈ Wv v := Finset.mem_image_of_mem v (Finset.mem_univ i)

/-- The chosen labels. -/
def Wk : Finset κ := Finset.univ.filter fun i ↦ sec v ⟨v i, mem_Wv v i⟩ = i

theorem sec_mem (x : RV (Wv v)) : sec v x ∈ Wk v := by
  simp only [Wk, Finset.mem_filter, Finset.mem_univ, true_and]
  congr 1
  exact Subtype.ext (v_sec v x)

theorem sec_v_of_mem {i : κ} (h : i ∈ Wk v) : sec v ⟨v i, mem_Wv v i⟩ = i := by
  simpa [Wk] using h

/-- The ray map from the full subtable on the hit vertices. -/
def secRay (r : RR P (Wv v)) : RR (P.infl v) (Wk v) :=
  ⟨P.lr v (sec v ⟨P.src r.1, r.2.1⟩) (sec v ⟨P.tgt r.1, r.2.2⟩) r.1
    (v_sec v ⟨P.src r.1, r.2.1⟩).symm (v_sec v ⟨P.tgt r.1, r.2.2⟩).symm, sec_mem v _, sec_mem v _⟩

theorem secRay_val (r : RR P (Wv v)) : (P.secRay v r).1.1 =
    (sec v ⟨P.src r.1, r.2.1⟩, sec v ⟨P.tgt r.1, r.2.2⟩, r.1) := rfl

theorem sec_injective : Function.Injective (sec v) := fun x y h ↦ by
  apply Subtype.ext
  rw [← v_sec v x, ← v_sec v y, h]

/-- **The full subtable on the hit vertices maps onto the chosen labels.** -/
def secMor : Mor (P.restrict (Wv v)) ((P.infl v).restrict (Wk v)) where
  f r := some (P.secRay v r)
  hmul r s := by
    simp only [Option.bind_some]
    apply Option.map_injective (f := fun t : RR (P.infl v) (Wk v) ↦ t.1.1)
      (fun a b h ↦ Subtype.ext (Subtype.ext h))
    change Option.map (Subtype.val ∘ Subtype.val)
      ((P.infl v).mulW (Wk v) (P.secRay v r) (P.secRay v s)) = _
    rw [← Option.map_map, Mult.mulW_val, infl_mul_val, Option.map_bind]
    split_ifs with hc
    · change Option.map (fun m ↦ (sec v ⟨P.src r.1, r.2.1⟩, sec v ⟨P.tgt s.1, s.2.2⟩, m))
        (P.mul r.1 s.1) = (P.mulW (Wv v) r s).bind _
      cases h : P.mulW (Wv v) r s with
      | none =>
        have := P.mulW_val (Wv v) r s
        rw [h] at this
        rw [← this]; rfl
      | some t =>
        have ht := (P.mulW_eq_some_iff (Wv v)).1 h
        rw [ht]
        change some _ = some (sec v ⟨P.src t.1, t.2.1⟩, sec v ⟨P.tgt t.1, t.2.2⟩, t.1)
        have e1 : (⟨P.src t.1, t.2.1⟩ : RV (Wv v)) = ⟨P.src r.1, r.2.1⟩ :=
          Subtype.ext (P.mul_src _ _ _ ht)
        have e2 : (⟨P.tgt t.1, t.2.2⟩ : RV (Wv v)) = ⟨P.tgt s.1, s.2.2⟩ :=
          Subtype.ext (P.mul_tgt _ _ _ ht)
        rw [e1, e2]
    · change none = (P.mulW (Wv v) r s).bind _
      have hm : P.tgt r.1 ≠ P.src s.1 := fun hm ↦ hc (by
        change sec v ⟨P.tgt r.1, r.2.2⟩ = sec v ⟨P.src s.1, s.2.1⟩
        congr 1; exact Subtype.ext hm)
      cases h : P.mulW (Wv v) r s with
      | none => rfl
      | some t => exact absurd (P.mul_mid _ _ _ ((P.mulW_eq_some_iff (Wv v)).1 h)) hm
  hid x := Or.inr ⟨⟨sec v x, sec_mem v x⟩, by
    simp only [Option.some.injEq]
    apply Subtype.ext; apply Subtype.ext
    change (sec v ⟨P.src (P.e x.1), _⟩, sec v ⟨P.tgt (P.e x.1), _⟩, P.e x.1) =
      (sec v x, sec v x, P.e (v (sec v x)))
    have h1 : (⟨P.src (P.e x.1), by rw [P.src_e]; exact x.2⟩ : RV (Wv v)) = x :=
      Subtype.ext (P.src_e _)
    have h2 : (⟨P.tgt (P.e x.1), by rw [P.tgt_e]; exact x.2⟩ : RV (Wv v)) = x :=
      Subtype.ext (P.tgt_e _)
    rw [v_sec v x]
    simp only [h1, h2]⟩
  hid' i := by
    refine ⟨⟨v i.1, mem_Wv v i.1⟩, ?_, fun y hy ↦ ?_⟩
    · simp only [Option.some.injEq]
      apply Subtype.ext; apply Subtype.ext
      change (sec v ⟨P.src (P.e (v i.1)), _⟩, sec v ⟨P.tgt (P.e (v i.1)), _⟩, P.e (v i.1)) =
        (i.1, i.1, P.e (v i.1))
      have h1 : (⟨P.src (P.e (v i.1)), by rw [P.src_e]; exact mem_Wv v i.1⟩ : RV (Wv v)) =
          ⟨v i.1, mem_Wv v i.1⟩ := Subtype.ext (P.src_e _)
      have h2 : (⟨P.tgt (P.e (v i.1)), by rw [P.tgt_e]; exact mem_Wv v i.1⟩ : RV (Wv v)) =
          ⟨v i.1, mem_Wv v i.1⟩ := Subtype.ext (P.tgt_e _)
      simp only [h1, h2, sec_v_of_mem v i.2]
    · simp only [Option.some.injEq] at hy
      have := congrArg (fun t : RR (P.infl v) (Wk v) ↦ t.1.1.1) hy
      change sec v ⟨P.src (P.e y.1), _⟩ = i.1 at this
      apply Subtype.ext
      rw [← v_sec v y, ← this]
      congr 2
      exact Subtype.ext (P.src_e _).symm

theorem secMor_surjective (t : RR (P.infl v) (Wk v)) : ∃ r, (P.secMor v).f r = some t := by
  obtain ⟨⟨⟨i, j, r⟩, h1, h2⟩, hi, hj⟩ := t
  change i ∈ Wk v at hi
  change j ∈ Wk v at hj
  refine ⟨⟨r, by rw [h1]; exact mem_Wv v i, by rw [h2]; exact mem_Wv v j⟩, ?_⟩
  simp only [secMor, Option.some.injEq]
  apply Subtype.ext; apply Subtype.ext
  rw [secRay_val]
  have e1 : (⟨P.src r, by rw [h1]; exact mem_Wv v i⟩ : RV (Wv v)) = ⟨v i, mem_Wv v i⟩ :=
    Subtype.ext h1
  have e2 : (⟨P.tgt r, by rw [h2]; exact mem_Wv v j⟩ : RV (Wv v)) = ⟨v j, mem_Wv v j⟩ :=
    Subtype.ext h2
  simp only [e1, e2, sec_v_of_mem v hi, sec_v_of_mem v hj]

theorem infl_full (a : (P.infl v).Lin k) :
    a ∈ Submodule.span k {x | ∃ p q, x = p * (P.infl v).eW k (Wk v) * q} := by
  have : a ∈ Submodule.span k (Set.range ((P.infl v).b k)) := by
    rw [(P.infl v).span_b k]; trivial
  refine Submodule.span_mono ?_ this
  rintro _ ⟨⟨⟨i, j, r⟩, h1, h2⟩, rfl⟩
  set σi := sec v ⟨v i, mem_Wv v i⟩
  set σj := sec v ⟨v j, mem_Wv v j⟩
  have hσi : v σi = v i := v_sec v _
  have hσj : v σj = v j := v_sec v _
  refine ⟨(P.infl v).b k (P.lr v i σi (P.e (v i)) (P.src_e _) (by rw [P.tgt_e, hσi])),
    (P.infl v).b k (P.lr v σi j r (by rw [h1, hσi]) h2), ?_⟩
  rw [b_mul_eW, if_pos (show (P.infl v).tgt (P.lr v i σi (P.e (v i)) (P.src_e _)
    (by rw [P.tgt_e, hσi])) ∈ Wk v from sec_mem v _)]
  rw [P.infl_b_mul_b k v i σi j (P.e (v i)) r _ _ _ _ r (by rw [← h1]; exact P.e_mul r)]
  rfl

/-- **Repeated labels preserve representation-finiteness.** -/
theorem infl_isRepresentationFinite (h : IsRepresentationFinite k (P.Lin k)) :
    IsRepresentationFinite k ((P.infl v).Lin k) := by
  have h1 := P.restrict_isRepresentationFinite k (Wv v) h
  have h2 := (P.secMor v).isRepresentationFinite k (P.secMor_surjective v) h1
  have := corner_finite (k := k) ((P.infl v).isIdempotentElem_eW k (Wk v))
  have h3 : IsRepresentationFinite k ((P.infl v).isIdempotentElem_eW k (Wk v)).Corner :=
    isRepresentationFinite_of_algEquiv ((P.infl v).restrictEquiv k (Wk v)) h2
  exact isRepresentationFinite_of_full ((P.infl v).isIdempotentElem_eW k (Wk v))
    (P.infl_full k v) h3

/-! ### Graded covers -/

section Cover

variable {G : Type} [AddCommGroup G] [DecidableEq G] (γ : R → G) (hγ : ∀ r s t, P.mul r s = some t → γ t = γ r + γ s)
  (g : κ → G)

include hγ in
theorem γ_e (x : V) : γ (P.e x) = 0 := by
  have := hγ _ _ _ (P.e_mul (P.e x))
  rw [P.src_e] at this
  exact add_eq_left.1 this.symm

/-- Rays of the graded cover: labelled rays of degree `g j - g i`. -/
abbrev CR := {t : IR P v // γ t.1.2.2 = g t.1.2.1 - g t.1.1}

include hγ in
theorem graded_of_mulI {t t' t'' : IR P v} (h : P.mulI v t t' = some t'')
    (ht : γ t.1.2.2 = g t.1.2.1 - g t.1.1) (ht' : γ t'.1.2.2 = g t'.1.2.1 - g t'.1.1) :
    γ t''.1.2.2 = g t''.1.2.1 - g t''.1.1 := by
  obtain ⟨h1, h2, h3, h4⟩ := P.mulI_eq_some v h
  rw [hγ _ _ _ h2, ht, ht', h3, h4, h1]
  abel

/-- The product of the graded cover. -/
def mulC (t t' : CR P v γ g) : Option (CR P v γ g) :=
  (P.mulI v t.1 t'.1).pmap (fun t'' h ↦ (⟨t'', h⟩ : CR P v γ g)) fun _ h ↦
    P.graded_of_mulI v γ hγ g h t.2 t'.2

theorem mulC_val (t t' : CR P v γ g) :
    (P.mulC v γ hγ g t t').map Subtype.val = P.mulI v t.1 t'.1 := by
  simp only [mulC, Option.map_pmap, Option.pmap_eq_map, Option.map_id']

theorem mulC_eq_some_iff {t t' t'' : CR P v γ g} :
    P.mulC v γ hγ g t t' = some t'' ↔ P.mulI v t.1 t'.1 = some t''.1 := by
  constructor
  · intro h; rw [← P.mulC_val v γ hγ g, h]; rfl
  · intro h
    have := P.mulC_val v γ hγ g t t'
    rw [h] at this
    obtain ⟨t₀, ht₀, ht₀e⟩ := Option.map_eq_some_iff.1 this
    rw [ht₀, Subtype.ext ht₀e]

/-- **The graded cover** on the objects `(v i, g i)`. -/
def cover : Mult κ (CR P v γ g) where
  src t := t.1.1.1
  tgt t := t.1.1.2.1
  e i := ⟨(P.infl v).e i, by
    change γ (P.e (v i)) = g i - g i
    rw [P.γ_e γ hγ, sub_self]⟩
  src_e _ := rfl
  tgt_e _ := rfl
  mul := P.mulC v γ hγ g
  mul_src _ _ _ h := (P.infl v).mul_src _ _ _ ((P.mulC_eq_some_iff v γ hγ g).1 h)
  mul_tgt _ _ _ h := (P.infl v).mul_tgt _ _ _ ((P.mulC_eq_some_iff v γ hγ g).1 h)
  mul_mid _ _ _ h := (P.infl v).mul_mid _ _ _ ((P.mulC_eq_some_iff v γ hγ g).1 h)
  e_mul t := (P.mulC_eq_some_iff v γ hγ g).2 ((P.infl v).e_mul t.1)
  mul_e t := (P.mulC_eq_some_iff v γ hγ g).2 ((P.infl v).mul_e t.1)
  assoc t t' t'' := by
    apply Option.map_injective Subtype.val_injective
    rw [Option.map_bind, Option.map_bind]
    change (P.mulC v γ hγ g t t').bind (fun s ↦ (P.mulC v γ hγ g s t'').map Subtype.val) =
      (P.mulC v γ hγ g t' t'').bind (fun s ↦ (P.mulC v γ hγ g t s).map Subtype.val)
    simp only [mulC_val]
    have h1 : ∀ x : Option (CR P v γ g), x.bind (fun s ↦ P.mulI v s.1 t''.1) =
        (x.map Subtype.val).bind (fun s ↦ P.mulI v s t''.1) := fun x ↦ by cases x <;> rfl
    have h2 : ∀ x : Option (CR P v γ g), x.bind (fun s ↦ P.mulI v t.1 s.1) =
        (x.map Subtype.val).bind (fun s ↦ P.mulI v t.1 s) := fun x ↦ by cases x <;> rfl
    rw [h1, h2, mulC_val, mulC_val]
    exact (P.infl v).assoc t.1 t'.1 t''.1

/-- The inclusion of the graded cover into the repeated labels. -/
def coverMor : Mor (P.cover v γ hγ g) (P.infl v) where
  f t := some t.1
  hmul t t' := by
    simp only [Option.bind_some]
    change P.mulI v t.1 t'.1 = (P.mulC v γ hγ g t t').bind (fun s ↦ some s.1)
    rw [← P.mulC_val v γ hγ g]
    cases P.mulC v γ hγ g t t' <;> rfl
  hid i := Or.inr ⟨i, rfl⟩
  hid' i := ⟨i, rfl, fun j hj ↦ by
    have := congrArg (fun o ↦ o.map (fun t : IR P v ↦ t.1.1)) hj
    simp only [Option.map_some, Option.some.injEq] at this
    exact this⟩

/-- The projection onto the graded rays. -/
def coverProj : (P.infl v).Lin k →ₗ[k] (P.cover v γ hγ g).Lin k :=
  ((P.infl v).basis k).constr k fun t ↦
    if h : γ t.1.2.2 = g t.1.2.1 - g t.1.1 then (P.cover v γ hγ g).b k ⟨t, h⟩ else 0

theorem coverProj_b (t : IR P v) : P.coverProj k v γ hγ g ((P.infl v).b k t) =
    if h : γ t.1.2.2 = g t.1.2.1 - g t.1.1 then (P.cover v γ hγ g).b k ⟨t, h⟩ else 0 := by
  rw [coverProj, ← Mult.basis_apply, Module.Basis.constr_basis]

theorem coverMor_alg_b (t : CR P v γ g) :
    (P.coverMor v γ hγ g).alg k ((P.cover v γ hγ g).b k t) = (P.infl v).b k t.1 :=
  (P.coverMor v γ hγ g).alg_b k t

theorem coverProj_alg (x : (P.cover v γ hγ g).Lin k) :
    P.coverProj k v γ hγ g ((P.coverMor v γ hγ g).alg k x) = x := by
  have : (P.coverProj k v γ hγ g).comp ((P.coverMor v γ hγ g).alg k).toLinearMap = LinearMap.id := by
    refine ((P.cover v γ hγ g).basis k).ext fun t ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq, Mult.basis_apply,
      AlgHom.toLinearMap_apply, coverMor_alg_b, coverProj_b, dif_pos t.2]
  exact congrArg (fun f ↦ f x) this

theorem coverProj_left (d : (P.cover v γ hγ g).Lin k) (x : (P.infl v).Lin k) :
    P.coverProj k v γ hγ g ((P.coverMor v γ hγ g).alg k d * x) =
      d * P.coverProj k v γ hγ g x := by
  have h : ((LinearMap.mul k _).compl₁₂ ((P.coverMor v γ hγ g).alg k).toLinearMap
      LinearMap.id).compr₂ (P.coverProj k v γ hγ g) =
      (LinearMap.mul k _).compl₁₂ LinearMap.id (P.coverProj k v γ hγ g) := by
    refine LinearMap.ext_basis ((P.cover v γ hγ g).basis k) ((P.infl v).basis k) fun t t' ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      AlgHom.toLinearMap_apply, LinearMap.id_coe, id_eq, Mult.basis_apply, coverMor_alg_b,
      coverProj_b, Mult.b_mul]
    cases hu : (P.infl v).mul t.1 t' with
    | none =>
      simp only [Option.elim_none, map_zero]
      split_ifs with ht'
      · rw [Mult.b_mul]
        cases hc : (P.cover v γ hγ g).mul t ⟨t', ht'⟩ with
        | none => rfl
        | some w =>
          have := (P.mulC_eq_some_iff v γ hγ g).1 hc
          change P.mulI v t.1 t' = _ at this
          rw [show (P.infl v).mul t.1 t' = P.mulI v t.1 t' from rfl, this] at hu
          exact absurd hu (by simp)
      · rw [mul_zero]
    | some u =>
      simp only [Option.elim_some, coverProj_b]
      have hu' : P.mulI v t.1 t' = some u := hu
      split_ifs with h1 h2 h2
      · rw [Mult.b_mul, show (P.cover v γ hγ g).mul t ⟨t', h2⟩ = some ⟨u, h1⟩ from
          (P.mulC_eq_some_iff v γ hγ g).2 hu']
        rfl
      · exfalso
        obtain ⟨e1, e2, e3, e4⟩ := P.mulI_eq_some v hu'
        apply h2
        have := hγ _ _ _ e2
        rw [h1, t.2, e3, e4, e1] at this
        rw [eq_sub_of_add_eq' this.symm]; abel
      · exact absurd (P.graded_of_mulI v γ hγ g hu' t.2 h2) h1
      · rw [mul_zero]
  exact congrArg (fun B ↦ B d x) h

theorem coverProj_right (x : (P.infl v).Lin k) (d : (P.cover v γ hγ g).Lin k) :
    P.coverProj k v γ hγ g (x * (P.coverMor v γ hγ g).alg k d) =
      P.coverProj k v γ hγ g x * d := by
  have h : ((LinearMap.mul k _).compl₁₂ LinearMap.id
      ((P.coverMor v γ hγ g).alg k).toLinearMap).compr₂ (P.coverProj k v γ hγ g) =
      (LinearMap.mul k _).compl₁₂ (P.coverProj k v γ hγ g) LinearMap.id := by
    refine LinearMap.ext_basis ((P.infl v).basis k) ((P.cover v γ hγ g).basis k) fun t' t ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      AlgHom.toLinearMap_apply, LinearMap.id_coe, id_eq, Mult.basis_apply, coverMor_alg_b,
      coverProj_b, Mult.b_mul]
    cases hu : (P.infl v).mul t' t.1 with
    | none =>
      simp only [Option.elim_none, map_zero]
      split_ifs with ht'
      · rw [Mult.b_mul]
        cases hc : (P.cover v γ hγ g).mul ⟨t', ht'⟩ t with
        | none => rfl
        | some w =>
          have := (P.mulC_eq_some_iff v γ hγ g).1 hc
          change P.mulI v t' t.1 = _ at this
          rw [show (P.infl v).mul t' t.1 = P.mulI v t' t.1 from rfl, this] at hu
          exact absurd hu (by simp)
      · rw [zero_mul]
    | some u =>
      simp only [Option.elim_some, coverProj_b]
      have hu' : P.mulI v t' t.1 = some u := hu
      split_ifs with h1 h2 h2
      · rw [Mult.b_mul, show (P.cover v γ hγ g).mul ⟨t', h2⟩ t = some ⟨u, h1⟩ from
          (P.mulC_eq_some_iff v γ hγ g).2 hu']
        rfl
      · exfalso
        obtain ⟨e1, e2, e3, e4⟩ := P.mulI_eq_some v hu'
        apply h2
        have := hγ _ _ _ e2
        rw [h1, t.2, e3, e4, ← e1] at this
        rw [eq_sub_of_add_eq this.symm]; abel
      · exact absurd (P.graded_of_mulI v γ hγ g hu' h2 t.2) h1
      · rw [zero_mul]
  exact congrArg (fun B ↦ B x d) h

theorem coverMor_injective : Function.Injective ((P.coverMor v γ hγ g).alg k) := fun x y h ↦ by
  rw [← P.coverProj_alg k v γ hγ g x, h, P.coverProj_alg]

/-- **Lemma 4.7 for ray tables** (`lem:homogeneous-projection`): every graded cover of a
representation-finite table is representation-finite. -/
theorem cover_isRepresentationFinite (h : IsRepresentationFinite k (P.Lin k)) :
    IsRepresentationFinite k ((P.cover v γ hγ g).Lin k) := by
  have hB := P.infl_isRepresentationFinite k v h
  set α := (P.coverMor v γ hγ g).alg k
  let e := AlgEquiv.ofInjective α (P.coverMor_injective k v γ hγ g)
  refine splitRepresentationTransfer_of (C := α.range) (q := e.symm.toAlgHom)
    (P.coverProj k v γ hγ g) (fun c c' b ↦ ?_) e.symm.surjective (fun c ↦ ?_) hB
  · obtain ⟨_, d, rfl⟩ := c
    obtain ⟨_, d', rfl⟩ := c'
    have h1 : e.symm ⟨α d, d, rfl⟩ = d := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    have h2 : e.symm ⟨α d', d', rfl⟩ = d' := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    change P.coverProj k v γ hγ g (α d * b * α d') =
      e.symm ⟨α d, d, rfl⟩ * P.coverProj k v γ hγ g b * e.symm ⟨α d', d', rfl⟩
    rw [h1, h2, coverProj_right, coverProj_left]
  · obtain ⟨_, d, rfl⟩ := c
    have h1 : e.symm ⟨α d, d, rfl⟩ = d := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    change P.coverProj k v γ hγ g (α d) = e.symm ⟨α d, d, rfl⟩
    rw [h1, coverProj_alg]

end Cover

end Infl

end Mult

end RaySys


end MultiplicativeBasisDeformations
