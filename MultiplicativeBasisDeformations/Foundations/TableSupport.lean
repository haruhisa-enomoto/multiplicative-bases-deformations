import MultiplicativeBasisDeformations.Foundations.TableCover
import MultiplicativeBasisDeformations.Foundations.FinPoset

/-!
# Incidence tables and faithful supports of ray tables

* `inc Q`: the incidence table of a finite poset; its linearization is the incidence
  algebra (`incEquiv`), so the forbidden configurations of `FinPoset` apply to it.
* Faithful projective support (`def:faithful-support`): the rays from `x` in a finite set
  `T`, ordered by `r ≤ s` if `r v = s` for a ray `v`. Its incidence table is a quotient of
  the graded cover on the objects `(tgt r, wt r)` (the action on `H(X, -)`), so it is
  representation-finite when `kP` is (Lemma 4.10).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

/-! ### Incidence tables -/

section Inc

variable (Q : Type) [PartialOrder Q] [Fintype Q] [DecidableEq Q] [DecidableLE Q]

/-- Comparable pairs. -/
abbrev IP := {p : Q × Q // p.1 ≤ p.2}

/-- **The incidence table of a finite poset.** -/
def inc : Mult Q (IP Q) where
  src p := p.1.1
  tgt p := p.1.2
  e a := ⟨(a, a), le_rfl⟩
  src_e _ := rfl
  tgt_e _ := rfl
  mul p p' := if h : p.1.2 = p'.1.1 then some ⟨(p.1.1, p'.1.2), p.2.trans (h ▸ p'.2)⟩ else none
  mul_src p p' t h := by
    split_ifs at h with h'
    · cases h; rfl
  mul_tgt p p' t h := by
    split_ifs at h with h'
    · cases h; rfl
  mul_mid p p' t h := by
    split_ifs at h with h'
    · exact h'
  e_mul p := by simp
  mul_e p := by simp
  assoc p p' p'' := by
    by_cases h1 : p.1.2 = p'.1.1 <;> by_cases h2 : p'.1.2 = p''.1.1 <;> simp [h1, h2]

variable {Q}

theorem inc_mul_of {p p' : IP Q} (h : p.1.2 = p'.1.1) :
    (inc Q).mul p p' = some ⟨(p.1.1, p'.1.2), p.2.trans (h ▸ p'.2)⟩ := by
  simp [inc, h]

variable (k : Type u) [Field k] [LocallyFiniteOrder Q]

/-- The indicator incidence function of a comparable pair. -/
def delta (p : IP Q) : IncidenceAlgebra k Q :=
  ⟨fun a b ↦ if (a, b) = p.1 then 1 else 0, fun a b hab ↦ by
    rw [if_neg]; rintro h; exact hab (by have := p.2; rw [← h] at this; exact this)⟩

theorem delta_apply (p : IP Q) (a b : Q) : delta k p a b = if (a, b) = p.1 then 1 else 0 := rfl

/-- The map from the linearization of the incidence table. -/
def incLin : (inc Q).Lin k →ₗ[k] IncidenceAlgebra k Q :=
  ((inc Q).basis k).constr k (delta k)

theorem incLin_b (p : IP Q) : incLin k ((inc Q).b k p) = delta k p := by
  rw [incLin, ← Mult.basis_apply, Module.Basis.constr_basis]

theorem delta_mul (p p' : IP Q) :
    delta k p * delta k p' = ((inc Q).mul p p').elim 0 (delta k) := by
  ext a c hac
  rw [IncidenceAlgebra.mul_apply]
  simp only [delta_apply]
  by_cases h : p.1.2 = p'.1.1
  · rw [inc_mul_of h]
    simp only [Option.elim_some, delta_apply]
    by_cases hac' : (a, c) = (p.1.1, p'.1.2)
    · rw [if_pos hac']
      obtain ⟨ha, hc⟩ := Prod.mk.injEq _ _ _ _ ▸ hac'
      subst ha hc
      rw [Finset.sum_eq_single_of_mem p.1.2 (Finset.mem_Icc.2 ⟨p.2, h ▸ p'.2⟩)]
      · rw [if_pos rfl, one_mul, if_pos (by rw [h])]
      · intro b _ hb
        rw [if_neg (fun h' ↦ hb (by rw [Prod.mk.injEq] at h'; exact h'.2)), zero_mul]
    · rw [if_neg hac']
      refine Finset.sum_eq_zero fun b _ ↦ ?_
      by_cases h1 : (a, b) = p.1
      · rw [if_pos h1, one_mul, if_neg]
        intro h2
        apply hac'
        rw [← h1, ← h2]
      · rw [if_neg h1, zero_mul]
  · rw [show (inc Q).mul p p' = none by simp [inc, h]]
    simp only [Option.elim_none, IncidenceAlgebra.zero_apply]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    by_cases h1 : (a, b) = p.1 <;> by_cases h2 : (b, c) = p'.1
    · exfalso; apply h; rw [← h1, ← h2]
    · simp [h2]
    · simp [h1]
    · simp [h1]

/-- Evaluation of incidence functions. -/
def evalAt (a b : Q) : IncidenceAlgebra k Q →+ k where
  toFun f := f a b
  map_zero' := IncidenceAlgebra.zero_apply a b
  map_add' f g := IncidenceAlgebra.add_apply f g a b

theorem sum_apply' {ι : Type} (s : Finset ι) (f : ι → IncidenceAlgebra k Q) (a b : Q) :
    (∑ i ∈ s, f i) a b = ∑ i ∈ s, f i a b :=
  map_sum (evalAt k a b) f s

theorem incLin_mul (x y : (inc Q).Lin k) : incLin k (x * y) = incLin k x * incLin k y := by
  have h : (LinearMap.mul k _).compr₂ (incLin k) =
      (LinearMap.mul k (IncidenceAlgebra k Q)).compl₁₂ (incLin k) (incLin k) := by
    refine LinearMap.ext_basis ((inc Q).basis k) ((inc Q).basis k) fun p p' ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
      Mult.basis_apply, incLin_b, Mult.b_mul, delta_mul]
    cases (inc Q).mul p p' with
    | none => simp
    | some t => simp [incLin_b]
  exact congrArg (fun B ↦ B x y) h

theorem incLin_one : incLin k (1 : (inc Q).Lin k) = 1 := by
  rw [← (inc Q).sum_b_e k, map_sum]
  simp only [incLin_b]
  ext a b hab
  rw [IncidenceAlgebra.one_apply]
  rw [sum_apply']
  simp only [delta_apply]
  by_cases h : a = b
  · subst h
    rw [Finset.sum_eq_single a (fun c _ hc ↦ by
      rw [if_neg]; intro h'; exact hc (by
        have := congrArg Prod.fst h'; exact this.symm)) (by simp)]
    simp [inc]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    rw [if_neg]; intro h'
    simp only [inc, Prod.mk.injEq] at h'
    exact h (h'.1.trans h'.2.symm)

theorem incLin_injective : Function.Injective (incLin k (Q := Q)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply ((inc Q).basis k).repr.injective
  ext p
  have h := congrArg (fun f : IncidenceAlgebra k Q ↦ f p.1.1 p.1.2) hx
  simp only [IncidenceAlgebra.zero_apply] at h
  rw [← ((inc Q).basis k).sum_repr x, map_sum] at h
  rw [sum_apply'] at h
  simp only [map_smul, Mult.basis_apply, incLin_b, IncidenceAlgebra.constSMul_apply, delta_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero] at h
  rw [Finset.sum_eq_single p (fun p' _ hp' ↦ if_neg (fun h' ↦ hp' (Subtype.ext h'.symm)))
    (by simp), if_pos rfl] at h
  simpa using h

theorem incLin_surjective : Function.Surjective (incLin k (Q := Q)) := by
  intro f
  refine ⟨∑ p : IP Q, f p.1.1 p.1.2 • (inc Q).b k p, ?_⟩
  rw [map_sum]
  ext a b hab
  rw [sum_apply']
  simp only [map_smul, incLin_b, IncidenceAlgebra.constSMul_apply, delta_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_eq_single ⟨(a, b), hab⟩ (fun p' _ hp' ↦ if_neg (fun h' ↦ hp' (Subtype.ext h'.symm)))
    (by simp), if_pos rfl]

/-- **The linearization of the incidence table is the incidence algebra.** -/
def incEquiv : (inc Q).Lin k ≃ₐ[k] IncidenceAlgebra k Q :=
  AlgEquiv.ofBijective (AlgHom.ofLinearMap (incLin k) (incLin_one k) (incLin_mul k))
    ⟨incLin_injective k, incLin_surjective k⟩

variable [IsAlgClosed k]

/-- **Forbidden configurations for incidence tables** (Lemma 8.8 with the table after it). -/
theorem inc_forbidden {n : ℕ} {le : Fin n → Fin n → Bool} [Fact (PosetRep.Ax le)]
    (e : PosetRep.Pos n le ≃o Q) (d : Fin n → ℕ) (hu : PosetRep.UniqOK le)
    (hc : PosetRep.CountOK le d) : ¬ IsRepresentationFinite k ((inc Q).Lin k) := by
  intro h
  have := incidence_finiteDimensional (k := k) (P := Q)
  exact PosetRep.forbidden k e d hu hc (isRepresentationFinite_of_algEquiv (incEquiv k) h)

end Inc

/-! ### Faithful supports -/

namespace Tab

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (P : Tab V R L)

/-- Right factorization: `s = r v` for a ray `v`. -/
def RF (r s : R) : Prop := ∃ v, P.mul r v = some s

/-- Left factorization: `r = v s` for a ray `v`. -/
def LF (r s : R) : Prop := ∃ v, P.mul v s = some r

theorem rf_refl (r : R) : P.RF r r := ⟨P.e (P.tgt r), P.mul_e r⟩

theorem lf_refl (r : R) : P.LF r r := ⟨P.e (P.src r), P.e_mul r⟩

theorem mul_assoc_some {r v v' s t : R} (h1 : P.mul r v = some s) (h2 : P.mul s v' = some t) :
    ∃ w, P.mul v v' = some w ∧ P.mul r w = some t := by
  have h := P.assoc r v v'
  rw [h1, Option.bind_some, h2] at h
  cases hw : P.mul v v' with
  | none => rw [hw] at h; exact absurd h.symm (by simp)
  | some w => rw [hw, Option.bind_some] at h; exact ⟨w, rfl, h.symm⟩

theorem mul_assoc_some' {v' v s r t : R} (h1 : P.mul v s = some r) (h2 : P.mul v' r = some t) :
    ∃ w, P.mul v' v = some w ∧ P.mul w s = some t := by
  have h := P.assoc v' v s
  rw [h1, Option.bind_some, h2] at h
  cases hw : P.mul v' v with
  | none => rw [hw] at h; exact absurd h (by simp)
  | some w => rw [hw, Option.bind_some] at h; exact ⟨w, rfl, h⟩

theorem rf_trans {r s t : R} (h1 : P.RF r s) (h2 : P.RF s t) : P.RF r t := by
  obtain ⟨v, hv⟩ := h1
  obtain ⟨v', hv'⟩ := h2
  obtain ⟨w, -, hw⟩ := P.mul_assoc_some hv hv'
  exact ⟨w, hw⟩

theorem lf_trans {r s t : R} (h1 : P.LF r s) (h2 : P.LF s t) : P.LF r t := by
  obtain ⟨v, hv⟩ := h1
  obtain ⟨v', hv'⟩ := h2
  obtain ⟨w, -, hw⟩ := P.mul_assoc_some' hv' hv
  exact ⟨w, hw⟩

theorem eq_of_mul_wt_zero {r v s : R} (h : P.mul r v = some s) (hv : P.wt v = 0) : s = r := by
  have h1 := P.eq_e_of_wt hv
  have h2 := P.mul_mid _ _ _ h
  rw [h1, ← h2, P.mul_e] at h
  exact (Option.some_injective _ h).symm

theorem eq_of_mul_wt_zero' {v r s : R} (h : P.mul v r = some s) (hv : P.wt v = 0) : s = r := by
  have h1 := P.eq_e_of_wt hv
  have h2 := P.mul_mid _ _ _ h
  have h3 : P.src v = P.src r := by rw [← h2, P.tgt_of_eq_e h1]
  rw [h1, h3, P.e_mul] at h
  exact (Option.some_injective _ h).symm

theorem wt_zero_of_sum {v v' : R} (h : P.wt v + P.wt v' = 0) : P.wt v = 0 := by
  have h1 := P.deg_nonneg v
  have h2 := P.deg_nonneg v'
  have h3 : P.deg (P.wt v) + P.deg (P.wt v') = 0 := by rw [← map_add, h, map_zero]
  have h4 : P.deg (P.wt v) = 0 := by omega
  by_contra hv
  exact (P.deg_pos v (fun he ↦ hv (by rw [he, wt_e]))).ne' h4

theorem rf_antisymm {r s : R} (h1 : P.RF r s) (h2 : P.RF s r) : r = s := by
  obtain ⟨v, hv⟩ := h1
  obtain ⟨v', hv'⟩ := h2
  have e1 := P.wt_mul _ _ _ hv
  have e2 := P.wt_mul _ _ _ hv'
  have : P.wt v + P.wt v' = 0 := by
    rw [e1, add_assoc] at e2; exact add_eq_left.1 e2.symm
  exact (P.eq_of_mul_wt_zero hv (P.wt_zero_of_sum this)).symm

theorem lf_antisymm {r s : R} (h1 : P.LF r s) (h2 : P.LF s r) : r = s := by
  obtain ⟨v, hv⟩ := h1
  obtain ⟨v', hv'⟩ := h2
  have e1 := P.wt_mul _ _ _ hv
  have e2 := P.wt_mul _ _ _ hv'
  have : P.wt v + P.wt v' = 0 := by
    rw [e1, ← add_assoc] at e2; rw [add_comm]; exact add_eq_right.1 e2.symm
  exact P.eq_of_mul_wt_zero' hv (P.wt_zero_of_sum this)

theorem mul_assoc_some_inv {r w u h h' : R} (hw : P.mul h h' = some w) (hu : P.mul r w = some u) :
    ∃ s', P.mul r h = some s' ∧ P.mul s' h' = some u := by
  have hA := P.assoc r h h'
  rw [hw, Option.bind_some, hu] at hA
  cases hs : P.mul r h with
  | none => rw [hs] at hA; exact absurd hA (by simp)
  | some s' => rw [hs, Option.bind_some] at hA; exact ⟨s', rfl, hA⟩

theorem mul_assoc_some_inv' {w s u h h' : R} (hw : P.mul h h' = some w) (hu : P.mul w s = some u) :
    ∃ s', P.mul h' s = some s' ∧ P.mul h s' = some u := by
  have hA := P.assoc h h' s
  rw [hw, Option.bind_some, hu] at hA
  cases hs : P.mul h' s with
  | none => rw [hs] at hA; exact absurd hA.symm (by simp)
  | some s' => rw [hs, Option.bind_some] at hA; exact ⟨s', rfl, hA.symm⟩

section Supp

variable (T : Finset R)

/-- The faithful projective support on `T` (`def:faithful-support`): `r ≤ s` if `s = r v`. -/
def ProjSup (_P : Tab V R L) (T : Finset R) : Type := {r : R // r ∈ T}

/-- The ray of a point of the support. -/
def ProjSup.ray {P : Tab V R L} {T : Finset R} (a : P.ProjSup T) : R := Subtype.val a

theorem ProjSup.ray_mem {P : Tab V R L} {T : Finset R} (a : P.ProjSup T) : a.ray ∈ T :=
  Subtype.property a

theorem ProjSup.ext {P : Tab V R L} {T : Finset R} {a b : P.ProjSup T} (h : a.ray = b.ray) :
    a = b := Subtype.ext h

/-- The point of the support at a ray. -/
def ProjSup.mk {P : Tab V R L} {T : Finset R} (r : R) (h : r ∈ T) : P.ProjSup T := ⟨r, h⟩

@[simp] theorem ProjSup.ray_mk {P : Tab V R L} {T : Finset R} (r : R) (h : r ∈ T) :
    (ProjSup.mk (P := P) r h).ray = r := rfl

instance : PartialOrder (P.ProjSup T) where
  le a b := P.RF a.ray b.ray
  le_refl a := P.rf_refl a.ray
  le_trans _ _ _ := P.rf_trans
  le_antisymm a b h1 h2 := ProjSup.ext (P.rf_antisymm h1 h2)

instance : Fintype (P.ProjSup T) := inferInstanceAs (Fintype {r : R // r ∈ T})

instance : DecidableEq (P.ProjSup T) := inferInstanceAs (DecidableEq {r : R // r ∈ T})

noncomputable instance : DecidableLE (P.ProjSup T) := Classical.decRel _

noncomputable instance : DecidableLT (P.ProjSup T) := Classical.decRel _

noncomputable instance : LocallyFiniteOrder (P.ProjSup T) := Fintype.toLocallyFiniteOrder

theorem projSup_le_iff (a b : P.ProjSup T) : a ≤ b ↔ ∃ v, P.mul a.ray v = some b.ray := Iff.rfl

variable {x : V} (hT : ∀ r ∈ T, P.src r = x)

/-- The labels of the projective support: `(tgt r, wt r)`. -/
abbrev psv : P.ProjSup T → V := fun r ↦ P.tgt r.ray

/-- The weights of the projective support. -/
abbrev psg : P.ProjSup T → L := fun r ↦ P.wt r.ray

/-- A comparable pair of the support from a factorization. -/
def supPair (a b : P.ProjSup T) (v : R) (hm : P.mul a.ray v = some b.ray) : IP (P.ProjSup T) :=
  ⟨(a, b), (P.projSup_le_iff T a b).2 ⟨v, hm⟩⟩

/-- The rays of the graded cover of the support. -/
abbrev PCR := Mult.CR P.toMult (P.psv T) P.wt (P.psg T)

/-- The action on `H(X, -)`. -/
def psf (t : P.PCR T) : Option (IP (P.ProjSup T)) :=
  if hm : P.mul t.1.1.1.ray t.1.1.2.2 = some t.1.1.2.1.ray then
    some (P.supPair T t.1.1.1 t.1.1.2.1 t.1.1.2.2 hm) else none

theorem psf_pos (t : P.PCR T) (hm : P.mul t.1.1.1.ray t.1.1.2.2 = some t.1.1.2.1.ray) :
    P.psf T t = some (P.supPair T t.1.1.1 t.1.1.2.1 t.1.1.2.2 hm) := dif_pos hm

theorem psf_neg (t : P.PCR T) (hm : ¬ P.mul t.1.1.1.ray t.1.1.2.2 = some t.1.1.2.1.ray) :
    P.psf T t = none := dif_neg hm

theorem inc_supPair_mul (a b c : P.ProjSup T) (v v' : R) (h1 h2) :
    (inc (P.ProjSup T)).mul (P.supPair T a b v h1) (P.supPair T b c v' h2) =
      some ⟨(a, c), le_trans ((P.projSup_le_iff T a b).2 ⟨v, h1⟩)
        ((P.projSup_le_iff T b c).2 ⟨v', h2⟩)⟩ := inc_mul_of rfl

include hT in
/-- The action on `H(X, -)` as a table morphism onto the incidence table. -/
def projSupMor : Mor (P.cover (P.psv T) P.wt P.wt_mul (P.psg T)) (inc (P.ProjSup T)) where
  f := P.psf T
  hmul t t' := by
    obtain ⟨⟨⟨r, s, h⟩, hh1, hh2⟩, hg⟩ := t
    obtain ⟨⟨⟨s2, u, h'⟩, hh1', hh2'⟩, hg'⟩ := t'
    by_cases hs : s = s2
    · subst hs
      cases hw : P.mul h h' with
      | none =>
        have hC0 : (P.cover (P.psv T) P.wt P.wt_mul (P.psg T)).mul ⟨⟨⟨r, s, h⟩, hh1, hh2⟩, hg⟩
            ⟨⟨⟨s, u, h'⟩, hh1', hh2'⟩, hg'⟩ = none := by
          cases hc : (P.cover (P.psv T) P.wt P.wt_mul (P.psg T)).mul ⟨⟨⟨r, s, h⟩, hh1, hh2⟩, hg⟩
              ⟨⟨⟨s, u, h'⟩, hh1', hh2'⟩, hg'⟩ with
          | none => rfl
          | some c =>
            have := (P.toMult.mulI_eq_some _ ((P.toMult.mulC_eq_some_iff (P.psv T) P.wt P.wt_mul (P.psg T)).1 hc)).2.1
            rw [hw] at this; exact absurd this (by simp)
        rw [hC0, Option.bind_none]
        by_cases h1 : P.mul r.ray h = some s.ray
        · rw [P.psf_pos T _ h1, Option.bind_some]
          by_cases h2 : P.mul s.ray h' = some u.ray
          · obtain ⟨w, hw', -⟩ := P.mul_assoc_some h1 h2
            rw [hw] at hw'; exact absurd hw' (by simp)
          · rw [P.psf_neg T _ h2]; rfl
        · rw [P.psf_neg T _ h1]; rfl
      | some w =>
        have hc : (P.cover (P.psv T) P.wt P.wt_mul (P.psg T)).mul ⟨⟨⟨r, s, h⟩, hh1, hh2⟩, hg⟩
            ⟨⟨⟨s, u, h'⟩, hh1', hh2'⟩, hg'⟩ = some ⟨⟨⟨r, u, w⟩,
              by rw [P.mul_src _ _ _ hw]; exact hh1, by rw [P.mul_tgt _ _ _ hw]; exact hh2'⟩,
              by
                change P.wt w = P.wt u.ray - P.wt r.ray
                change P.wt h = P.wt s.ray - P.wt r.ray at hg
                change P.wt h' = P.wt u.ray - P.wt s.ray at hg'
                rw [P.wt_mul _ _ _ hw, hg, hg']; abel⟩ := by
          exact (P.toMult.mulC_eq_some_iff (P.psv T) P.wt P.wt_mul (P.psg T)).2
            ((P.toMult.mulI_eq_some_iff _).2 ⟨rfl, hw, rfl, rfl⟩)
        rw [hc, Option.bind_some]
        by_cases h1 : P.mul r.ray h = some s.ray
        · rw [P.psf_pos T _ h1, Option.bind_some]
          by_cases h2 : P.mul s.ray h' = some u.ray
          · rw [P.psf_pos T _ h2, Option.bind_some]
            obtain ⟨w', hw', hu⟩ := P.mul_assoc_some h1 h2
            rw [hw] at hw'
            cases hw'
            rw [P.psf_pos T _ hu]
            exact P.inc_supPair_mul T r s u h h' h1 h2
          · rw [P.psf_neg T _ h2, Option.bind_none, P.psf_neg T]
            intro hu
            change P.mul r.ray w = some u.ray at hu
            obtain ⟨s', hs1, hs2⟩ := P.mul_assoc_some_inv hw hu
            rw [h1] at hs1; cases hs1
            exact h2 hs2
        · rw [P.psf_neg T _ h1, Option.bind_none, P.psf_neg T]
          intro hu
          change P.mul r.ray w = some u.ray at hu
          obtain ⟨s', hs1, hs2⟩ := P.mul_assoc_some_inv hw hu
          apply h1
          rw [hs1]
          congr 1
          apply P.sep
          · rw [P.mul_src _ _ _ hs1, hT _ r.ray_mem, hT _ s.ray_mem]
          · rw [P.mul_tgt _ _ _ hs1]; exact hh2
          · change P.wt h = P.wt s.ray - P.wt r.ray at hg
            rw [P.wt_mul _ _ _ hs1, hg]; abel
    · rw [show (P.cover (P.psv T) P.wt P.wt_mul (P.psg T)).mul ⟨⟨⟨r, s, h⟩, hh1, hh2⟩, hg⟩
          ⟨⟨⟨s2, u, h'⟩, hh1', hh2'⟩, hg'⟩ = none by
        cases hc : (P.cover (P.psv T) P.wt P.wt_mul (P.psg T)).mul ⟨⟨⟨r, s, h⟩, hh1, hh2⟩, hg⟩
            ⟨⟨⟨s2, u, h'⟩, hh1', hh2'⟩, hg'⟩ with
        | none => rfl
        | some c => exact absurd (P.toMult.mulI_eq_some _ ((P.toMult.mulC_eq_some_iff (P.psv T) P.wt P.wt_mul (P.psg T)).1 hc)).1 hs]
      rw [Option.bind_none]
      by_cases h1 : P.mul r.ray h = some s.ray
      · rw [P.psf_pos T _ h1, Option.bind_some]
        by_cases h2 : P.mul s2.ray h' = some u.ray
        · rw [P.psf_pos T _ h2, Option.bind_some]
          simp [inc, supPair, hs]
        · rw [P.psf_neg T _ h2]; rfl
      · rw [P.psf_neg T _ h1]; rfl
  hid r := Or.inr ⟨r, P.psf_pos T ((P.cover (P.psv T) P.wt P.wt_mul (P.psg T)).e r) (P.mul_e r.ray)⟩
  hid' r := ⟨r, P.psf_pos T ((P.cover (P.psv T) P.wt P.wt_mul (P.psg T)).e r) (P.mul_e r.ray),
    fun r' h ↦ by
      change P.psf T _ = _ at h
      by_cases hm : P.mul r'.ray (P.e (P.tgt r'.ray)) = some r'.ray
      · rw [P.psf_pos T ((P.cover (P.psv T) P.wt P.wt_mul (P.psg T)).e r') hm] at h
        exact congrArg (fun p : IP (P.ProjSup T) ↦ p.1.1) (Option.some_injective _ h)
      · rw [P.psf_neg T _ hm] at h; exact absurd h (by simp)⟩

include hT in
/-- **Lemma 4.10 for a projective support**: its incidence algebra is representation-finite
when `kP` is. -/
theorem projSup_isRepresentationFinite (k : Type u) [Field k]
    (h : IsRepresentationFinite k (P.Lin k)) :
    IsRepresentationFinite k ((inc (P.ProjSup T)).Lin k) := by
  refine (P.projSupMor T hT).isRepresentationFinite k (fun p ↦ ?_)
    (P.cover_isRepresentationFinite k (P.psv T) P.wt P.wt_mul (P.psg T) h)
  obtain ⟨⟨a, b⟩, v, hv⟩ := p
  change P.mul a.ray v = some b.ray at hv
  refine ⟨⟨⟨⟨a, b, v⟩, (P.mul_mid _ _ _ hv).symm, (P.mul_tgt _ _ _ hv).symm⟩, by
    change P.wt v = P.wt b.ray - P.wt a.ray
    rw [P.wt_mul _ _ _ hv]; abel⟩, ?_⟩
  exact P.psf_pos T _ hv

end Supp

section ISupp

variable (T : Finset R)

/-- The faithful injective support on `T` (`def:faithful-support`), in the opposite of the
paper's order: `r ≤ s` if `r = v s` for a ray `v`. -/
def InjSup (_P : Tab V R L) (T : Finset R) : Type := {r : R // r ∈ T}

/-- The ray of a point of the injective support. -/
def InjSup.ray {P : Tab V R L} {T : Finset R} (a : P.InjSup T) : R := Subtype.val a

theorem InjSup.ray_mem {P : Tab V R L} {T : Finset R} (a : P.InjSup T) : a.ray ∈ T :=
  Subtype.property a

theorem InjSup.ext {P : Tab V R L} {T : Finset R} {a b : P.InjSup T} (h : a.ray = b.ray) :
    a = b := Subtype.ext h

/-- The point of the injective support at a ray. -/
def InjSup.mk {P : Tab V R L} {T : Finset R} (r : R) (h : r ∈ T) : P.InjSup T := ⟨r, h⟩

@[simp] theorem InjSup.ray_mk {P : Tab V R L} {T : Finset R} (r : R) (h : r ∈ T) :
    (InjSup.mk (P := P) r h).ray = r := rfl

instance : PartialOrder (P.InjSup T) where
  le a b := P.LF a.ray b.ray
  le_refl a := P.lf_refl a.ray
  le_trans _ _ _ := P.lf_trans
  le_antisymm a b h1 h2 := InjSup.ext (P.lf_antisymm h1 h2)

instance : Fintype (P.InjSup T) := inferInstanceAs (Fintype {r : R // r ∈ T})

instance : DecidableEq (P.InjSup T) := inferInstanceAs (DecidableEq {r : R // r ∈ T})

noncomputable instance : DecidableLE (P.InjSup T) := Classical.decRel _

noncomputable instance : DecidableLT (P.InjSup T) := Classical.decRel _

noncomputable instance : LocallyFiniteOrder (P.InjSup T) := Fintype.toLocallyFiniteOrder

theorem injSup_le_iff (a b : P.InjSup T) : a ≤ b ↔ ∃ v, P.mul v b.ray = some a.ray := Iff.rfl

variable {x : V} (hT : ∀ r ∈ T, P.tgt r = x)

/-- The labels of the injective support: `(src r, -wt r)`. -/
abbrev isv : P.InjSup T → V := fun r ↦ P.src r.ray

/-- The weights of the injective support. -/
abbrev isg : P.InjSup T → L := fun r ↦ -P.wt r.ray

/-- A comparable pair of the injective support from a factorization. -/
def isupPair (a b : P.InjSup T) (v : R) (hm : P.mul v b.ray = some a.ray) : IP (P.InjSup T) :=
  ⟨(a, b), (P.injSup_le_iff T a b).2 ⟨v, hm⟩⟩

/-- The rays of the graded cover of the injective support. -/
abbrev ICR := Mult.CR P.toMult (P.isv T) P.wt (P.isg T)

/-- The action on `H(-, X)`. -/
def isf (t : P.ICR T) : Option (IP (P.InjSup T)) :=
  if hm : P.mul t.1.1.2.2 t.1.1.2.1.ray = some t.1.1.1.ray then
    some (P.isupPair T t.1.1.1 t.1.1.2.1 t.1.1.2.2 hm) else none

theorem isf_pos (t : P.ICR T) (hm : P.mul t.1.1.2.2 t.1.1.2.1.ray = some t.1.1.1.ray) :
    P.isf T t = some (P.isupPair T t.1.1.1 t.1.1.2.1 t.1.1.2.2 hm) := dif_pos hm

theorem isf_neg (t : P.ICR T) (hm : ¬ P.mul t.1.1.2.2 t.1.1.2.1.ray = some t.1.1.1.ray) :
    P.isf T t = none := dif_neg hm

theorem inc_isupPair_mul (a b c : P.InjSup T) (v v' : R) (h1 h2) :
    (inc (P.InjSup T)).mul (P.isupPair T a b v h1) (P.isupPair T b c v' h2) =
      some ⟨(a, c), le_trans ((P.injSup_le_iff T a b).2 ⟨v, h1⟩)
        ((P.injSup_le_iff T b c).2 ⟨v', h2⟩)⟩ := inc_mul_of rfl

include hT in
/-- The action on `H(-, X)` as a table morphism onto the incidence table. -/
def injSupMor : Mor (P.cover (P.isv T) P.wt P.wt_mul (P.isg T)) (inc (P.InjSup T)) where
  f := P.isf T
  hmul t t' := by
    obtain ⟨⟨⟨a, b, h⟩, hh1, hh2⟩, hg⟩ := t
    obtain ⟨⟨⟨b2, c, h'⟩, hh1', hh2'⟩, hg'⟩ := t'
    by_cases hs : b = b2
    · subst hs
      cases hw : P.mul h h' with
      | none =>
        have hC0 : (P.cover (P.isv T) P.wt P.wt_mul (P.isg T)).mul ⟨⟨⟨a, b, h⟩, hh1, hh2⟩, hg⟩
            ⟨⟨⟨b, c, h'⟩, hh1', hh2'⟩, hg'⟩ = none := by
          cases hc : (P.cover (P.isv T) P.wt P.wt_mul (P.isg T)).mul ⟨⟨⟨a, b, h⟩, hh1, hh2⟩, hg⟩
              ⟨⟨⟨b, c, h'⟩, hh1', hh2'⟩, hg'⟩ with
          | none => rfl
          | some d =>
            have := (P.toMult.mulI_eq_some _ ((P.toMult.mulC_eq_some_iff (P.isv T) P.wt P.wt_mul
              (P.isg T)).1 hc)).2.1
            rw [hw] at this; exact absurd this (by simp)
        rw [hC0, Option.bind_none]
        by_cases h1 : P.mul h b.ray = some a.ray
        · rw [P.isf_pos T _ h1, Option.bind_some]
          by_cases h2 : P.mul h' c.ray = some b.ray
          · obtain ⟨w, hw', -⟩ := P.mul_assoc_some' h2 h1
            rw [hw] at hw'; exact absurd hw' (by simp)
          · rw [P.isf_neg T _ h2]; rfl
        · rw [P.isf_neg T _ h1]; rfl
      | some w =>
        have hc : (P.cover (P.isv T) P.wt P.wt_mul (P.isg T)).mul ⟨⟨⟨a, b, h⟩, hh1, hh2⟩, hg⟩
            ⟨⟨⟨b, c, h'⟩, hh1', hh2'⟩, hg'⟩ = some ⟨⟨⟨a, c, w⟩,
              by rw [P.mul_src _ _ _ hw]; exact hh1, by rw [P.mul_tgt _ _ _ hw]; exact hh2'⟩,
              by
                change P.wt w = -P.wt c.ray - -P.wt a.ray
                change P.wt h = -P.wt b.ray - -P.wt a.ray at hg
                change P.wt h' = -P.wt c.ray - -P.wt b.ray at hg'
                rw [P.wt_mul _ _ _ hw, hg, hg']; abel⟩ :=
          (P.toMult.mulC_eq_some_iff (P.isv T) P.wt P.wt_mul (P.isg T)).2
            ((P.toMult.mulI_eq_some_iff _).2 ⟨rfl, hw, rfl, rfl⟩)
        rw [hc, Option.bind_some]
        by_cases h1 : P.mul h b.ray = some a.ray
        · rw [P.isf_pos T _ h1, Option.bind_some]
          by_cases h2 : P.mul h' c.ray = some b.ray
          · rw [P.isf_pos T _ h2, Option.bind_some]
            obtain ⟨w', hw', hu⟩ := P.mul_assoc_some' h2 h1
            rw [hw] at hw'
            cases hw'
            rw [P.isf_pos T _ hu]
            exact P.inc_isupPair_mul T a b c h h' h1 h2
          · rw [P.isf_neg T _ h2, Option.bind_none, P.isf_neg T]
            intro hu
            change P.mul w c.ray = some a.ray at hu
            obtain ⟨s', hs1, hs2⟩ := P.mul_assoc_some_inv' hw hu
            apply h2
            rw [hs1]
            congr 1
            apply P.sep
            · rw [P.mul_src _ _ _ hs1]; exact hh1'
            · rw [P.mul_tgt _ _ _ hs1, hT _ c.ray_mem, hT _ b.ray_mem]
            · change P.wt h' = -P.wt c.ray - -P.wt b.ray at hg'
              rw [P.wt_mul _ _ _ hs1, hg']; abel
        · rw [P.isf_neg T _ h1, Option.bind_none, P.isf_neg T]
          intro hu
          change P.mul w c.ray = some a.ray at hu
          obtain ⟨s', hs1, hs2⟩ := P.mul_assoc_some_inv' hw hu
          apply h1
          have : s' = b.ray := by
            apply P.sep
            · rw [P.mul_src _ _ _ hs1]; exact hh1'
            · rw [P.mul_tgt _ _ _ hs1, hT _ c.ray_mem, hT _ b.ray_mem]
            · change P.wt h' = -P.wt c.ray - -P.wt b.ray at hg'
              rw [P.wt_mul _ _ _ hs1, hg']; abel
          rw [← this]; exact hs2
    · rw [show (P.cover (P.isv T) P.wt P.wt_mul (P.isg T)).mul ⟨⟨⟨a, b, h⟩, hh1, hh2⟩, hg⟩
          ⟨⟨⟨b2, c, h'⟩, hh1', hh2'⟩, hg'⟩ = none by
        cases hc : (P.cover (P.isv T) P.wt P.wt_mul (P.isg T)).mul ⟨⟨⟨a, b, h⟩, hh1, hh2⟩, hg⟩
            ⟨⟨⟨b2, c, h'⟩, hh1', hh2'⟩, hg'⟩ with
        | none => rfl
        | some d => exact absurd (P.toMult.mulI_eq_some _ ((P.toMult.mulC_eq_some_iff (P.isv T)
            P.wt P.wt_mul (P.isg T)).1 hc)).1 hs]
      rw [Option.bind_none]
      by_cases h1 : P.mul h b.ray = some a.ray
      · rw [P.isf_pos T _ h1, Option.bind_some]
        by_cases h2 : P.mul h' c.ray = some b2.ray
        · rw [P.isf_pos T _ h2, Option.bind_some]
          simp [inc, isupPair, hs]
        · rw [P.isf_neg T _ h2]; rfl
      · rw [P.isf_neg T _ h1]; rfl
  hid r := Or.inr ⟨r, P.isf_pos T ((P.cover (P.isv T) P.wt P.wt_mul (P.isg T)).e r) (P.e_mul r.ray)⟩
  hid' r := ⟨r, P.isf_pos T ((P.cover (P.isv T) P.wt P.wt_mul (P.isg T)).e r) (P.e_mul r.ray),
    fun r' h ↦ by
      change P.isf T _ = _ at h
      by_cases hm : P.mul (P.e (P.src r'.ray)) r'.ray = some r'.ray
      · rw [P.isf_pos T ((P.cover (P.isv T) P.wt P.wt_mul (P.isg T)).e r') hm] at h
        exact congrArg (fun p : IP (P.InjSup T) ↦ p.1.1) (Option.some_injective _ h)
      · rw [P.isf_neg T _ hm] at h; exact absurd h (by simp)⟩

include hT in
/-- **Lemma 4.10 for an injective support.** -/
theorem injSup_isRepresentationFinite (k : Type u) [Field k]
    (h : IsRepresentationFinite k (P.Lin k)) :
    IsRepresentationFinite k ((inc (P.InjSup T)).Lin k) := by
  refine (P.injSupMor T hT).isRepresentationFinite k (fun p ↦ ?_)
    (P.cover_isRepresentationFinite k (P.isv T) P.wt P.wt_mul (P.isg T) h)
  obtain ⟨⟨a, b⟩, v, hv⟩ := p
  change P.mul v b.ray = some a.ray at hv
  refine ⟨⟨⟨⟨a, b, v⟩, (P.mul_src _ _ _ hv).symm, P.mul_mid _ _ _ hv⟩, by
    change P.wt v = -P.wt b.ray - -P.wt a.ray
    rw [P.wt_mul _ _ _ hv]; abel⟩, ?_⟩
  exact P.isf_pos T _ hv

end ISupp

end Tab

end RaySys

end MultiplicativeBasisDeformations
