import MultiplicativeBasisDeformations.Foundations.IntegralLifting
import MultiplicativeBasisDeformations.Foundations.SplitTransfer

/-!
# Lemma 9.2: the centralizer ray algebra `B_χ`

`lem:centralizer-ray-algebra` (`integral-partial-lifts.tex`). The centralizer
`C_χ = Cent_{A₀}(q̂)` is spanned by the identities, the two-sided rays and the unshiftable
rays; `B_χ = C_χ/𝔞_χ` has basis the supporting identities and the two-sided rays, with the
products of `A₀` (zero when the product leaves the basis). We record these as ray tables
`Tc` (the centralizer) and `Qχ` (the two-sided table) with morphisms `Tc → P` (inclusion)
and `Tc → Qχ` (quotient), and the projection `π : kP → kQχ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Tab

variable {V R L : Type} [AddCommGroup L] (P : Tab V R L)

/-- Data for a sub-table: selected vertices and rays, closed enough for associativity. -/
structure SubData where
  pV : V → Prop
  pR : R → Prop
  e_mem : ∀ x, pV x → pR (P.e x)
  src_mem : ∀ r, pR r → pV (P.src r)
  tgt_mem : ∀ r, pR r → pV (P.tgt r)
  cc : ∀ r s u t v w, pR r → pR s → pR u → P.mul r s = some t → P.mul t u = some w →
    P.mul s u = some v → pR w → (pR t ↔ pR v)

variable {P} (D : P.SubData)

open Classical in
/-- The restricted product: zero when the product leaves the selected rays. -/
def subMul (r s : {r // D.pR r}) : Option {r // D.pR r} :=
  (P.mul r.1 s.1).bind fun t ↦ if h : D.pR t then some ⟨t, h⟩ else none

theorem subMul_eq_some {r s : {r // D.pR r}} {t : {r // D.pR r}} :
    subMul D r s = some t ↔ P.mul r.1 s.1 = some t.1 := by
  classical
  unfold subMul
  cases h : P.mul r.1 s.1 with
  | none => simp
  | some t' =>
    simp only [Option.bind_some, Option.some.injEq]
    by_cases ht : D.pR t'
    · rw [dif_pos ht, Option.some.injEq]
      constructor
      · rintro rfl; rfl
      · intro e; exact Subtype.ext e
    · rw [dif_neg ht]
      simp only [reduceCtorEq, false_iff]
      intro e; subst e; exact ht t.2

theorem subMul_assoc (r s u : {r // D.pR r}) :
    (subMul D r s).bind (fun t ↦ subMul D t u) = (subMul D s u).bind (fun t ↦ subMul D r t) := by
  classical
  have hA := P.assoc r.1 s.1 u.1
  cases hrs : P.mul r.1 s.1 with
  | none =>
    have e1 : subMul D r s = none := by unfold subMul; rw [hrs]; rfl
    rw [e1, Option.bind_none]
    rw [hrs, Option.bind_none] at hA
    cases hsu : subMul D s u with
    | none => rfl
    | some v =>
      have hv := (subMul_eq_some D).1 hsu
      rw [hv, Option.bind_some] at hA
      simp only [Option.bind_some]
      unfold subMul; rw [← hA]; rfl
  | some t =>
    rw [hrs, Option.bind_some] at hA
    by_cases ht : D.pR t
    · have e1 : subMul D r s = some ⟨t, ht⟩ := (subMul_eq_some D).2 hrs
      rw [e1, Option.bind_some]
      cases htu : P.mul t u.1 with
      | none =>
        have e2 : subMul D ⟨t, ht⟩ u = none := by unfold subMul; rw [htu]; rfl
        rw [e2]
        rw [htu] at hA
        cases hsu : subMul D s u with
        | none => rfl
        | some v =>
          have hv := (subMul_eq_some D).1 hsu
          rw [hv, Option.bind_some] at hA
          simp only [Option.bind_some]
          unfold subMul; rw [← hA]; rfl
      | some w =>
        rw [htu] at hA
        cases hsu' : P.mul s.1 u.1 with
        | none => rw [hsu', Option.bind_none] at hA; cases hA
        | some v' =>
          rw [hsu', Option.bind_some] at hA
          by_cases hw : D.pR w
          · have hv' := (D.cc _ _ _ _ _ _ r.2 s.2 u.2 hrs htu hsu' hw).1 ht
            have e2 : subMul D ⟨t, ht⟩ u = some ⟨w, hw⟩ := (subMul_eq_some D).2 htu
            have e3 : subMul D s u = some ⟨v', hv'⟩ := (subMul_eq_some D).2 hsu'
            have e4 : subMul D r ⟨v', hv'⟩ = some ⟨w, hw⟩ := (subMul_eq_some D).2 hA.symm
            rw [e2, e3, Option.bind_some, e4]
          · have e2 : subMul D ⟨t, ht⟩ u = none := by unfold subMul; rw [htu]; simp [hw]
            rw [e2]
            cases hsu : subMul D s u with
            | none => rfl
            | some v =>
              have hv := (subMul_eq_some D).1 hsu
              rw [hsu'] at hv
              cases hv
              simp only [Option.bind_some]
              unfold subMul; rw [← hA]; simp [hw]
    · have e1 : subMul D r s = none := by unfold subMul; rw [hrs]; simp [ht]
      rw [e1, Option.bind_none]
      cases hsu : subMul D s u with
      | none => rfl
      | some v =>
        have hv := (subMul_eq_some D).1 hsu
        simp only [Option.bind_some]
        cases hrv : subMul D r v with
        | none => rfl
        | some w =>
          exfalso
          have hw := (subMul_eq_some D).1 hrv
          rw [hv, Option.bind_some, hw] at hA
          exact ht ((D.cc _ _ _ _ _ _ r.2 s.2 u.2 hrs hA hv w.2).2 v.2)

/-- **The sub-table.** -/
def sub : Tab {x // D.pV x} {r // D.pR r} L where
  src r := ⟨P.src r.1, D.src_mem r.1 r.2⟩
  tgt r := ⟨P.tgt r.1, D.tgt_mem r.1 r.2⟩
  e x := ⟨P.e x.1, D.e_mem x.1 x.2⟩
  src_e x := Subtype.ext (P.src_e x.1)
  tgt_e x := Subtype.ext (P.tgt_e x.1)
  mul := subMul D
  mul_src r s t h := Subtype.ext (P.mul_src _ _ _ ((subMul_eq_some D).1 h))
  mul_tgt r s t h := Subtype.ext (P.mul_tgt _ _ _ ((subMul_eq_some D).1 h))
  mul_mid r s t h := Subtype.ext (P.mul_mid _ _ _ ((subMul_eq_some D).1 h))
  e_mul r := (subMul_eq_some D).2 (P.e_mul r.1)
  mul_e r := (subMul_eq_some D).2 (P.mul_e r.1)
  assoc := subMul_assoc D
  wt r := P.wt r.1
  wt_mul r s t h := P.wt_mul _ _ _ ((subMul_eq_some D).1 h)
  deg := P.deg
  deg_pos r h := P.deg_pos r.1 (fun h' ↦ h (Subtype.ext h'))
  sep r r' h1 h2 h3 := Subtype.ext (P.sep _ _ (congrArg Subtype.val h1) (congrArg Subtype.val h2) h3)

end Tab

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L)

local notation:max "⌜" r "⌝" => Sys.rr S r

variable {χ : L}

/-- Rays of the centralizer: two-sided or unshiftable. -/
def InC (χ : L) (r : R) : Prop := S.TB χ r ∨ ¬ S.Shift χ r

theorem e_inC (x : V) : S.InC χ (S.P.e x) := Or.inr fun h ↦ h.1 (by rw [S.P.src_e])

/-- **The centralizer is closed under products** (`integral-partial-lifts.tex`). -/
theorem inC_mul (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {r s t : R} (hr : S.InC χ r)
    (hs : S.InC χ s) (h : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) : S.InC χ t := by
  by_cases ht : S.Shift χ t
  swap
  · exact Or.inr ht
  have h1 := S.src_of_mul_ne (by rw [h]; exact S.rr_ne t)
  by_cases hr0 : r = S.P.e (S.P.src r)
  · have hsr : S.P.src s = S.P.src r := by rw [← h1]; nth_rewrite 1 [hr0]; rw [S.P.tgt_e]
    rw [show ⌜r⌝ = ⌜S.P.e (S.P.src r)⌝ from congrArg _ hr0, S.e_mul_rr' s hsr] at h
    rw [← S.rr_inj h]; exact hs
  by_cases hs0 : s = S.P.e (S.P.src s)
  · rw [show ⌜s⌝ = ⌜S.P.e (S.P.src s)⌝ from congrArg _ hs0, ← h1, S.rr_mul_e] at h
    rw [← S.rr_inj h]; exact hr
  rcases S.types_of_shift hχ hprim ht with hT | hT | hT
  · exfalso
    rcases S.table_L hχ hprim hr0 hs0 h hT with ⟨hTr, -⟩ | ⟨-, hTs, -⟩
    · rcases hr with hr | hr
      · exact hr.2.2 hTr.2.2
      · exact hr hTr.1
    · rcases hs with hs | hs
      · exact hs.2.2 hTs.2.2
      · exact hs hTs.1
  · exfalso
    rcases S.table_R hχ hprim hr0 hs0 h hT with ⟨hTs, -⟩ | ⟨-, hTr, -⟩
    · rcases hs with hs | hs
      · exact hs.2.1 hTs.2.1
      · exact hs hTs.1
    · rcases hr with hr | hr
      · exact hr.2.1 hTr.2.1
      · exact hr hTr.1
  · exact Or.inl hT

/-- Rays of `B_χ`: two-sided rays and supporting identities. -/
def InQ (χ : L) (r : R) : Prop := S.TB χ r ∨ (r = S.P.e (S.P.src r) ∧ S.Supp χ (S.P.src r))

theorem inQ_src {r : R} (h : S.InQ χ r) : S.Supp χ (S.P.src r) := by
  rcases h with h | h
  · exact S.supp_of_qh h.2.1
  · exact h.2

theorem inQ_tgt {r : R} (h : S.InQ χ r) : S.Supp χ (S.P.tgt r) := by
  rcases h with h | ⟨h1, h2⟩
  · exact S.supp_of_qh' h.2.2
  · rw [h1, S.P.tgt_e]; exact h2

theorem inQ_inC {r : R} (h : S.InQ χ r) : S.InC χ r := by
  rcases h with h | ⟨h1, -⟩
  · exact Or.inl h
  · rw [h1]; exact S.e_inC _

/-- A retained product has retained factors when one factor lies in the centralizer
(`integral-partial-lifts.tex`). -/
theorem inQ_of_mul (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {r s t : R} (hrs : S.InC χ r ∨ S.InC χ s)
    (h : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) (ht : S.InQ χ t) : S.InQ χ r ∧ S.InQ χ s := by
  obtain ⟨t1, t2, t3, t4⟩ := S.prod_of h
  have h1 := S.src_of_mul_ne (by rw [h]; exact S.rr_ne t)
  by_cases hr0 : r = S.P.e (S.P.src r)
  · have hsr : S.P.src s = S.P.src r := by rw [← h1]; nth_rewrite 1 [hr0]; rw [S.P.tgt_e]
    rw [show ⌜r⌝ = ⌜S.P.e (S.P.src r)⌝ from congrArg _ hr0, S.e_mul_rr' s hsr] at h
    have := S.rr_inj h; subst this
    exact ⟨Or.inr ⟨hr0, by rw [← hsr]; exact S.inQ_src ht⟩, ht⟩
  by_cases hs0 : s = S.P.e (S.P.src s)
  · rw [show ⌜s⌝ = ⌜S.P.e (S.P.src s)⌝ from congrArg _ hs0, ← h1, S.rr_mul_e] at h
    have := S.rr_inj h; subst this
    exact ⟨ht, Or.inr ⟨hs0, by rw [← h1]; exact S.inQ_tgt ht⟩⟩
  rcases ht with hB | ⟨he, -⟩
  · rcases (S.table_B hχ hprim hr0 hs0 h hB).1 with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · exact ⟨Or.inl h2, Or.inl h3⟩
    · exfalso
      rcases hrs with hr | hs
      · rcases hr with hr | hr
        · exact hr.2.2 h2.2.2
        · exact hr h2.1
      · rcases hs with hs | hs
        · exact hs.2.1 h3.2.1
        · exact hs h3.1
  · exfalso
    have := S.P.deg_pos r hr0
    have := S.P.deg_nonneg s
    have e := congrArg S.P.deg t4
    rw [he, S.P.wt_e, map_zero, map_add] at e
    linarith

/-- The centralizer sub-table data. -/
def cData (hχ : 0 < S.P.deg χ) (hprim : Prim χ) : S.P.SubData where
  pV _ := True
  pR := S.InC χ
  e_mem x _ := S.e_inC x
  src_mem _ _ := trivial
  tgt_mem _ _ := trivial
  cc r s u t v w hr hs hu hrs htu hsu _ :=
    ⟨fun _ ↦ S.inC_mul hχ hprim hs hu (S.P.rr_mul_rr_eq_rr.2 hsu),
      fun _ ↦ S.inC_mul hχ hprim hr hs (S.P.rr_mul_rr_eq_rr.2 hrs)⟩

/-- The two-sided sub-table data (`Q_χ`). -/
def qData (hχ : 0 < S.P.deg χ) (hprim : Prim χ) : S.P.SubData where
  pV := S.Supp χ
  pR := S.InQ χ
  e_mem x hx := Or.inr ⟨by rw [S.P.src_e], by rw [S.P.src_e]; exact hx⟩
  src_mem r h := S.inQ_src h
  tgt_mem r h := S.inQ_tgt h
  cc r s u t v w hr hs hu hrs htu hsu hw := by
    have hA := S.P.assoc r s u
    rw [hrs, hsu, Option.bind_some, Option.bind_some, htu] at hA
    exact ⟨fun _ ↦ (S.inQ_of_mul hχ hprim (Or.inl (S.inQ_inC hr))
        (S.P.rr_mul_rr_eq_rr.2 hA.symm) hw).2,
      fun _ ↦ (S.inQ_of_mul hχ hprim (Or.inr (S.inQ_inC hu))
        (S.P.rr_mul_rr_eq_rr.2 htu) hw).1⟩

/-- The centralizer table `Tc`. -/
def Tc (hχ : 0 < S.P.deg χ) (hprim : Prim χ) := S.P.sub (S.cData hχ hprim)

/-- The two-sided table `Q_χ`; `B_χ = kQ_χ`. -/
def Qχ (hχ : 0 < S.P.deg χ) (hprim : Prim χ) := S.P.sub (S.qData hχ hprim)

variable (hχ : 0 < S.P.deg χ) (hprim : Prim χ)

/-- The inclusion `Tc → P`. -/
def incl : Mor (S.Tc hχ hprim).toMult S.P.toMult where
  f r := some r.1
  hmul r s := by
    classical
    simp only [Option.bind_some]
    change S.P.mul r.1 s.1 = (Tab.subMul (S.cData hχ hprim) r s).bind _
    cases h : S.P.mul r.1 s.1 with
    | none => unfold Tab.subMul; rw [h]; rfl
    | some t =>
      have ht : S.InC χ t := S.inC_mul hχ hprim r.2 s.2 (S.P.rr_mul_rr_eq_rr.2 h)
      rw [(Tab.subMul_eq_some (S.cData hχ hprim) (t := ⟨t, ht⟩)).2 h]; rfl
  hid x := Or.inr ⟨x.1, rfl⟩
  hid' x' := ⟨⟨x', trivial⟩, rfl, fun y h ↦ by
    simp only [Option.some.injEq] at h
    exact Subtype.ext (by
      have := congrArg S.P.src h
      change S.P.src (S.P.e y.1) = S.P.src (S.P.e x') at this
      rwa [S.P.src_e, S.P.src_e] at this)⟩

open Classical in
/-- The quotient `Tc → Q_χ`. -/
def quot : Mor (S.Tc hχ hprim).toMult (S.Qχ hχ hprim).toMult where
  f r := if h : S.InQ χ r.1 then some ⟨r.1, h⟩ else none
  hmul r s := by
    change ((if h : S.InQ χ r.1 then some ⟨r.1, h⟩ else none).bind fun a ↦
      (if h : S.InQ χ s.1 then some ⟨s.1, h⟩ else none).bind fun c ↦
        Tab.subMul (S.qData hχ hprim) a c) =
      (Tab.subMul (S.cData hχ hprim) r s).bind fun t ↦
        if h : S.InQ χ t.1 then some ⟨t.1, h⟩ else none
    cases h : S.P.mul r.1 s.1 with
    | none =>
      have e1 : Tab.subMul (S.cData hχ hprim) r s = none := by unfold Tab.subMul; rw [h]; rfl
      rw [e1, Option.bind_none]
      by_cases hr : S.InQ χ r.1
      · by_cases hs : S.InQ χ s.1
        · simp only [dif_pos hr, dif_pos hs, Option.bind_some]
          unfold Tab.subMul; change (S.P.mul r.1 s.1).bind _ = _; rw [h]; rfl
        · simp only [dif_pos hr, dif_neg hs, Option.bind_some, Option.bind_none]
      · simp only [dif_neg hr, Option.bind_none]
    | some t =>
      have ht : S.InC χ t := S.inC_mul hχ hprim r.2 s.2 (S.P.rr_mul_rr_eq_rr.2 h)
      have e1 : Tab.subMul (S.cData hχ hprim) r s = some ⟨t, ht⟩ :=
        (Tab.subMul_eq_some (S.cData hχ hprim)).2 h
      rw [e1, Option.bind_some]
      by_cases htq : S.InQ χ t
      · obtain ⟨hr, hs⟩ := S.inQ_of_mul hχ hprim (Or.inl r.2) (S.P.rr_mul_rr_eq_rr.2 h) htq
        simp only [dif_pos hr, dif_pos hs, dif_pos htq, Option.bind_some]
        exact (Tab.subMul_eq_some (S.qData hχ hprim) (t := ⟨t, htq⟩)).2 h
      · simp only [dif_neg htq]
        by_cases hr : S.InQ χ r.1
        · by_cases hs : S.InQ χ s.1
          · simp only [dif_pos hr, dif_pos hs, Option.bind_some]
            unfold Tab.subMul; change (S.P.mul r.1 s.1).bind _ = _; rw [h, Option.bind_some]
            rw [dif_neg (show ¬ (S.qData hχ hprim).pR t from htq)]
          · simp only [dif_pos hr, dif_neg hs, Option.bind_some, Option.bind_none]
        · simp only [dif_neg hr, Option.bind_none]
  hid x := by
    by_cases hx : S.Supp χ x.1
    · refine Or.inr ⟨⟨x.1, hx⟩, ?_⟩
      have h : S.InQ χ ((S.Tc hχ hprim).e x).1 :=
        Or.inr ⟨by change S.P.e x.1 = S.P.e (S.P.src (S.P.e x.1)); rw [S.P.src_e],
          by change S.Supp χ (S.P.src (S.P.e x.1)); rw [S.P.src_e]; exact hx⟩
      simp only [dif_pos h]; rfl
    · left
      have h : ¬ S.InQ χ ((S.Tc hχ hprim).e x).1 := fun h' ↦ hx (by
        have := S.inQ_src h'; change S.Supp χ (S.P.src (S.P.e x.1)) at this
        rwa [S.P.src_e] at this)
      simp only [dif_neg h]
  hid' x' := by
    have h : S.InQ χ (S.P.e x'.1) :=
      Or.inr ⟨by rw [S.P.src_e], by rw [S.P.src_e]; exact x'.2⟩
    refine ⟨⟨x'.1, trivial⟩, ?_, fun y hy ↦ ?_⟩
    · dsimp only
      rw [dif_pos (show S.InQ χ ((S.Tc hχ hprim).e ⟨x'.1, trivial⟩).1 from h)]; rfl
    · dsimp only at hy
      split_ifs at hy with h'
      simp only [Option.some.injEq] at hy
      have := congrArg (fun r : {r // S.InQ χ r} ↦ S.P.src r.1) hy
      change S.P.src (S.P.e y.1) = S.P.src (S.P.e x'.1) at this
      rw [S.P.src_e, S.P.src_e] at this
      exact Subtype.ext this

variable (k : Type u) [Field k]

open Classical

/-- The projection `π : kP → kQ_χ` onto the retained rays. -/
def proj : S.P.Lin k →ₗ[k] (S.Qχ hχ hprim).Lin k :=
  (S.P.basis k).constr k fun r ↦ if h : S.InQ χ r then (S.Qχ hχ hprim).b k ⟨r, h⟩ else 0

theorem proj_b (r : R) : S.proj hχ hprim k (S.P.b k r) =
    if h : S.InQ χ r then (S.Qχ hχ hprim).b k ⟨r, h⟩ else 0 := by
  classical
  rw [proj, ← Mult.basis_apply, Module.Basis.constr_basis]

theorem quot_b (r : {r // (S.cData hχ hprim).pR r}) :
    (S.quot hχ hprim).alg k ((S.Tc hχ hprim).b k r) =
      if h : S.InQ χ r.1 then (S.Qχ hχ hprim).b k ⟨r.1, h⟩ else 0 := by
  have := Mor.alg_b (S.quot hχ hprim) k r
  rw [this]
  change ((if h : S.InQ χ r.1 then some ⟨r.1, h⟩ else none : Option {r // S.InQ χ r}).elim 0
    ((S.Qχ hχ hprim).b k)) = _
  split_ifs <;> rfl

theorem incl_b (r : {r // (S.cData hχ hprim).pR r}) :
    (S.incl hχ hprim).alg k ((S.Tc hχ hprim).b k r) = S.P.b k r.1 := by
  have := Mor.alg_b (S.incl hχ hprim) k r
  rw [this]; rfl

/-- The product of two retained basis vectors of `kQ_χ`. -/
theorem Qb_mul {r s : R} (hr : S.InQ χ r) (hs : S.InQ χ s) :
    (S.Qχ hχ hprim).b k ⟨r, hr⟩ * (S.Qχ hχ hprim).b k ⟨s, hs⟩ =
      match S.P.mul r s with
      | some t => if h : S.InQ χ t then (S.Qχ hχ hprim).b k ⟨t, h⟩ else 0
      | none => 0 := by
  classical
  rw [Mult.b_mul]
  cases h : S.P.mul r s with
  | none =>
    have : (S.Qχ hχ hprim).mul ⟨r, hr⟩ ⟨s, hs⟩ = none := by
      change Tab.subMul _ _ _ = none; unfold Tab.subMul; rw [h]; rfl
    rw [this]; rfl
  | some t =>
    by_cases ht : S.InQ χ t
    · have : (S.Qχ hχ hprim).mul ⟨r, hr⟩ ⟨s, hs⟩ = some ⟨t, ht⟩ :=
        (Tab.subMul_eq_some (S.qData hχ hprim)).2 h
      rw [this]; simp [dif_pos ht]
    · have : (S.Qχ hχ hprim).mul ⟨r, hr⟩ ⟨s, hs⟩ = none := by
        change Tab.subMul _ _ _ = none; unfold Tab.subMul; rw [h, Option.bind_some]
        rw [dif_neg (show ¬ (S.qData hχ hprim).pR t from ht)]
      rw [this]; simp [dif_neg ht]

/-- `π(c b) = q(c) π(b)` (the retained-product analysis). -/
theorem proj_left (x : (S.Tc hχ hprim).Lin k) (y : S.P.Lin k) :
    S.proj hχ hprim k ((S.incl hχ hprim).alg k x * y) =
      (S.quot hχ hprim).alg k x * S.proj hχ hprim k y := by
  have key : ((LinearMap.mul k (S.P.Lin k)).compl₁₂ ((S.incl hχ hprim).alg k).toLinearMap
      LinearMap.id).compr₂ (S.proj hχ hprim k) =
      (LinearMap.mul k ((S.Qχ hχ hprim).Lin k)).compl₁₂ ((S.quot hχ hprim).alg k).toLinearMap
        (S.proj hχ hprim k) := by
    refine (S.Tc hχ hprim).basis k |>.ext fun r ↦ (S.P.basis k).ext fun t ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      AlgHom.toLinearMap_apply, LinearMap.id_coe, id_eq, Mult.basis_apply]
    rw [S.incl_b, S.quot_b, Mult.b_mul, S.proj_b]
    cases h : S.P.mul r.1 t with
    | none =>
      simp only [Option.elim_none, map_zero]
      split_ifs with h1 h2 <;> first | (rw [S.Qb_mul, h]) | simp
    | some w =>
      simp only [Option.elim_some, S.proj_b]
      by_cases hw : S.InQ χ w
      · obtain ⟨h1, h2⟩ := S.inQ_of_mul hχ hprim (Or.inl r.2) (S.P.rr_mul_rr_eq_rr.2 h) hw
        rw [dif_pos hw, dif_pos h1, dif_pos h2, S.Qb_mul, h]; simp [dif_pos hw]
      · rw [dif_neg hw]
        split_ifs with h1 h2 <;> first | (rw [S.Qb_mul, h]; simp [dif_neg hw]) | simp
  exact congrArg (fun F ↦ F x y) key

/-- `π(b c) = π(b) q(c)`. -/
theorem proj_right (y : S.P.Lin k) (x : (S.Tc hχ hprim).Lin k) :
    S.proj hχ hprim k (y * (S.incl hχ hprim).alg k x) =
      S.proj hχ hprim k y * (S.quot hχ hprim).alg k x := by
  have key : ((LinearMap.mul k (S.P.Lin k)).compl₁₂ LinearMap.id
      ((S.incl hχ hprim).alg k).toLinearMap).compr₂ (S.proj hχ hprim k) =
      (LinearMap.mul k ((S.Qχ hχ hprim).Lin k)).compl₁₂ (S.proj hχ hprim k)
        ((S.quot hχ hprim).alg k).toLinearMap := by
    refine (S.P.basis k).ext fun t ↦ (S.Tc hχ hprim).basis k |>.ext fun r ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      AlgHom.toLinearMap_apply, LinearMap.id_coe, id_eq, Mult.basis_apply]
    rw [S.incl_b, S.quot_b, Mult.b_mul, S.proj_b]
    cases h : S.P.mul t r.1 with
    | none =>
      simp only [Option.elim_none, map_zero]
      split_ifs with h1 h2 <;> first | (rw [S.Qb_mul, h]) | simp
    | some w =>
      simp only [Option.elim_some, S.proj_b]
      by_cases hw : S.InQ χ w
      · obtain ⟨h1, h2⟩ := S.inQ_of_mul hχ hprim (Or.inr r.2) (S.P.rr_mul_rr_eq_rr.2 h) hw
        rw [dif_pos hw, dif_pos h1, dif_pos h2, S.Qb_mul, h]; simp [dif_pos hw]
      · rw [dif_neg hw]
        split_ifs with h1 h2 <;> first | (rw [S.Qb_mul, h]; simp [dif_neg hw]) | simp
  exact congrArg (fun F ↦ F y x) key

theorem incl_injective : Function.Injective ((S.incl hχ hprim).alg k) := by
  -- a left inverse on the basis
  let ret : S.P.Lin k →ₗ[k] (S.Tc hχ hprim).Lin k :=
    (S.P.basis k).constr k fun r ↦
      if h : (S.cData hχ hprim).pR r then (S.Tc hχ hprim).b k ⟨r, h⟩ else 0
  have hret : ret.comp ((S.incl hχ hprim).alg k).toLinearMap = LinearMap.id := by
    refine ((S.Tc hχ hprim).basis k).ext fun r ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      Mult.basis_apply, LinearMap.id_coe, id_eq]
    rw [S.incl_b, ← Mult.basis_apply, Module.Basis.constr_basis, dif_pos r.2]
  intro a b h
  have := congrArg ret h
  have e := fun z ↦ congrArg (fun F ↦ F z) hret
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.id_coe, id_eq] at e
  rw [e a, e b] at this
  exact this

/-- **Lemma 9.2** (`lem:centralizer-ray-algebra`), representation-finiteness: `B_χ = kQ_χ` is
representation-finite (Lemma 4.6 applied to `C_χ ⊆ A₀`, the quotient `C_χ → B_χ` and `π`). -/
theorem Qχ_isRepresentationFinite (hfin : IsRepresentationFinite k (S.P.Lin k)) :
    IsRepresentationFinite k ((S.Qχ hχ hprim).Lin k) := by
  set ι := (S.incl hχ hprim).alg k
  set e := AlgEquiv.ofInjective ι (S.incl_injective hχ hprim k)
  let q : ι.range →ₐ[k] (S.Qχ hχ hprim).Lin k := ((S.quot hχ hprim).alg k).comp e.symm.toAlgHom
  have hq : ∀ c : ι.range, q c = (S.quot hχ hprim).alg k (e.symm c) := fun _ ↦ rfl
  have hc : ∀ c : ι.range, (c : S.P.Lin k) = ι (e.symm c) := fun c ↦ by
    have := e.apply_symm_apply c
    exact (congrArg Subtype.val this).symm
  refine splitRepresentationTransfer_of (C := ι.range) (q := q) (S.proj hχ hprim k) ?_ ?_ ?_ hfin
  · intro c c' b
    rw [hc c, hc c', S.proj_right, S.proj_left, hq, hq]
  · intro y
    obtain ⟨x, hx⟩ := Mor.alg_surjective (S.quot hχ hprim) k (fun r' ↦
      ⟨⟨r'.1, S.inQ_inC r'.2⟩, by
        dsimp only [quot]
        rw [dif_pos (show S.InQ χ r'.1 from r'.2)]⟩) y
    exact ⟨e x, by rw [hq, e.symm_apply_apply, hx]⟩
  · intro c
    rw [hc c, hq]
    have key : (S.proj hχ hprim k).comp ι.toLinearMap = ((S.quot hχ hprim).alg k).toLinearMap := by
      refine ((S.Tc hχ hprim).basis k).ext fun r ↦ ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        Mult.basis_apply]
      rw [S.incl_b, S.proj_b, S.quot_b]
    exact congrArg (fun F ↦ F (e.symm c)) key

/-! ### The weight group of `Q_χ` -/

omit [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R] in
/-- Additive functions on a ray table (homomorphisms out of `W(P)`). -/
def _root_.MultiplicativeBasisDeformations.RaySys.Tab.IsAdd {V' R' : Type} (T : Tab V' R' L)
    {N : Type*} [AddCommGroup N] (f : R' → N) : Prop :=
  ∀ r s t, T.mul r s = some t → f t = f r + f s

/-- **Lemma 9.2, the weight group**: the lifting property of `W(Q_χ)` gives the lifting
property used in Theorem 9.1(3). -/
theorem hW_of_Qχ
    (hQ : ∀ w : {r // (S.qData hχ hprim).pR r} → ZMod 2, (S.Qχ hχ hprim).IsAdd w →
      ∃ ω : {r // (S.qData hχ hprim).pR r} → ℤ, (S.Qχ hχ hprim).IsAdd ω ∧
        ∀ r, (ω r : ZMod 2) = w r) :
    ∀ w : R → ZMod 2,
      (∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → w t = w r + w s) →
      ∃ ω : R → ℤ, (∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ →
        ω t = ω r + ω s) ∧ ∀ r, S.TB χ r → (ω r : ZMod 2) = w r := by
  intro w hw
  let w' : {r // (S.qData hχ hprim).pR r} → ZMod 2 := fun r ↦ if S.TB χ r.1 then w r.1 else 0
  have hw' : (S.Qχ hχ hprim).IsAdd w' := by
    intro r s t h
    have h' := (Tab.subMul_eq_some (S.qData hχ hprim)).1 h
    have hp : ⌜r.1⌝ * ⌜s.1⌝ = ⌜t.1⌝ := S.P.rr_mul_rr_eq_rr.2 h'
    have h1 := S.src_of_mul_ne (by rw [hp]; exact S.rr_ne t.1)
    by_cases hr0 : r.1 = S.P.e (S.P.src r.1)
    · have hsr : S.P.src s.1 = S.P.src r.1 := by rw [← h1]; nth_rewrite 1 [hr0]; rw [S.P.tgt_e]
      rw [show ⌜r.1⌝ = ⌜S.P.e (S.P.src r.1)⌝ from congrArg _ hr0, S.e_mul_rr' s.1 hsr] at hp
      have hst : s = t := Subtype.ext (S.rr_inj hp)
      subst hst
      have hnB : ¬ S.TB χ r.1 := fun h ↦ h.1.1 hr0
      simp [w', hnB]
    by_cases hs0 : s.1 = S.P.e (S.P.src s.1)
    · rw [show ⌜s.1⌝ = ⌜S.P.e (S.P.src s.1)⌝ from congrArg _ hs0, ← h1, S.rr_mul_e] at hp
      have hrt : r = t := Subtype.ext (S.rr_inj hp)
      subst hrt
      have hnB : ¬ S.TB χ s.1 := fun h ↦ h.1.1 hs0
      simp [w', hnB]
    have hBr : S.TB χ r.1 := r.2.resolve_right fun h ↦ hr0 h.1
    have hBs : S.TB χ s.1 := s.2.resolve_right fun h ↦ hs0 h.1
    have ht0 : t.1 ≠ S.P.e (S.P.src t.1) := by
      apply S.ne_e_of_deg; rw [(S.prod_of hp).2.2.2, map_add]
      have := S.P.deg_pos r.1 hr0; have := S.P.deg_nonneg s.1; linarith
    have hBt : S.TB χ t.1 := t.2.resolve_right fun h ↦ ht0 h.1
    simp only [w', if_pos hBr, if_pos hBs, if_pos hBt]
    exact hw _ _ _ hBr hBs hBt hp
  obtain ⟨ω', hω', hω'w⟩ := hQ w' hw'
  refine ⟨fun r ↦ if h : S.TB χ r then ω' ⟨r, Or.inl h⟩ else 0, ?_, ?_⟩
  · intro r s t hr hs ht h
    simp only [dif_pos hr, dif_pos hs, dif_pos ht]
    exact hω' _ _ _ ((Tab.subMul_eq_some (S.qData hχ hprim) (t := ⟨t, Or.inl ht⟩)).2
      (S.P.rr_mul_rr_eq_rr.1 h))
  · intro r hr
    simp only [dif_pos hr]
    rw [hω'w]; simp [w', hr]

/-- The local generators are nilpotent. -/
theorem q_nilpotent (x : V) : ∃ n, S.q x ^ (n + 1) = 0 := by
  by_contra h
  push Not at h
  -- the powers `q^n e_x` are pairwise distinct rays
  have hne : ∀ n, S.q x ^ (n + 1) * ⌜S.P.e x⌝ ≠ 0 := fun n ↦ by
    rw [S.qpow_mul_e (by omega)]; exact h n
  choose f hf using fun n ↦ S.mul_right_ray (hne n)
  have hinj : Function.Injective f := by
    intro a b hab
    have hq : S.q x ≠ 0 := fun h0 ↦ h 0 (by rw [zero_add, pow_one, h0])
    have hd := S.χ_deg_pos x hq
    have e1 := S.deg_wt_qpow_e (hf a).symm
    have e2 := S.deg_wt_qpow_e (hf b).symm
    rw [hab, e2] at e1
    have : ((b + 1 : ℕ) : ℤ) = (a + 1 : ℕ) := mul_right_cancel₀ hd.ne' e1
    omega
  exact not_injective_infinite_finite f hinj

/-- **Lemma 9.2, dimension**: `Q_χ` has fewer rays than `P`, unless no vertex supports `χ`
(`dim B_χ < dim A`). -/
theorem card_Qχ_lt (hx : ∃ x, S.Supp χ x) :
    Fintype.card {r // (S.qData hχ hprim).pR r} < Fintype.card R := by
  classical
  obtain ⟨x, hsx⟩ := hx
  have hex : ∃ n, S.q x ^ (n + 1) = 0 := S.q_nilpotent x
  set n := Nat.find hex with hn
  have hn0 : n ≠ 0 := by
    intro h0; have := Nat.find_spec hex; rw [← hn, h0, zero_add, pow_one] at this; exact hsx.1 this
  have hqn : S.q x ^ n ≠ 0 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have := Nat.find_min hex (show m < n by omega)
    rw [hm]; exact this
  have hqn1 : S.q x ^ (n + 1) = 0 := Nat.find_spec hex
  obtain ⟨t, ht⟩ := S.mul_right_ray (show S.q x ^ n * ⌜S.P.e x⌝ ≠ 0 by
    rw [S.qpow_mul_e (by omega)]; exact hqn)
  obtain ⟨t1, -⟩ := S.tgt_of_qpow_e ht.symm
  have hnQ : ¬ (S.qData hχ hprim).pR t := by
    rintro (hB | ⟨he, -⟩)
    · apply hB.2.1
      rw [t1, S.qh_of_supp χ hsx, ← ht, ← mul_assoc, ← pow_succ', hqn1, zero_mul]
    · have hd := S.χ_deg_pos x hsx.1
      have e := S.deg_wt_qpow_e ht.symm
      rw [he, S.P.wt_e, map_zero] at e
      have : (0 : ℤ) < n * S.P.deg (S.χ x) := by
        have : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
        positivity
      linarith
  exact Fintype.card_subtype_lt hnQ

end Sys

end RaySys

end MultiplicativeBasisDeformations
