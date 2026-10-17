import MultiplicativeBasisDeformations.Foundations.IntegralLifting
import MultiplicativeBasisDeformations.Foundations.TwoSidedPaths

/-!
# Lemma 9.4 along arbitrary ordinary paths

`lem:one-sided-path-coefficients` (`integral-partial-lifts.tex`): for a generating
left-sided ray `r`, an ordinary path of `r` with two-sided prefix `p` and first
left-sided arrow `a`, the value `d_r = [p] + X_a` does not depend on the chosen path, and
neither does `a`. Dually `d_s = Y_b + [p']` for a generating right-sided ray `s`.

`IntegralLifting.lean` defines `d_r` (`DL`) by a recursion on unique first arrows. Here
the manuscript's definition is given (`dPath`, `dPathR`: read along a chosen ordinary path, which
exists, `exists_ordPath`) and shown equal to it (`dPath_eq_DL`, `dPathR_eq_DR`), so the product
equations `DL_prod`, `DR_prod` hold for it. The value read along any ordinary path is `DL r`
(`dL_eq_pathCoef`), the first arrow of the path which is not two-sided (`fstNB`) exists and
is left-sided, and it is the same for all paths (`fstNB_unique`). The dual statements read
the reversed path (`dR_eq_pathCoef`, `lstNB_unique`). The product equations with generating
one-sided output are `DL_prod` and `DR_prod`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L)

local notation:max "⌜" r "⌝" => Sys.rr S r

variable (χ : L)

open Classical in
/-- `[p] + X_a` read along a path: two-sided arrows contribute `ω`; the first arrow `a`
which is not two-sided contributes `X_a` and ends the reading. -/
def pathCoef (ω X : R → ℤ) : List R → ℤ
  | [] => 0
  | a :: l => if S.TB χ a then ω a + pathCoef ω X l else X a

open Classical in
/-- The first arrow of a path which is not two-sided. -/
def fstNB : List R → Option R
  | [] => none
  | a :: l => if S.TB χ a then fstNB l else some a

variable {χ}

theorem pathCoef_of_fstNB (X : R → ℤ) {a : R} (l : List R) (h : S.fstNB χ l = some a) :
    S.pathCoef χ 0 X l = X a := by
  classical
  induction l with
  | nil => simp [fstNB] at h
  | cons b l ih =>
    by_cases hB : S.TB χ b
    · simp only [fstNB, if_pos hB] at h
      simp only [pathCoef, if_pos hB, Pi.zero_apply, zero_add]
      exact ih h
    · simp only [fstNB, if_neg hB, Option.some.injEq] at h
      subst h
      simp only [pathCoef, if_neg hB]

/-- **Every nonidentity ray has an ordinary path**: split it into nonidentity factors until all
factors are ordinary (the degree drops at each split). -/
theorem exists_ordPath (r : R) (hr : r ≠ S.P.e (S.P.src r)) : ∃ l, S.IsOrdPath r l := by
  induction hm : (S.P.deg (S.P.wt r)).toNat using Nat.strong_induction_on generalizing r with
  | _ m ih =>
    by_cases ho : S.Ord r
    · exact ⟨[r], by simp, by simpa using ho, by simp [pathM]⟩
    · have : ∃ u v : R, u ≠ S.P.e (S.P.src u) ∧ v ≠ S.P.e (S.P.src v) ∧ ⌜u⌝ * ⌜v⌝ = ⌜r⌝ := by
        unfold Ord at ho
        push Not at ho
        obtain ⟨u, v, hu, hv, huv⟩ := ho hr
        exact ⟨u, v, hu, hv, huv⟩
      obtain ⟨u, v, hu, hv, huv⟩ := this
      have hw := congrArg S.P.deg (S.prod_of huv).2.2.2
      rw [map_add] at hw
      have du := S.P.deg_pos u hu
      have dv := S.P.deg_pos v hv
      obtain ⟨l1, h1⟩ := ih _ (by omega) u hu rfl
      obtain ⟨l2, h2⟩ := ih _ (by omega) v hv rfl
      exact ⟨l1 ++ l2, by simp [h1.1], fun a ha ↦ (List.mem_append.1 ha).elim (h1.2.1 a) (h2.2.1 a),
        by rw [pathM_append, h1.2.2, h2.2.2, huv]⟩

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Lemma 9.4**, path form: along any ordinary path of a generating left-sided ray `r`,
`d_r = [p] + X_a`, where `p` is the two-sided prefix and `a` the first arrow which is not
two-sided; this arrow exists and is left-sided. -/
theorem dL_eq_pathCoef (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) (ω X : R → ℤ) (l : List R) {r : R} (hr : S.IsGen r) (hT : S.TL χ r)
    (hl : S.IsOrdPath r l) :
    S.DL χ ω X r = S.pathCoef χ ω X l ∧ ∃ a, S.fstNB χ l = some a ∧ S.TL χ a := by
  classical
  induction l generalizing r with
  | nil => exact absurd rfl hl.1
  | cons a l ih =>
    have hm : ⌜a⌝ * S.pathM l = ⌜r⌝ := hl.2.2
    have hoa : S.Ord a := hl.2.1 a (List.mem_cons_self ..)
    by_cases hl0 : l = []
    · subst hl0
      have har : a = r := S.rr_inj (by simpa [pathM] using hm)
      subst har
      have hB : ¬ S.TB χ a := fun hB ↦ hB.2.2 hT.2.2
      have hDL := S.DL_eq k ω X hfin hχ hprim hr hT ⟨hoa, _, S.rr_mul_e a⟩ (S.rr_mul_e a)
      rw [if_neg hB] at hDL
      refine ⟨by rw [hDL]; simp [pathCoef, hB], a, by simp [fstNB, hB], hT⟩
    · have hne : S.pathM l ≠ 0 := fun h0 ↦ S.rr_ne r (by rw [← hm, h0, mul_zero])
      obtain ⟨c, hc, hc0⟩ := S.pathM_ray hl0
        (fun b hb ↦ (hl.2.1 b (List.mem_cons_of_mem _ hb)).1) hne
      have hac : ⌜a⌝ * ⌜c⌝ = ⌜r⌝ := by rw [← hc]; exact hm
      have hDL := S.DL_eq k ω X hfin hχ hprim hr hT ⟨hoa, c, hac⟩ hac
      by_cases hB : S.TB χ a
      · obtain ⟨g, t, -⟩ := S.rest_TL k hfin hχ hprim hr hT hoa hB hac
        obtain ⟨ih1, ih2⟩ :=
          ih g t ⟨hl0, fun b hb ↦ hl.2.1 b (List.mem_cons_of_mem _ hb), hc⟩
        rw [hDL, if_pos hB, ih1]
        simp only [pathCoef, fstNB, if_pos hB, true_and]
        exact ih2
      · rw [hDL, if_neg hB]
        have hTa : S.TL χ a := by
          rcases S.table_L hχ hprim hoa.1 hc0 hac hT with ⟨h, -⟩ | ⟨h, -⟩
          · exact h
          · exact absurd h hB
        exact ⟨by simp [pathCoef, hB], a, by simp [fstNB, hB], hTa⟩

variable (χ) in
open Classical in
/-- **`d_r = [p] + X_a`, defined as in the manuscript**: read along a chosen ordinary path. -/
def dPath (ω X : R → ℤ) (r : R) : ℤ :=
  if h : r ≠ S.P.e (S.P.src r) then S.pathCoef χ ω X (S.exists_ordPath r h).choose else 0

/-- The path definition of `d_r` is the coefficient `DL` used in the integral lifting. -/
theorem dPath_eq_DL (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) (ω X : R → ℤ) {r : R} (hr : S.IsGen r) (hT : S.TL χ r) :
    S.dPath χ ω X r = S.DL χ ω X r := by
  have h0 : r ≠ S.P.e (S.P.src r) := hT.1.1
  rw [dPath, dif_pos h0]
  exact (S.dL_eq_pathCoef k hfin hχ hprim ω X _ hr hT (S.exists_ordPath r h0).choose_spec).1.symm

/-- **Lemma 9.4**, product equations with generating left-sided output, for the path
definition: `d_t = d_u` for a left-sided first factor, `d_t = [u] + d_v` for a two-sided one. -/
theorem dPath_prod (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) (ω X : R → ℤ)
    (hω : ∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → ω t = ω r + ω s)
    {r u v : R} (hr : S.IsGen r) (hT : S.TL χ r) (huv : ⌜u⌝ * ⌜v⌝ = ⌜r⌝)
    (hu0 : u ≠ S.P.e (S.P.src u)) :
    (S.TL χ u → S.dPath χ ω X r = S.dPath χ ω X u) ∧
      (S.TB χ u → S.dPath χ ω X r = ω u + S.dPath χ ω X v) := by
  obtain ⟨h1, h2⟩ := S.DL_prod k ω X hfin hχ hprim hω hr hT huv hu0
  have gu : S.IsGen u := S.gen_factor k hfin hr (S.dim2_of_TL hT) (a := S.P.e (S.P.src r))
    (m := u) (b := v) (by rw [mul_assoc, huv, S.e_mul_rr])
  have gv : S.IsGen v := S.gen_factor k hfin hr (S.dim2_of_TL hT) (a := u) (m := v)
    (b := S.P.e (S.P.tgt r)) (by rw [huv, S.rr_mul_e])
  rw [S.dPath_eq_DL k hfin hχ hprim ω X hr hT]
  refine ⟨fun hu ↦ by rw [h1 hu, S.dPath_eq_DL k hfin hχ hprim ω X gu hu], fun hu ↦ ?_⟩
  have hv0 : v ≠ S.P.e (S.P.src v) := by
    intro he
    have := S.src_of_mul_ne (by rw [huv]; exact S.rr_ne r)
    rw [he, ← this, S.rr_mul_e] at huv
    rw [← S.rr_inj huv] at hT
    exact hu.2.2 hT.2.2
  have hv : S.TL χ v := by
    rcases S.table_L hχ hprim hu0 hv0 huv hT with ⟨h, -⟩ | ⟨-, h, -⟩
    · exact absurd hT.2.2 (by intro h'; exact hu.2.2 h.2.2)
    · exact h
  rw [h2 hu, S.dPath_eq_DL k hfin hχ hprim ω X gv hv]

/-- **Lemma 9.4**: `d_r = [p] + X_a` does not depend on the chosen ordinary path. -/
theorem pathCoef_unique (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) (ω X : R → ℤ) {r : R} (hr : S.IsGen r) (hT : S.TL χ r) {l l' : List R}
    (hl : S.IsOrdPath r l) (hl' : S.IsOrdPath r l') :
    S.pathCoef χ ω X l = S.pathCoef χ ω X l' :=
  (S.dL_eq_pathCoef k hfin hχ hprim ω X l hr hT hl).1.symm.trans
    (S.dL_eq_pathCoef k hfin hχ hprim ω X l' hr hT hl').1

/-- **Lemma 9.4**: the first left-sided arrow of an ordinary path of a generating
left-sided ray does not depend on the path. -/
theorem fstNB_unique (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {r : R} (hr : S.IsGen r) (hT : S.TL χ r) {l l' : List R}
    (hl : S.IsOrdPath r l) (hl' : S.IsOrdPath r l') : S.fstNB χ l = S.fstNB χ l' := by
  classical
  obtain ⟨-, a, ha, -⟩ := S.dL_eq_pathCoef k hfin hχ hprim 0 0 l hr hT hl
  obtain ⟨-, a', ha', -⟩ := S.dL_eq_pathCoef k hfin hχ hprim 0 0 l' hr hT hl'
  set X : R → ℤ := fun b ↦ if b = a then 1 else 0
  have h := S.pathCoef_unique k hfin hχ hprim 0 X hr hT hl hl'
  rw [S.pathCoef_of_fstNB X l ha, S.pathCoef_of_fstNB X l' ha'] at h
  simp only [X, if_pos rfl] at h
  rw [ha, ha']
  by_contra hne
  rw [if_neg (fun h' ↦ hne (by rw [h']))] at h
  exact one_ne_zero h

/-! ### The dual: right-sided rays -/

theorem op_pathM (l : List R) : S.op.pathM l.reverse = S.P.toOp (S.pathM l) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.reverse_cons, S.op.pathM_append, ih]
    simp only [pathM, mul_one]
    rw [Tab.toOp_mul]; rfl

theorem op_isOrdPath {s : R} {l : List R} (h : S.IsOrdPath s l) : S.op.IsOrdPath s l.reverse :=
  ⟨by simpa using h.1, fun a ha ↦ (S.op_ord a).2 (h.2.1 a (List.mem_reverse.1 ha)),
    by rw [op_pathM, h.2.2]; rfl⟩

theorem op_pathCoef (ω X : R → ℤ) (l : List R) :
    S.op.pathCoef χ ω X l = S.pathCoef χ ω X l := by
  classical
  induction l with
  | nil => rfl
  | cons a l ih => simp only [pathCoef, op_TB, ih]

theorem op_fstNB (l : List R) : S.op.fstNB χ l = S.fstNB χ l := by
  classical
  induction l with
  | nil => rfl
  | cons a l ih => simp only [fstNB, op_TB, ih]

/-- **Lemma 9.4**, dual path form: along any ordinary path of a generating right-sided ray
`s`, read from its end, `d_s = Y_b + [p']`, where `p'` is the two-sided suffix and `b` the
last arrow which is not two-sided; this arrow exists and is right-sided. -/
theorem dR_eq_pathCoef (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) (ω Y : R → ℤ) (l : List R) {s : R} (hs : S.IsGen s) (hT : S.TR χ s)
    (hl : S.IsOrdPath s l) :
    S.DR χ ω Y s = S.pathCoef χ ω Y l.reverse ∧
      ∃ b, S.fstNB χ l.reverse = some b ∧ S.TR χ b := by
  obtain ⟨h1, b, hb, hTb⟩ := S.op.dL_eq_pathCoef k (S.P.op_isRepresentationFinite k hfin) hχ
    hprim ω Y l.reverse ((S.op_isGen_iff s).2 hs) ((S.op_TL s).2 hT) (S.op_isOrdPath hl)
  rw [op_pathCoef] at h1
  rw [op_fstNB] at hb
  exact ⟨h1, b, hb, (S.op_TL b).1 hTb⟩

variable (χ) in
open Classical in
/-- **`d_s = Y_b + [p']`, defined as in the manuscript**: read backwards along a chosen ordinary
path. -/
def dPathR (ω Y : R → ℤ) (s : R) : ℤ :=
  if h : s ≠ S.P.e (S.P.src s) then S.pathCoef χ ω Y (S.exists_ordPath s h).choose.reverse else 0

/-- The path definition of `d_s` is the coefficient `DR` used in the integral lifting. -/
theorem dPathR_eq_DR (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) (ω Y : R → ℤ) {s : R} (hs : S.IsGen s) (hT : S.TR χ s) :
    S.dPathR χ ω Y s = S.DR χ ω Y s := by
  have h0 : s ≠ S.P.e (S.P.src s) := hT.1.1
  rw [dPathR, dif_pos h0]
  exact (S.dR_eq_pathCoef k hfin hχ hprim ω Y _ hs hT (S.exists_ordPath s h0).choose_spec).1.symm

/-- **Lemma 9.4**, product equations with generating right-sided output, for the path
definition: `d_t = d_v` for a right-sided last factor, `d_t = d_u + [v]` for a two-sided one. -/
theorem dPathR_prod (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) (ω Y : R → ℤ)
    (hω : ∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → ω t = ω r + ω s)
    {r u v : R} (hr : S.IsGen r) (hT : S.TR χ r) (huv : ⌜u⌝ * ⌜v⌝ = ⌜r⌝)
    (hv0 : v ≠ S.P.e (S.P.src v)) :
    (S.TR χ v → S.dPathR χ ω Y r = S.dPathR χ ω Y v) ∧
      (S.TB χ v → S.dPathR χ ω Y r = S.dPathR χ ω Y u + ω v) := by
  obtain ⟨h1, h2⟩ := S.DR_prod k ω Y hfin hχ hprim hω hr hT huv hv0
  have hd2 : S.Dim2 r := by
    right; rw [← S.qh_of_supp χ (S.supp_of_qh' hT.2.2)]; exact hT.2.2
  have gu : S.IsGen u := S.gen_factor k hfin hr hd2 (a := S.P.e (S.P.src r))
    (m := u) (b := v) (by rw [mul_assoc, huv, S.e_mul_rr])
  have gv : S.IsGen v := S.gen_factor k hfin hr hd2 (a := u) (m := v)
    (b := S.P.e (S.P.tgt r)) (by rw [huv, S.rr_mul_e])
  rw [S.dPathR_eq_DR k hfin hχ hprim ω Y hr hT]
  refine ⟨fun hv ↦ by rw [h1 hv, S.dPathR_eq_DR k hfin hχ hprim ω Y gv hv], fun hv ↦ ?_⟩
  have hu0 : u ≠ S.P.e (S.P.src u) := by
    intro he
    have h3 := (S.prod_of huv).2.2.1
    rw [he, S.P.tgt_e] at h3
    rw [he, S.e_mul_rr' v h3.symm] at huv
    rw [← S.rr_inj huv] at hT
    exact hv.2.1 hT.2.1
  have hu : S.TR χ u := by
    rcases S.table_R hχ hprim hu0 hv0 huv hT with ⟨h, -⟩ | ⟨-, h, -⟩
    · exact absurd h.2.1 hv.2.1
    · exact h
  rw [h2 hv, S.dPathR_eq_DR k hfin hχ hprim ω Y gu hu]

/-- **Lemma 9.4**, dual: the last right-sided arrow of an ordinary path of a generating
right-sided ray does not depend on the path. -/
theorem lstNB_unique (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {s : R} (hs : S.IsGen s) (hT : S.TR χ s) {l l' : List R}
    (hl : S.IsOrdPath s l) (hl' : S.IsOrdPath s l') :
    S.fstNB χ l.reverse = S.fstNB χ l'.reverse := by
  have := S.op.fstNB_unique k (S.P.op_isRepresentationFinite k hfin) hχ hprim
    ((S.op_isGen_iff s).2 hs) ((S.op_TL s).2 hT) (S.op_isOrdPath hl) (S.op_isOrdPath hl')
  rwa [op_fstNB, op_fstNB] at this

end Sys

end RaySys

end MultiplicativeBasisDeformations
