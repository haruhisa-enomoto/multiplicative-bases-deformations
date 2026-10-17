import MultiplicativeBasisDeformations.Foundations.TableTree

/-!
# The six-lift and eight-lift trees of Appendix C.1

`eq:six-lift-tree` with the lifts `eq:six-lift-coordinates`, and `eq:eight-lift-tree` with the
lifts `eq:eight-lift-coordinates` (`local-ray-restrictions.tex:104–352`). Each is given as a
table poset with its rays; the factorization checks of `lem:tree-quotient` enter only through
the retraction conditions on cover relations (Lemma 8.9), as hypotheses `X*`/`Y*` naming the
excluded factorizations. Lemma 8.8 then excludes both trees.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Tab

open PosetRep

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (P : Tab V R L)

/-! ### The six-lift tree -/

/-- `v₁ → v₂ → v₃`, `v₄ → v₅ → v₂`, `v₆ → v₅` (indices `0, …, 5`). -/
def t6L : Fin 6 → Fin 6 → Bool := fun i j ↦
  i == j || (j.val == 2 && i.val != 2) ||
    (j.val == 1 && (i.val == 0 || i.val == 3 || i.val == 4 || i.val == 5)) ||
    (j.val == 4 && (i.val == 3 || i.val == 5))

instance : Fact (Ax t6L) := ⟨by unfold Ax; decide⟩

theorem t6L_uniq : UniqOK t6L := by unfold UniqOK; decide

theorem t6L_count : CountOK t6L ![1, 2, 1, 1, 2, 1] := by unfold CountOK; decide

section Six

variable {x y z t : V} {γ α lam β f qy qz aq ζ bq : R}
  (γ1 : P.src γ = x) (γ2 : P.tgt γ = y) (α1 : P.src α = y) (α2 : P.tgt α = z)
  (l1 : P.src lam = z) (l2 : P.tgt lam = y) (β1 : P.src β = t) (β2 : P.tgt β = z)
  (hf : P.mul γ α = some f) (hqy : P.mul α lam = some qy) (hqz : P.mul lam α = some qz)
  (haq1 : P.mul α qz = some aq) (haq2 : P.mul qy α = some aq) (hζ : P.mul β lam = some ζ)
  (hbq1 : P.mul β qz = some bq) (hbq2 : P.mul ζ α = some bq)
  (dγ : 0 < P.deg (P.wt γ)) (dα : 0 < P.deg (P.wt α)) (dl : 0 < P.deg (P.wt lam))
  (dβ : 0 < P.deg (P.wt β))
  (X1 : ∀ h, P.src h = y → P.tgt h = x → P.mul h γ ≠ some qy)
  (X2 : ∀ h, P.src h = z → P.tgt h = x → P.mul h γ ≠ some lam)
  (X3 : ∀ h, P.src h = t → P.tgt h = x → P.mul h γ ≠ some ζ)
  (X4 : ∀ h, P.src h = t → P.tgt h = y → P.mul h α ≠ some β)
  (X5 : ∀ h, P.src h = x → P.tgt h = z → P.wt h + P.wt qz = P.wt α + P.wt γ →
    P.mul h lam ≠ some γ)
  (X6 : ∀ h, P.src h = y → P.tgt h = t → P.mul h β ≠ some α)

/-- The objects. -/
def s6V (x y z t : V) : Fin 6 → V := ![x, y, z, y, z, t]

/-- The weights. -/
def s6G (γ α β qz : R) : Fin 6 → L :=
  ![-P.wt γ, 0, P.wt α, -P.wt qz, P.wt α - P.wt qz, P.wt α - P.wt qz - P.wt β]

/-- The rays. -/
def s6ρ (x y z t : V) (γ α lam β f qy qz aq ζ bq : R) : Fin 6 → Fin 6 → R :=
  ![![P.e x, γ, f, P.e x, P.e x, P.e x],
    ![P.e x, P.e y, α, P.e x, P.e x, P.e x],
    ![P.e x, P.e x, P.e z, P.e x, P.e x, P.e x],
    ![P.e x, qy, aq, P.e y, α, P.e x],
    ![P.e x, lam, qz, P.e x, P.e z, P.e x],
    ![P.e x, ζ, bq, P.e x, β, P.e t]]

set_option maxHeartbeats 1000000 in
include γ1 α1 l1 β1 hf hqy hqz haq1 haq2 hζ hbq1 hbq2 in
theorem s6_src : ∀ i j, t6L i j = true →
    P.src (P.s6ρ x y z t γ α lam β f qy qz aq ζ bq i j) = s6V x y z t i := by
  have e1 := P.mul_src _ _ _ hf
  have e2 := P.mul_src _ _ _ hqy
  have e3 := P.mul_src _ _ _ hqz
  have e4 := P.mul_src _ _ _ haq2
  have e5 := P.mul_src _ _ _ hζ
  have e6 := P.mul_src _ _ _ hbq1
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [t6L] at hij <;>
    simp [s6V, s6ρ, P.src_e, e1, e2, e3, e4, e5, e6, γ1, α1, l1, β1]

set_option maxHeartbeats 1000000 in
include γ2 α2 l2 β2 hf hqy hqz haq1 haq2 hζ hbq1 hbq2 in
theorem s6_tgt : ∀ i j, t6L i j = true →
    P.tgt (P.s6ρ x y z t γ α lam β f qy qz aq ζ bq i j) = s6V x y z t j := by
  have e1 := P.mul_tgt _ _ _ hf
  have e2 := P.mul_tgt _ _ _ hqy
  have e3 := P.mul_tgt _ _ _ hqz
  have e4 := P.mul_tgt _ _ _ haq2
  have e5 := P.mul_tgt _ _ _ hζ
  have e6 := P.mul_tgt _ _ _ hbq1
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [t6L] at hij <;>
    simp [s6V, s6ρ, P.tgt_e, e1, e2, e3, e4, e5, e6, γ2, α2, l2, β2]

set_option maxHeartbeats 1000000 in
include hf hqy hqz haq1 haq2 hζ hbq1 hbq2 in
theorem s6_wt : ∀ i j, t6L i j = true →
    P.wt (P.s6ρ x y z t γ α lam β f qy qz aq ζ bq i j) = P.s6G γ α β qz j - P.s6G γ α β qz i := by
  have e1 := P.wt_mul _ _ _ hf
  have e2 := P.wt_mul _ _ _ hqy
  have e3 := P.wt_mul _ _ _ hqz
  have e4 := P.wt_mul _ _ _ haq1
  have e5 := P.wt_mul _ _ _ hζ
  have e6 := P.wt_mul _ _ _ hbq1
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [t6L] at hij <;>
    simp [s6G, s6ρ, P.wt_e, e1, e2, e3, e4, e5, e6] <;> abel

set_option maxHeartbeats 2000000 in
include γ1 α1 l1 β1 γ2 α2 l2 β2 hf hqy hqz haq1 haq2 hζ hbq1 hbq2 in
theorem s6_mul : ∀ i j l, t6L i j = true → t6L j l = true →
    P.mul (P.s6ρ x y z t γ α lam β f qy qz aq ζ bq i j)
      (P.s6ρ x y z t γ α lam β f qy qz aq ζ bq j l) =
      some (P.s6ρ x y z t γ α lam β f qy qz aq ζ bq i l) := by
  refine P.hmul_of_strict (s6V x y z t) _ (P.s6_src γ1 α1 l1 β1 hf hqy hqz haq1 haq2 hζ hbq1 hbq2)
    (P.s6_tgt γ2 α2 l2 β2 hf hqy hqz haq1 haq2 hζ hbq1 hbq2) (fun i ↦ by fin_cases i <;> rfl) ?_
  intro i j l h1 h2 h3 h4
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp [t6L] at h1 h2 h3 h4 <;>
    simp [s6ρ, hf, hqy, hqz, haq1, haq2, hζ, hbq1, hbq2]

set_option maxHeartbeats 4000000 in
include hf hqy hqz haq1 haq2 hζ hbq1 hbq2 dγ dα dl dβ in
theorem s6_retL : ∀ i j l (h : R), covB t6L i j = true → t6L i l = true →
    P.src h = s6V x y z t j → P.tgt h = s6V x y z t l →
    P.wt h = P.s6G γ α β qz l - P.s6G γ α β qz j →
    P.mul (P.s6ρ x y z t γ α lam β f qy qz aq ζ bq i j) h =
      some (P.s6ρ x y z t γ α lam β f qy qz aq ζ bq i l) → t6L j l = true := by
  have e3 := congrArg P.deg (P.wt_mul _ _ _ hqz)
  rw [map_add] at e3
  intro i j l h hcv hil h1 h2 h3 hm
  fin_cases i <;> fin_cases j <;> fin_cases l
  all_goals first
    | decide
    | exact absurd hcv (by decide)
    | exact absurd hil (by decide)
    | skip
  all_goals simp [s6V, s6G, s6ρ] at h1 h2 h3 hm
  all_goals (exfalso; have hd := P.deg_nonneg h; rw [h3] at hd
             simp only [map_sub, map_neg, map_add, map_zero] at hd; linarith)

set_option maxHeartbeats 4000000 in
include hf hqy hqz haq1 haq2 hζ hbq1 hbq2 dγ dα dl dβ X1 X2 X3 X4 X5 X6 in
theorem s6_retR : ∀ i j l (h : R), covB t6L i j = true → t6L l j = true →
    P.src h = s6V x y z t l → P.tgt h = s6V x y z t i →
    P.wt h = P.s6G γ α β qz i - P.s6G γ α β qz l →
    P.mul h (P.s6ρ x y z t γ α lam β f qy qz aq ζ bq i j) =
      some (P.s6ρ x y z t γ α lam β f qy qz aq ζ bq l j) → t6L l i = true := by
  have e3 := congrArg P.deg (P.wt_mul _ _ _ hqz)
  rw [map_add] at e3
  intro i j l h hcv hlj h1 h2 h3 hm
  fin_cases i <;> fin_cases j <;> fin_cases l
  all_goals first
    | decide
    | exact absurd hcv (by decide)
    | exact absurd hlj (by decide)
    | skip
  all_goals simp [s6V, s6G, s6ρ] at h1 h2 h3 hm
  all_goals first
    | exact (X1 h h1 h2 hm).elim
    | exact (X2 h h1 h2 hm).elim
    | exact (X3 h h1 h2 hm).elim
    | exact (X4 h h1 h2 hm).elim
    | exact (X5 h h1 h2 (by rw [h3]; abel) hm).elim
    | exact (X6 h h1 h2 hm).elim
    | (exfalso; have hd := P.deg_nonneg h; rw [h3] at hd
       simp only [map_sub, map_neg, map_add, map_zero] at hd; linarith)

variable (k : Type u) [Field k] [IsAlgClosed k]

include γ1 α1 l1 β1 γ2 α2 l2 β2 hf hqy hqz haq1 haq2 hζ hbq1 hbq2 dγ dα dl dβ
  X1 X2 X3 X4 X5 X6 in
/-- **The six-lift tree is excluded** (`eq:six-lift-tree`). -/
theorem s6_false (hfin : IsRepresentationFinite k (P.Lin k)) : False :=
  P.table_false (s6V x y z t) (P.s6G γ α β qz) (P.s6ρ x y z t γ α lam β f qy qz aq ζ bq)
    (P.s6_src γ1 α1 l1 β1 hf hqy hqz haq1 haq2 hζ hbq1 hbq2)
    (P.s6_tgt γ2 α2 l2 β2 hf hqy hqz haq1 haq2 hζ hbq1 hbq2)
    (P.s6_wt hf hqy hqz haq1 haq2 hζ hbq1 hbq2)
    (P.s6_mul γ1 γ2 α1 α2 l1 l2 β1 β2 hf hqy hqz haq1 haq2 hζ hbq1 hbq2)
    (P.s6_retL hf hqy hqz haq1 haq2 hζ hbq1 hbq2 dγ dα dl dβ)
    (P.s6_retR hf hqy hqz haq1 haq2 hζ hbq1 hbq2 dγ dα dl dβ X1 X2 X3 X4 X5 X6) k hfin
    ![1, 2, 1, 1, 2, 1] t6L_uniq t6L_count

end Six

/-! ### The eight-lift tree -/

/-- Arms `(3,3,1)` around `v₃` (indices `0, …, 7` for `v₁, …, v₈`). -/
def t8L : Fin 8 → Fin 8 → Bool := fun i j ↦
  i == j || (i.val == 0 && (j.val == 2 || j.val == 3 || j.val == 4)) ||
    (i.val == 2 && (j.val == 3 || j.val == 4)) || (i.val == 1 && (j.val == 3 || j.val == 6)) ||
    (i.val == 5 && j.val == 4) || (i.val == 7 && (j.val == 5 || j.val == 4))

instance : Fact (Ax t8L) := ⟨by unfold Ax; decide⟩

theorem t8L_uniq : UniqOK t8L := by unfold UniqOK; decide

theorem t8L_count : CountOK t8L ![2, 2, 4, 3, 3, 2, 1, 1] := by unfold CountOK; decide

section Eight

variable {x y z t : V} {γ α η β f qy qz γq bq : R}
  (γ1 : P.src γ = x) (γ2 : P.tgt γ = y) (α1 : P.src α = y) (α2 : P.tgt α = z)
  (η1 : P.src η = x) (η2 : P.tgt η = t) (β1 : P.src β = t) (β2 : P.tgt β = z)
  (qy1 : P.src qy = y) (qy2 : P.tgt qy = y) (qz1 : P.src qz = z) (qz2 : P.tgt qz = z)
  (hγq : P.mul γ qy = some γq) (hf : P.mul γ α = some f) (hf' : P.mul η β = some f)
  (hbq : P.mul β qz = some bq)
  (dγ : 0 < P.deg (P.wt γ)) (dα : 0 < P.deg (P.wt α)) (dη : 0 < P.deg (P.wt η))
  (dβ : 0 < P.deg (P.wt β)) (dqy : 0 < P.deg (P.wt qy)) (dqz : 0 < P.deg (P.wt qz))
  (Y1 : ∀ h, P.src h = y → P.tgt h = z → P.mul qy h ≠ some α)
  (Y2 : ∀ h, P.src h = z → P.tgt h = y → P.mul α h ≠ some qy)
  (Y3 : ∀ h, P.src h = y → P.tgt h = t → P.mul γ h ≠ some η)
  (Y4 : ∀ h, P.src h = t → P.tgt h = y → P.mul η h ≠ some γ)
  (Y5 : ∀ h, P.src h = x → P.tgt h = y → P.wt h + P.wt qy = P.wt γ → P.mul h qy ≠ some γ)
  (Y6 : ∀ h, P.src h = z → P.tgt h = y → P.mul h α ≠ some qz)
  (Y7 : ∀ h, P.src h = t → P.tgt h = y → P.mul h α ≠ some bq)
  (Y8 : ∀ h, P.src h = x → P.tgt h = x → P.mul h γ ≠ some γq)
  (Y9 : ∀ h, P.src h = y → P.tgt h = x → P.mul h γ ≠ some qy)
  (Y10 : ∀ h, P.src h = x → P.tgt h = z → P.wt h + P.wt qz = P.wt α + P.wt γ →
    P.mul h qz ≠ some f)
  (Y11 : ∀ h, P.src h = y → P.tgt h = z → P.mul h qz ≠ some α)

/-- The objects. -/
def s8V (x y z t : V) : Fin 8 → V := ![x, x, y, y, z, z, t, t]

/-- The weights. -/
def s8G (γ α β qy qz : R) : Fin 8 → L :=
  ![-P.wt γ, P.wt qy - P.wt γ, 0, P.wt qy, P.wt α, P.wt α - P.wt qz,
    P.wt α + P.wt qy - P.wt β, P.wt α - P.wt qz - P.wt β]

/-- The rays. -/
def s8ρ (x y z t : V) (γ α η β f qy qz γq bq : R) : Fin 8 → Fin 8 → R :=
  ![![P.e x, P.e x, γ, γq, f, P.e x, P.e x, P.e x],
    ![P.e x, P.e x, P.e x, γ, P.e x, P.e x, η, P.e x],
    ![P.e x, P.e x, P.e y, qy, α, P.e x, P.e x, P.e x],
    ![P.e x, P.e x, P.e x, P.e y, P.e x, P.e x, P.e x, P.e x],
    ![P.e x, P.e x, P.e x, P.e x, P.e z, P.e x, P.e x, P.e x],
    ![P.e x, P.e x, P.e x, P.e x, qz, P.e z, P.e x, P.e x],
    ![P.e x, P.e x, P.e x, P.e x, P.e x, P.e x, P.e t, P.e x],
    ![P.e x, P.e x, P.e x, P.e x, bq, β, P.e x, P.e t]]

set_option maxHeartbeats 2000000 in
include γ1 α1 η1 β1 qy1 qz1 hγq hf hbq in
theorem s8_src : ∀ i j, t8L i j = true →
    P.src (P.s8ρ x y z t γ α η β f qy qz γq bq i j) = s8V x y z t i := by
  have e1 := P.mul_src _ _ _ hγq
  have e2 := P.mul_src _ _ _ hf
  have e3 := P.mul_src _ _ _ hbq
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [t8L] at hij <;>
    simp [s8V, s8ρ, P.src_e, e1, e2, e3, γ1, α1, η1, β1, qy1, qz1]

set_option maxHeartbeats 2000000 in
include γ2 α2 η2 β2 qy2 qz2 hγq hf hbq in
theorem s8_tgt : ∀ i j, t8L i j = true →
    P.tgt (P.s8ρ x y z t γ α η β f qy qz γq bq i j) = s8V x y z t j := by
  have e1 := P.mul_tgt _ _ _ hγq
  have e2 := P.mul_tgt _ _ _ hf
  have e3 := P.mul_tgt _ _ _ hbq
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [t8L] at hij <;>
    simp [s8V, s8ρ, P.tgt_e, e1, e2, e3, γ2, α2, η2, β2, qy2, qz2]

set_option maxHeartbeats 2000000 in
include hγq hf hf' hbq in
theorem s8_wt : ∀ i j, t8L i j = true →
    P.wt (P.s8ρ x y z t γ α η β f qy qz γq bq i j) =
      P.s8G γ α β qy qz j - P.s8G γ α β qy qz i := by
  have e1 := P.wt_mul _ _ _ hγq
  have e2 := P.wt_mul _ _ _ hf
  have e3 := P.wt_mul _ _ _ hbq
  have e4 : P.wt η = P.wt γ + P.wt α - P.wt β := by
    rw [← e2, P.wt_mul _ _ _ hf']; abel
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [t8L] at hij <;>
    simp [s8G, s8ρ, P.wt_e, e1, e2, e3, e4] <;> abel

set_option maxHeartbeats 2000000 in
include γ1 α1 η1 β1 qy1 qz1 γ2 α2 η2 β2 qy2 qz2 hγq hf hbq in
theorem s8_mul : ∀ i j l, t8L i j = true → t8L j l = true →
    P.mul (P.s8ρ x y z t γ α η β f qy qz γq bq i j) (P.s8ρ x y z t γ α η β f qy qz γq bq j l) =
      some (P.s8ρ x y z t γ α η β f qy qz γq bq i l) := by
  refine P.hmul_of_strict (s8V x y z t) _ (P.s8_src γ1 α1 η1 β1 qy1 qz1 hγq hf hbq)
    (P.s8_tgt γ2 α2 η2 β2 qy2 qz2 hγq hf hbq) (fun i ↦ by fin_cases i <;> rfl) ?_
  intro i j l h1 h2 h3 h4
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp [t8L] at h1 h2 h3 h4 <;>
    simp [s8ρ, hγq, hf, hbq]

set_option maxHeartbeats 8000000 in
include hγq hf hf' hbq dγ dα dη dβ dqy dqz Y1 Y2 Y3 Y4 in
theorem s8_retL : ∀ i j l (h : R), covB t8L i j = true → t8L i l = true →
    P.src h = s8V x y z t j → P.tgt h = s8V x y z t l →
    P.wt h = P.s8G γ α β qy qz l - P.s8G γ α β qy qz j →
    P.mul (P.s8ρ x y z t γ α η β f qy qz γq bq i j) h =
      some (P.s8ρ x y z t γ α η β f qy qz γq bq i l) → t8L j l = true := by
  have e4 := congrArg P.deg (P.wt_mul _ _ _ hf)
  have e5 := congrArg P.deg (P.wt_mul _ _ _ hf')
  rw [map_add] at e4 e5
  intro i j l h hcv hil h1 h2 h3 hm
  fin_cases i <;> fin_cases j <;> fin_cases l
  all_goals first
    | decide
    | exact absurd hcv (by decide)
    | exact absurd hil (by decide)
    | skip
  all_goals simp [s8V, s8G, s8ρ] at h1 h2 h3 hm
  all_goals first
    | exact (Y1 h h1 h2 hm).elim
    | exact (Y2 h h1 h2 hm).elim
    | exact (Y3 h h1 h2 hm).elim
    | exact (Y4 h h1 h2 hm).elim
    | (exfalso; have hd := P.deg_nonneg h; rw [h3] at hd
       simp only [map_sub, map_neg, map_add, map_zero] at hd; linarith)

set_option maxHeartbeats 8000000 in
include hγq hf hf' hbq dγ dα dη dβ dqy dqz Y5 Y6 Y7 Y8 Y9 Y10 Y11 in
theorem s8_retR : ∀ i j l (h : R), covB t8L i j = true → t8L l j = true →
    P.src h = s8V x y z t l → P.tgt h = s8V x y z t i →
    P.wt h = P.s8G γ α β qy qz i - P.s8G γ α β qy qz l →
    P.mul h (P.s8ρ x y z t γ α η β f qy qz γq bq i j) =
      some (P.s8ρ x y z t γ α η β f qy qz γq bq l j) → t8L l i = true := by
  have e4 := congrArg P.deg (P.wt_mul _ _ _ hf)
  have e5 := congrArg P.deg (P.wt_mul _ _ _ hf')
  rw [map_add] at e4 e5
  intro i j l h hcv hlj h1 h2 h3 hm
  fin_cases i <;> fin_cases j <;> fin_cases l
  all_goals first
    | decide
    | exact absurd hcv (by decide)
    | exact absurd hlj (by decide)
    | skip
  all_goals simp [s8V, s8G, s8ρ] at h1 h2 h3 hm
  all_goals first
    | exact (Y5 h h1 h2 (by rw [h3]; abel) hm).elim
    | exact (Y6 h h1 h2 hm).elim
    | exact (Y7 h h1 h2 hm).elim
    | exact (Y8 h h1 h2 hm).elim
    | exact (Y9 h h1 h2 hm).elim
    | exact (Y10 h h1 h2 (by rw [h3]; abel) hm).elim
    | exact (Y11 h h1 h2 hm).elim
    | (exfalso; have hd := P.deg_nonneg h; rw [h3] at hd
       simp only [map_sub, map_neg, map_add, map_zero] at hd; linarith)

variable (k : Type u) [Field k] [IsAlgClosed k]

include γ1 α1 η1 β1 qy1 qz1 γ2 α2 η2 β2 qy2 qz2 hγq hf hf' hbq dγ dα dη dβ dqy dqz
  Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10 Y11 in
/-- **The eight-lift tree with arms `(3,3,1)` is excluded** (`eq:eight-lift-tree`). -/
theorem s8_false (hfin : IsRepresentationFinite k (P.Lin k)) : False :=
  P.table_false (s8V x y z t) (P.s8G γ α β qy qz) (P.s8ρ x y z t γ α η β f qy qz γq bq)
    (P.s8_src γ1 α1 η1 β1 qy1 qz1 hγq hf hbq)
    (P.s8_tgt γ2 α2 η2 β2 qy2 qz2 hγq hf hbq)
    (P.s8_wt hγq hf hf' hbq)
    (P.s8_mul γ1 γ2 α1 α2 η1 η2 β1 β2 qy1 qy2 qz1 qz2 hγq hf hbq)
    (P.s8_retL hγq hf hf' hbq dγ dα dη dβ dqy dqz Y1 Y2 Y3 Y4)
    (P.s8_retR hγq hf hf' hbq dγ dα dη dβ dqy dqz Y5 Y6 Y7 Y8 Y9 Y10 Y11) k hfin
    ![2, 2, 4, 3, 3, 2, 1, 1] t8L_uniq t8L_count

end Eight

/-! ### The proper six-tree `eq:proper-six-tree` -/

/-- `B₀ → B₁ → B₂ → B₃`, `B₁ → Y₊`, `Y₋ → B₂` (indices `0, …, 3`, `4 = Y₊`, `5 = Y₋`). -/
def tQ6 : Fin 6 → Fin 6 → Bool := fun i j ↦
  i == j || (i.val ≤ 3 && j.val ≤ 3 && i.val ≤ j.val) || (j.val == 4 && i.val ≤ 1) ||
    (i.val == 5 && (j.val == 2 || j.val == 3))

instance : Fact (Ax tQ6) := ⟨by unfold Ax; decide⟩

theorem tQ6_uniq : UniqOK tQ6 := by unfold UniqOK; decide

theorem tQ6_count : CountOK tQ6 ![1, 2, 2, 1, 1, 1] := by unfold CountOK; decide

section Q6

variable {b y : V} {q1 q2 q3 e qe l lq : R}
  (q11 : P.src q1 = b) (q12 : P.tgt q1 = b) (e1 : P.src e = b) (e2 : P.tgt e = y)
  (l1 : P.src l = y) (l2 : P.tgt l = b)
  (h11 : P.mul q1 q1 = some q2) (h12 : P.mul q1 q2 = some q3) (h21 : P.mul q2 q1 = some q3)
  (hqe : P.mul q1 e = some qe) (hlq : P.mul l q1 = some lq)
  (dq : 0 < P.deg (P.wt q1)) (de : 0 < P.deg (P.wt e)) (dl : 0 < P.deg (P.wt l))
  (Z1 : ∀ h, P.src h = b → P.tgt h = y → P.mul q1 h ≠ some e)
  (Z2 : ∀ h, P.src h = y → P.tgt h = b → P.mul e h ≠ some q1)
  (Z3 : ∀ h, P.src h = y → P.tgt h = b → P.wt h + P.wt e + P.wt q1 = P.wt q3 → False)
  (Z4 : ∀ h, P.src h = y → P.tgt h = b → P.wt h + P.wt q2 = P.wt q1 + P.wt l → False)
  (Z5 : ∀ h, P.src h = b → P.tgt h = y → P.wt h + P.wt l + P.wt q1 = P.wt q2 → False)
  (Z6 : ∀ h, P.src h = b → P.tgt h = y → P.wt h + P.wt l = P.wt q2 → False)

/-- The objects. -/
def q6V (b y : V) : Fin 6 → V := ![b, b, b, b, y, y]

/-- The weights. -/
def q6G (q1 q2 q3 e l : R) : Fin 6 → L :=
  ![0, P.wt q1, P.wt q2, P.wt q3, P.wt e + P.wt q1, P.wt q2 - P.wt l]

/-- The rays. -/
def q6ρ (b y : V) (q1 q2 q3 e qe l lq : R) : Fin 6 → Fin 6 → R :=
  ![![P.e b, q1, q2, q3, qe, P.e b],
    ![P.e b, P.e b, q1, q2, e, P.e b],
    ![P.e b, P.e b, P.e b, q1, P.e b, P.e b],
    ![P.e b, P.e b, P.e b, P.e b, P.e b, P.e b],
    ![P.e b, P.e b, P.e b, P.e b, P.e y, P.e b],
    ![P.e b, P.e b, l, lq, P.e b, P.e y]]

set_option maxHeartbeats 1000000 in
include q11 e1 l1 h11 h12 hqe hlq in
theorem q6_src : ∀ i j, tQ6 i j = true →
    P.src (P.q6ρ b y q1 q2 q3 e qe l lq i j) = q6V b y i := by
  have a1 := P.mul_src _ _ _ h11
  have a2 := P.mul_src _ _ _ h12
  have a3 := P.mul_src _ _ _ hqe
  have a4 := P.mul_src _ _ _ hlq
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [tQ6] at hij <;>
    simp [q6V, q6ρ, P.src_e, a1, a2, a3, a4, q11, e1, l1]

set_option maxHeartbeats 1000000 in
include q12 e2 l2 h11 h12 hqe hlq in
theorem q6_tgt : ∀ i j, tQ6 i j = true →
    P.tgt (P.q6ρ b y q1 q2 q3 e qe l lq i j) = q6V b y j := by
  have a1 := P.mul_tgt _ _ _ h11
  have a2 := P.mul_tgt _ _ _ h12
  have a3 := P.mul_tgt _ _ _ hqe
  have a4 := P.mul_tgt _ _ _ hlq
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [tQ6] at hij <;>
    simp [q6V, q6ρ, P.tgt_e, a1, a2, a3, a4, q12, e2, l2]

set_option maxHeartbeats 1000000 in
include h11 h12 hqe hlq in
theorem q6_wt : ∀ i j, tQ6 i j = true →
    P.wt (P.q6ρ b y q1 q2 q3 e qe l lq i j) = P.q6G q1 q2 q3 e l j - P.q6G q1 q2 q3 e l i := by
  have a1 := P.wt_mul _ _ _ h11
  have a2 := P.wt_mul _ _ _ h12
  have a3 := P.wt_mul _ _ _ hqe
  have a4 := P.wt_mul _ _ _ hlq
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [tQ6] at hij <;>
    simp [q6G, q6ρ, P.wt_e, a1, a2, a3, a4] <;> abel

set_option maxHeartbeats 2000000 in
include q11 q12 e1 e2 l1 l2 h11 h12 h21 hqe hlq in
theorem q6_mul : ∀ i j m, tQ6 i j = true → tQ6 j m = true →
    P.mul (P.q6ρ b y q1 q2 q3 e qe l lq i j) (P.q6ρ b y q1 q2 q3 e qe l lq j m) =
      some (P.q6ρ b y q1 q2 q3 e qe l lq i m) := by
  refine P.hmul_of_strict (q6V b y) _ (P.q6_src q11 e1 l1 h11 h12 hqe hlq)
    (P.q6_tgt q12 e2 l2 h11 h12 hqe hlq) (fun i ↦ by fin_cases i <;> rfl) ?_
  intro i j m a1 a2 a3 a4
  fin_cases i <;> fin_cases j <;> fin_cases m <;> simp [tQ6] at a1 a2 a3 a4 <;>
    simp [q6ρ, h11, h12, h21, hqe, hlq]

set_option maxHeartbeats 4000000 in
include h11 h12 hqe hlq dq de dl Z1 Z2 Z3 in
theorem q6_retL : ∀ i j m (h : R), covB tQ6 i j = true → tQ6 i m = true →
    P.src h = q6V b y j → P.tgt h = q6V b y m →
    P.wt h = P.q6G q1 q2 q3 e l m - P.q6G q1 q2 q3 e l j →
    P.mul (P.q6ρ b y q1 q2 q3 e qe l lq i j) h = some (P.q6ρ b y q1 q2 q3 e qe l lq i m) →
    tQ6 j m = true := by
  have a1 := congrArg P.deg (P.wt_mul _ _ _ h11)
  have a2 := congrArg P.deg (P.wt_mul _ _ _ h12)
  rw [map_add] at a1 a2
  intro i j m h hcv him h1 h2 h3 hm
  fin_cases i <;> fin_cases j <;> fin_cases m
  all_goals first
    | decide
    | exact absurd hcv (by decide)
    | exact absurd him (by decide)
    | skip
  all_goals simp [q6V, q6G, q6ρ] at h1 h2 h3 hm
  all_goals first
    | exact (Z1 h h1 h2 hm).elim
    | exact (Z2 h h1 h2 hm).elim
    | (refine (Z3 h h1 h2 ?_).elim; rw [h3]; abel1)
    | (exfalso; have hd := P.deg_nonneg h; rw [h3] at hd
       simp only [map_sub, map_neg, map_add, map_zero] at hd; linarith)

set_option maxHeartbeats 4000000 in
include h11 h12 hqe hlq dq de dl Z4 Z5 Z6 in
theorem q6_retR : ∀ i j m (h : R), covB tQ6 i j = true → tQ6 m j = true →
    P.src h = q6V b y m → P.tgt h = q6V b y i →
    P.wt h = P.q6G q1 q2 q3 e l i - P.q6G q1 q2 q3 e l m →
    P.mul h (P.q6ρ b y q1 q2 q3 e qe l lq i j) = some (P.q6ρ b y q1 q2 q3 e qe l lq m j) →
    tQ6 m i = true := by
  have a1 := congrArg P.deg (P.wt_mul _ _ _ h11)
  have a2 := congrArg P.deg (P.wt_mul _ _ _ h12)
  rw [map_add] at a1 a2
  intro i j m h hcv hmj h1 h2 h3 hm
  fin_cases i <;> fin_cases j <;> fin_cases m
  all_goals first
    | decide
    | exact absurd hcv (by decide)
    | exact absurd hmj (by decide)
    | skip
  all_goals simp [q6V, q6G, q6ρ] at h1 h2 h3 hm
  all_goals first
    | (refine (Z4 h h1 h2 ?_).elim; rw [h3]; abel1)
    | (refine (Z5 h h1 h2 ?_).elim; rw [h3]; abel1)
    | (refine (Z6 h h1 h2 ?_).elim; rw [h3]; abel1)
    | (exfalso; have hd := P.deg_nonneg h; rw [h3] at hd
       simp only [map_sub, map_neg, map_add, map_zero] at hd; linarith)

variable (k : Type u) [Field k] [IsAlgClosed k]

include q11 q12 e1 e2 l1 l2 h11 h12 h21 hqe hlq dq de dl Z1 Z2 Z3 Z4 Z5 Z6 in
/-- **The proper six-tree is excluded** (`eq:proper-six-tree`). -/
theorem q6_false (hfin : IsRepresentationFinite k (P.Lin k)) : False :=
  P.table_false (q6V b y) (P.q6G q1 q2 q3 e l) (P.q6ρ b y q1 q2 q3 e qe l lq)
    (P.q6_src q11 e1 l1 h11 h12 hqe hlq) (P.q6_tgt q12 e2 l2 h11 h12 hqe hlq)
    (P.q6_wt h11 h12 hqe hlq) (P.q6_mul q11 q12 e1 e2 l1 l2 h11 h12 h21 hqe hlq)
    (P.q6_retL h11 h12 hqe hlq dq de dl Z1 Z2 Z3)
    (P.q6_retR h11 h12 hqe hlq dq de dl Z4 Z5 Z6) k hfin
    ![1, 2, 2, 1, 1, 1] tQ6_uniq tQ6_count

end Q6

/-! ### The complementary-path tree (Appendix C.2, Step 3) -/

section C6

variable {x y z : V} {g f r s qx qz gq gr sg : R}
  (g1 : P.src g = z) (g2 : P.tgt g = x) (f1 : P.src f = x) (f2 : P.tgt f = z)
  (r1 : P.src r = x) (r2 : P.tgt r = y) (s1 : P.src s = y) (s2 : P.tgt s = z)
  (hgf : P.mul g f = some qz) (hfg : P.mul f g = some qx) (hgq : P.mul g qx = some gq)
  (hqg : P.mul qz g = some gq) (hgr : P.mul g r = some gr) (hsg : P.mul s g = some sg)
  (dg : 0 < P.deg (P.wt g)) (df : 0 < P.deg (P.wt f)) (dr : 0 < P.deg (P.wt r))
  (ds : 0 < P.deg (P.wt s))
  (W1 : ∀ h, P.src h = z → P.tgt h = y → P.mul f h ≠ some r)
  (W2 : ∀ h, P.src h = y → P.tgt h = z → P.wt r + P.wt h = P.wt f → False)
  (W3 : ∀ h, P.src h = y → P.tgt h = x → P.mul r h ≠ some qx)
  (W4 : ∀ h, P.src h = y → P.tgt h = x → P.mul h f ≠ some s)
  (W5 : ∀ h, P.src h = x → P.tgt h = y → P.wt h + P.wt s = P.wt f → False)
  (W6 : ∀ h, P.src h = z → P.tgt h = y → P.mul h s ≠ some qz)

/-- The objects. -/
def c6V (x y z : V) : Fin 6 → V := ![z, x, z, x, y, y]

/-- The weights. -/
def c6G (g f r s : R) : Fin 6 → L :=
  ![0, P.wt g, P.wt g + P.wt f, P.wt g + P.wt f + P.wt g, P.wt g + P.wt r,
    P.wt g + P.wt f - P.wt s]

/-- The rays. -/
def c6ρ (x y z : V) (g f r s qx qz gq gr sg : R) : Fin 6 → Fin 6 → R :=
  ![![P.e z, g, qz, gq, gr, P.e z],
    ![P.e z, P.e x, f, qx, r, P.e z],
    ![P.e z, P.e z, P.e z, g, P.e z, P.e z],
    ![P.e z, P.e z, P.e z, P.e x, P.e z, P.e z],
    ![P.e z, P.e z, P.e z, P.e z, P.e y, P.e z],
    ![P.e z, P.e z, s, sg, P.e z, P.e y]]

set_option maxHeartbeats 1000000 in
include g1 f1 r1 s1 hgf hfg hgq hgr hsg in
theorem c6_src : ∀ i j, tQ6 i j = true →
    P.src (P.c6ρ x y z g f r s qx qz gq gr sg i j) = c6V x y z i := by
  have a1 := P.mul_src _ _ _ hgf
  have a2 := P.mul_src _ _ _ hfg
  have a3 := P.mul_src _ _ _ hgq
  have a4 := P.mul_src _ _ _ hgr
  have a5 := P.mul_src _ _ _ hsg
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [tQ6] at hij <;>
    simp [c6V, c6ρ, P.src_e, a1, a2, a3, a4, a5, g1, f1, r1, s1]

set_option maxHeartbeats 1000000 in
include g2 f2 r2 s2 hgf hfg hgq hgr hsg in
theorem c6_tgt : ∀ i j, tQ6 i j = true →
    P.tgt (P.c6ρ x y z g f r s qx qz gq gr sg i j) = c6V x y z j := by
  have a1 := P.mul_tgt _ _ _ hgf
  have a2 := P.mul_tgt _ _ _ hfg
  have a3 := P.mul_tgt _ _ _ hgq
  have a4 := P.mul_tgt _ _ _ hgr
  have a5 := P.mul_tgt _ _ _ hsg
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [tQ6] at hij <;>
    simp [c6V, c6ρ, P.tgt_e, a1, a2, a3, a4, a5, g2, f2, r2, s2]

set_option maxHeartbeats 1000000 in
include hgf hfg hgq hgr hsg in
theorem c6_wt : ∀ i j, tQ6 i j = true →
    P.wt (P.c6ρ x y z g f r s qx qz gq gr sg i j) = P.c6G g f r s j - P.c6G g f r s i := by
  have a1 := P.wt_mul _ _ _ hgf
  have a2 := P.wt_mul _ _ _ hfg
  have a3 := P.wt_mul _ _ _ hgq
  have a4 := P.wt_mul _ _ _ hgr
  have a5 := P.wt_mul _ _ _ hsg
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [tQ6] at hij <;>
    simp [c6G, c6ρ, P.wt_e, a1, a2, a3, a4, a5] <;> abel

set_option maxHeartbeats 2000000 in
include g1 g2 f1 f2 r1 r2 s1 s2 hgf hfg hgq hqg hgr hsg in
theorem c6_mul : ∀ i j m, tQ6 i j = true → tQ6 j m = true →
    P.mul (P.c6ρ x y z g f r s qx qz gq gr sg i j) (P.c6ρ x y z g f r s qx qz gq gr sg j m) =
      some (P.c6ρ x y z g f r s qx qz gq gr sg i m) := by
  refine P.hmul_of_strict (c6V x y z) _ (P.c6_src g1 f1 r1 s1 hgf hfg hgq hgr hsg)
    (P.c6_tgt g2 f2 r2 s2 hgf hfg hgq hgr hsg) (fun i ↦ by fin_cases i <;> rfl) ?_
  intro i j m a1 a2 a3 a4
  fin_cases i <;> fin_cases j <;> fin_cases m <;> simp [tQ6] at a1 a2 a3 a4 <;>
    simp [c6ρ, hgf, hfg, hgq, hqg, hgr, hsg]

set_option maxHeartbeats 4000000 in
include hgf hfg hgq hgr hsg dg df dr ds W1 W2 W3 in
theorem c6_retL : ∀ i j m (h : R), covB tQ6 i j = true → tQ6 i m = true →
    P.src h = c6V x y z j → P.tgt h = c6V x y z m →
    P.wt h = P.c6G g f r s m - P.c6G g f r s j →
    P.mul (P.c6ρ x y z g f r s qx qz gq gr sg i j) h =
      some (P.c6ρ x y z g f r s qx qz gq gr sg i m) → tQ6 j m = true := by
  intro i j m h hcv him h1 h2 h3 hm
  fin_cases i <;> fin_cases j <;> fin_cases m
  all_goals first
    | decide
    | exact absurd hcv (by decide)
    | exact absurd him (by decide)
    | skip
  all_goals simp [c6V, c6G, c6ρ] at h1 h2 h3 hm
  all_goals first
    | (exfalso; have hd := P.deg_nonneg h; rw [h3] at hd
       simp only [map_sub, map_neg, map_add, map_zero] at hd; linarith)
    | exact (W1 h h1 h2 hm).elim
    | exact (W3 h h1 h2 hm).elim
    | (refine (W2 h h1 h2 ?_).elim; rw [h3]; abel1)

set_option maxHeartbeats 4000000 in
include hgf hfg hgq hgr hsg dg df dr ds W4 W5 W6 in
theorem c6_retR : ∀ i j m (h : R), covB tQ6 i j = true → tQ6 m j = true →
    P.src h = c6V x y z m → P.tgt h = c6V x y z i →
    P.wt h = P.c6G g f r s i - P.c6G g f r s m →
    P.mul h (P.c6ρ x y z g f r s qx qz gq gr sg i j) =
      some (P.c6ρ x y z g f r s qx qz gq gr sg m j) → tQ6 m i = true := by
  intro i j m h hcv hmj h1 h2 h3 hm
  fin_cases i <;> fin_cases j <;> fin_cases m
  all_goals first
    | decide
    | exact absurd hcv (by decide)
    | exact absurd hmj (by decide)
    | skip
  all_goals simp [c6V, c6G, c6ρ] at h1 h2 h3 hm
  all_goals first
    | (exfalso; have hd := P.deg_nonneg h; rw [h3] at hd
       simp only [map_sub, map_neg, map_add, map_zero] at hd; linarith)
    | exact (W4 h h1 h2 hm).elim
    | exact (W6 h h1 h2 hm).elim
    | (refine (W5 h h1 h2 ?_).elim; rw [h3]; abel1)

variable (k : Type u) [Field k] [IsAlgClosed k]

include g1 g2 f1 f2 r1 r2 s1 s2 hgf hfg hgq hqg hgr hsg dg df dr ds W1 W2 W3 W4 W5 W6 in
/-- **The complementary-path tree is excluded** (Appendix C.2, Step 3). -/
theorem c6_false (hfin : IsRepresentationFinite k (P.Lin k)) : False :=
  P.table_false (c6V x y z) (P.c6G g f r s) (P.c6ρ x y z g f r s qx qz gq gr sg)
    (P.c6_src g1 f1 r1 s1 hgf hfg hgq hgr hsg) (P.c6_tgt g2 f2 r2 s2 hgf hfg hgq hgr hsg)
    (P.c6_wt hgf hfg hgq hgr hsg) (P.c6_mul g1 g2 f1 f2 r1 r2 s1 s2 hgf hfg hgq hqg hgr hsg)
    (P.c6_retL hgf hfg hgq hgr hsg dg df dr ds W1 W2 W3)
    (P.c6_retR hgf hfg hgq hgr hsg dg df dr ds W4 W5 W6) k hfin
    ![1, 2, 2, 1, 1, 1] tQ6_uniq tQ6_count

end C6

end Tab

end RaySys

end MultiplicativeBasisDeformations
