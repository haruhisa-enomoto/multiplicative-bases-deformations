module

public import MultiplicativeBasisDeformations.Foundations.PeriodicGauge
public import MultiplicativeBasisDeformations.Foundations.OrbitReps
public import MultiplicativeBasisDeformations.Foundations.StarCorner

/-!
# The periodic gauge on a star model (Lemma A.1(1))

`lem:periodic-scalar-gauges` (1), `periodic-mesh-calculations.tex`, for
`Q = ℤΔ / ⟨g⟩` with `Δ` a star rooted at its centre, `g (v, t) = (σ v, t + c₀)`
and `σ` fixing the centre and permuting the arms by `θ`.

The coefficients are recorded by `Cf w w' h`, the coefficient at `(w, h + 2)` of
the arrow from `(w', h + 1)`, invariant under `g`. The unknowns are the arrow
scales `M e h` (the arrow over the edge with child endpoint `e` at source height
`h`) and the relation scales `N v h`. On the representative arm of each
`θ`-orbit the edges are treated down the arm (`reps`): the parent's relation
scales are known, and `exists_periodic_line_vertex` gives the arrow scales and
the child's relation scales, with period `per · c₀`. The other arms of the orbit
are obtained by applying `g`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace StarGauge

open StarCorner OrbitReps

variable {k : Type u} [CommRing k] {t : ℕ} {L : Fin t → ℕ}

/-- The parent of the vertex `j` of arm `i`. -/
def pa (i : Fin t) (j : ℕ) (h : j ≤ L i) : StarV L :=
  if hj : j = 0 then none else some ⟨i, ⟨j - 1, by omega⟩⟩

/-- The vertex `j` of arm `i`. -/
def ch (i : Fin t) (j : ℕ) (h : j ≤ L i) : StarV L := some ⟨i, ⟨j, by omega⟩⟩

variable (Cf : StarV L → StarV L → ℤ → kˣ) (sg : StarV L → StarV L → kˣ)

/-- The prescribed products on the edge line with child `ch i j`, given the
relation scales `Np` of the parent. -/
def lineS (i : Fin t) (j : ℕ) (h : j ≤ L i) (Np : ℤ → kˣ) (s : ℤ) : kˣ :=
  if (s : ZMod 2) = ((j + 1 : ℕ) : ZMod 2) then
    sg (ch i j h) (pa i j h) * (Cf (ch i j h) (pa i j h) s)⁻¹
  else sg (pa i j h) (ch i j h) * (Np (s + 2) * Cf (pa i j h) (ch i j h) s)⁻¹

open Classical in
/-- One step down an arm: the child's relation scales and the edge's arrow
scales. -/
def step (P : ℕ) (i : Fin t) (j : ℕ) (h : j ≤ L i) (Np : ℤ → kˣ) : (ℤ → kˣ) × (ℤ → kˣ) :=
  if hP : 0 < P ∧ Even P ∧ ∀ s, lineS Cf sg i j h Np (s + P) = lineS Cf sg i j h Np s then
    ((exists_periodic_line_vertex P hP.1 hP.2.1 _ hP.2.2 ((j + 1 : ℕ) : ZMod 2)).choose,
      (exists_periodic_line_vertex P hP.1 hP.2.1 _ hP.2.2 ((j + 1 : ℕ) : ZMod 2)).choose_spec.choose)
  else (fun _ ↦ 1, fun _ ↦ 1)

theorem step_spec (P : ℕ) (i : Fin t) (j : ℕ) (h : j ≤ L i) (Np : ℤ → kˣ) (hP : 0 < P)
    (hPe : Even P) (hS : ∀ s, lineS Cf sg i j h Np (s + P) = lineS Cf sg i j h Np s) :
    (∀ s, (step Cf sg P i j h Np).1 (s + P) = (step Cf sg P i j h Np).1 s) ∧
    (∀ s, (step Cf sg P i j h Np).2 (s + P) = (step Cf sg P i j h Np).2 s) ∧
    ∀ s, (step Cf sg P i j h Np).2 s * (step Cf sg P i j h Np).2 (s + 1) *
      (if (s : ZMod 2) = ((j + 1 : ℕ) : ZMod 2) then (step Cf sg P i j h Np).1 (s + 2) else 1) =
        lineS Cf sg i j h Np s := by
  unfold step
  rw [dif_pos ⟨hP, hPe, hS⟩]
  exact (exists_periodic_line_vertex P hP hPe _ hS _).choose_spec.choose_spec

/-- The scales down a representative arm `i₀`. -/
def reps (P : ℕ) (i : Fin t) : ℕ → (ℤ → kˣ) × (ℤ → kˣ)
  | 0 => step Cf sg P i 0 (Nat.zero_le _) (fun _ ↦ 1)
  | j + 1 => if h : j + 1 ≤ L i then step Cf sg P i (j + 1) h (reps P i j).1
      else (fun _ ↦ 1, fun _ ↦ 1)

theorem reps_succ (P : ℕ) (i : Fin t) (j : ℕ) (h : j + 1 ≤ L i) :
    reps Cf sg P i (j + 1) = step Cf sg P i (j + 1) h (reps Cf sg P i j).1 := by
  rw [reps, dif_pos h]

/-- The relation scales of the parent of the vertex `j` of the arm. -/
def parN (P : ℕ) (i : Fin t) (j : ℕ) : ℤ → kˣ :=
  if j = 0 then fun _ ↦ 1 else (reps Cf sg P i (j - 1)).1

theorem reps_eq_step (P : ℕ) (i : Fin t) (j : ℕ) (h : j ≤ L i) :
    reps Cf sg P i j = step Cf sg P i j h (parN Cf sg P i j) := by
  rcases j with _ | j
  · rfl
  · rw [reps_succ Cf sg P i j h]; rfl

variable (P : ℕ) (hP : 0 < P) (hPe : Even P) (i : Fin t)
  (hper : ∀ (j : ℕ) (h : j ≤ L i) (s : ℤ),
    Cf (ch i j h) (pa i j h) (s + P) = Cf (ch i j h) (pa i j h) s ∧
    Cf (pa i j h) (ch i j h) (s + P) = Cf (pa i j h) (ch i j h) s)

include hPe hper in
theorem lineS_periodic (j : ℕ) (h : j ≤ L i) (Np : ℤ → kˣ) (hNp : ∀ s, Np (s + P) = Np s) (s : ℤ) :
    lineS Cf sg i j h Np (s + P) = lineS Cf sg i j h Np s := by
  have hP2 : ((s + P : ℤ) : ZMod 2) = (s : ZMod 2) := by
    obtain ⟨r, hr⟩ := hPe
    rw [hr]; push_cast
    rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]
  unfold lineS
  rw [hP2, (hper j h s).1, (hper j h s).2, show s + P + 2 = (s + 2) + P by ring, hNp]

include hP hPe hper in
/-- **The scales down a representative arm** are `P`-periodic and solve the edge
equations. -/
theorem reps_spec (j : ℕ) (h : j ≤ L i) :
    (∀ s, (reps Cf sg P i j).1 (s + P) = (reps Cf sg P i j).1 s) ∧
    (∀ s, (reps Cf sg P i j).2 (s + P) = (reps Cf sg P i j).2 s) ∧
    ∀ s, (reps Cf sg P i j).2 s * (reps Cf sg P i j).2 (s + 1) *
      (if (s : ZMod 2) = ((j + 1 : ℕ) : ZMod 2) then (reps Cf sg P i j).1 (s + 2) else 1) =
        lineS Cf sg i j h (parN Cf sg P i j) s := by
  induction j with
  | zero =>
      rw [reps_eq_step Cf sg P i 0 h]
      exact step_spec Cf sg P i 0 h _ hP hPe
        (lineS_periodic Cf sg P hPe i hper 0 h _ (by simp [parN]))
  | succ j ih =>
      rw [reps_eq_step Cf sg P i (j + 1) h]
      have hpar : ∀ s, parN Cf sg P i (j + 1) (s + P) = parN Cf sg P i (j + 1) s := by
        simp only [parN, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]
        exact (ih (by omega)).1
      exact step_spec Cf sg P i (j + 1) h _ hP hPe
        (lineS_periodic Cf sg P hPe i hper (j + 1) h _ hpar)

/-! ### Transport along the orbit -/

theorem ch_congr {i i' : Fin t} (e : i = i') (j : ℕ) (h : j ≤ L i) (h' : j ≤ L i') :
    ch i j h = ch i' j h' := by subst e; rfl

theorem pa_congr {i i' : Fin t} (e : i = i') (j : ℕ) (h : j ≤ L i) (h' : j ≤ L i') :
    pa i j h = pa i' j h' := by subst e; rfl

variable (θ : Equiv.Perm (Fin t)) (hL : ∀ i, L (θ i) = L i)
  (σ : StarV L ≃ StarV L) (hσo : σ none = none)
  (hθ : ∀ i j (h : j ≤ L i), σ (ch i j h) = ch (θ i) j (h.trans (hL i).ge))

include hL in
theorem L_pow (n : ℕ) (i : Fin t) : L ((θ ^ n) i) = L i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hL, ih]

include hθ in
theorem pow_ch (n : ℕ) (i : Fin t) (j : ℕ) (h : j ≤ L i) :
    (σ ^ n) (ch i j h) = ch ((θ ^ n) i) j (by rw [L_pow θ hL]; exact h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, hθ]
      exact ch_congr (by rw [pow_succ', Equiv.Perm.mul_apply]) _ _ _

include hθ hσo in
theorem pow_pa (n : ℕ) (i : Fin t) (j : ℕ) (h : j ≤ L i) :
    (σ ^ n) (pa i j h) = pa ((θ ^ n) i) j (by rw [L_pow θ hL]; exact h) := by
  unfold pa
  split_ifs with hj
  · induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hσo]
  · have := pow_ch θ hL σ hθ n i (j - 1) (by omega)
    exact this

variable (c0 : ℕ) (hCinv : ∀ w w' s, Cf (σ w) (σ w') (s + c0) = Cf w w' s)

include hCinv in
theorem Cf_pow (n : ℕ) (w w' : StarV L) (s : ℤ) :
    Cf ((σ ^ n) w) ((σ ^ n) w') (s + n * c0) = Cf w w' s := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        show s + ((n + 1 : ℕ) : ℤ) * c0 = (s + n * c0) + c0 by push_cast; ring, hCinv, ih]

variable (hsg : ∀ w w', sg (σ w) (σ w') = sg w w')

include hsg in
theorem sg_pow (n : ℕ) (w w' : StarV L) : sg ((σ ^ n) w) ((σ ^ n) w') = sg w w' := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsg, ih]

/-- The period of the edge lines on the orbit of the arm `i`. -/
def Pof (i : Fin t) : ℕ := per θ i * c0

/-- The relation scales. -/
def Nf : StarV L → ℤ → kˣ
  | none => fun _ ↦ 1
  | some ⟨i, ⟨j, _⟩⟩ => fun s ↦ (reps Cf sg (Pof θ c0 i) (rep θ i) j).1 (s - ord θ i * c0)

/-- The arrow scales, indexed by the child endpoint of the edge. -/
def Mf : StarV L → ℤ → kˣ
  | none => fun _ ↦ 1
  | some ⟨i, ⟨j, _⟩⟩ => fun s ↦ (reps Cf sg (Pof θ c0 i) (rep θ i) j).2 (s - ord θ i * c0)

include hL in
theorem L_rep (i : Fin t) : L (rep θ i) = L i := by
  conv_rhs => rw [← pow_ord θ i]
  exact (L_pow θ hL _ _).symm

include hL hσo hθ hCinv hsg in
/-- **The edge equations hold on every arm.** -/
theorem edge_eq (hc0 : 0 < c0) (hc0e : Even c0) (i : Fin t) (j : ℕ) (h : j ≤ L i) (s : ℤ) :
    Mf Cf sg θ c0 (ch i j h) s * Mf Cf sg θ c0 (ch i j h) (s + 1) *
      (if (s : ZMod 2) = ((j + 1 : ℕ) : ZMod 2) then Nf Cf sg θ c0 (ch i j h) (s + 2) else 1) =
        lineS Cf sg i j h (Nf Cf sg θ c0 (pa i j h)) s := by
  set i₀ := rep θ i
  set n := ord θ i
  have h₀ : j ≤ L i₀ := by rw [L_rep θ hL]; exact h
  have hn : (θ ^ n) i₀ = i := pow_ord θ i
  have hP : 0 < Pof θ c0 i := Nat.mul_pos (per_pos θ i) hc0
  have hPe : Even (Pof θ c0 i) := hc0e.mul_left _
  -- periodicity on the representative arm
  have hper : ∀ (j : ℕ) (h : j ≤ L i₀) (s : ℤ),
      Cf (ch i₀ j h) (pa i₀ j h) (s + Pof θ c0 i) = Cf (ch i₀ j h) (pa i₀ j h) s ∧
      Cf (pa i₀ j h) (ch i₀ j h) (s + Pof θ c0 i) = Cf (pa i₀ j h) (ch i₀ j h) s := by
    intro j h s
    have hp : (θ ^ per θ i) i₀ = i₀ := pow_per θ i
    have e1 := Cf_pow Cf σ c0 hCinv (per θ i) (ch i₀ j h) (pa i₀ j h) s
    have e2 := Cf_pow Cf σ c0 hCinv (per θ i) (pa i₀ j h) (ch i₀ j h) s
    rw [pow_ch θ hL σ hθ, pow_pa θ hL σ hσo hθ, ch_congr hp _ _ h, pa_congr hp _ _ h] at e1 e2
    simp only [Pof]; push_cast
    exact ⟨e1, e2⟩
  obtain ⟨-, -, hspec⟩ := reps_spec Cf sg (Pof θ c0 i) hP hPe i₀ hper j h₀
  clear hper
  have hs := hspec (s - n * c0)
  have hpar : ((s - n * c0 : ℤ) : ZMod 2) = (s : ZMod 2) := by
    obtain ⟨r, hr⟩ := hc0e
    push_cast; rw [hr]; push_cast
    rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, mul_zero]; exact sub_zero _
  -- the left side
  have eL : Mf Cf sg θ c0 (ch i j h) s * Mf Cf sg θ c0 (ch i j h) (s + 1) *
      (if (s : ZMod 2) = ((j + 1 : ℕ) : ZMod 2) then Nf Cf sg θ c0 (ch i j h) (s + 2) else 1) =
      (reps Cf sg (Pof θ c0 i) i₀ j).2 (s - n * c0) *
        (reps Cf sg (Pof θ c0 i) i₀ j).2 (s - n * c0 + 1) *
        (if ((s - n * c0 : ℤ) : ZMod 2) = ((j + 1 : ℕ) : ZMod 2) then
          (reps Cf sg (Pof θ c0 i) i₀ j).1 (s - n * c0 + 2) else 1) := by
    rw [hpar]
    simp only [Mf, Nf, ch]
    rw [show s + 1 - n * c0 = s - n * c0 + 1 by ring, show s + 2 - n * c0 = s - n * c0 + 2 by ring]
  rw [eL, hs]
  -- the right side
  have hch : (σ ^ n) (ch i₀ j h₀) = ch i j h := (pow_ch θ hL σ hθ n i₀ j h₀).trans
    (ch_congr hn _ _ _)
  have hpa : (σ ^ n) (pa i₀ j h₀) = pa i j h := (pow_pa θ hL σ hσo hθ n i₀ j h₀).trans
    (pa_congr hn _ _ _)
  unfold lineS
  rw [hpar, ← Cf_pow Cf σ c0 hCinv n (ch i₀ j h₀) (pa i₀ j h₀) (s - n * c0),
    ← Cf_pow Cf σ c0 hCinv n (pa i₀ j h₀) (ch i₀ j h₀) (s - n * c0),
    ← sg_pow sg σ hsg n (ch i₀ j h₀) (pa i₀ j h₀), ← sg_pow sg σ hsg n (pa i₀ j h₀) (ch i₀ j h₀),
    hch, hpa, show s - n * c0 + n * c0 = s by ring]
  congr 2
  -- the parent's relation scales
  unfold parN pa
  split_ifs with hj
  · rfl
  · simp only [Nf]
    rw [show s + 2 - n * c0 = s - n * c0 + 2 by ring]

include hL hσo hθ hCinv in
theorem reps_periodic (hc0 : 0 < c0) (hc0e : Even c0) (i : Fin t) (j : ℕ) (h : j ≤ L i) :
    Function.Periodic (reps Cf sg (Pof θ c0 i) (rep θ i) j).1 (Pof θ c0 i) ∧
    Function.Periodic (reps Cf sg (Pof θ c0 i) (rep θ i) j).2 (Pof θ c0 i) := by
  set i₀ := rep θ i
  have h₀ : j ≤ L i₀ := by rw [L_rep θ hL]; exact h
  have hP : 0 < Pof θ c0 i := Nat.mul_pos (per_pos θ i) hc0
  have hPe : Even (Pof θ c0 i) := hc0e.mul_left _
  have hper : ∀ (j : ℕ) (h : j ≤ L i₀) (s : ℤ),
      Cf (ch i₀ j h) (pa i₀ j h) (s + Pof θ c0 i) = Cf (ch i₀ j h) (pa i₀ j h) s ∧
      Cf (pa i₀ j h) (ch i₀ j h) (s + Pof θ c0 i) = Cf (pa i₀ j h) (ch i₀ j h) s := by
    intro j h s
    have hp : (θ ^ per θ i) i₀ = i₀ := pow_per θ i
    have e1 := Cf_pow Cf σ c0 hCinv (per θ i) (ch i₀ j h) (pa i₀ j h) s
    have e2 := Cf_pow Cf σ c0 hCinv (per θ i) (pa i₀ j h) (ch i₀ j h) s
    rw [pow_ch θ hL σ hθ, pow_pa θ hL σ hσo hθ, ch_congr hp _ _ h, pa_congr hp _ _ h] at e1 e2
    simp only [Pof]; push_cast
    exact ⟨e1, e2⟩
  obtain ⟨h1, h2, -⟩ := reps_spec Cf sg (Pof θ c0 i) hP hPe i₀ hper j h₀
  exact ⟨fun s ↦ by exact_mod_cast h1 s, fun s ↦ by exact_mod_cast h2 s⟩

theorem Pof_apply (i : Fin t) : Pof θ c0 (θ i) = Pof θ c0 i := by simp only [Pof, per_apply]

theorem shift_eq (i : Fin t) (s : ℤ) : ∃ q : ℤ,
    s + c0 - (ord θ (θ i) : ℤ) * c0 = (s - ord θ i * c0) + q * (Pof θ c0 i : ℕ) := by
  obtain ⟨q, hq⟩ := ord_apply θ i
  exact ⟨q, by simp only [Pof]; push_cast; linear_combination (c0 : ℤ) * hq⟩

include hL hσo hθ hCinv in
/-- **The relation scales are `g`-invariant.** -/
theorem Nf_inv (hc0 : 0 < c0) (hc0e : Even c0) (v : StarV L) (s : ℤ) :
    Nf Cf sg θ c0 (σ v) (s + c0) = Nf Cf sg θ c0 v s := by
  rcases v with _ | ⟨i, ⟨j, hj⟩⟩
  · rw [hσo]; rfl
  · have h : j ≤ L i := Nat.lt_succ_iff.1 hj
    have e := hθ i j h
    change Nf Cf sg θ c0 (σ (ch i j h)) (s + c0) = _
    rw [e]
    simp only [Nf, ch]
    obtain ⟨q, hq⟩ := shift_eq θ c0 i s
    rw [hq, rep_apply, Pof_apply]
    exact (reps_periodic Cf sg θ hL σ hσo hθ c0 hCinv hc0 hc0e i j h).1.int_mul q _

include hL hσo hθ hCinv in
/-- **The arrow scales are `g`-invariant.** -/
theorem Mf_inv (hc0 : 0 < c0) (hc0e : Even c0) (v : StarV L) (s : ℤ) :
    Mf Cf sg θ c0 (σ v) (s + c0) = Mf Cf sg θ c0 v s := by
  rcases v with _ | ⟨i, ⟨j, hj⟩⟩
  · rw [hσo]; rfl
  · have h : j ≤ L i := Nat.lt_succ_iff.1 hj
    have e := hθ i j h
    change Mf Cf sg θ c0 (σ (ch i j h)) (s + c0) = _
    rw [e]
    simp only [Mf, ch]
    obtain ⟨q, hq⟩ := shift_eq θ c0 i s
    rw [hq, rep_apply, Pof_apply]
    exact (reps_periodic Cf sg θ hL σ hσo hθ c0 hCinv hc0 hc0e i j h).2.int_mul q _

end StarGauge

end MultiplicativeBasisDeformations
