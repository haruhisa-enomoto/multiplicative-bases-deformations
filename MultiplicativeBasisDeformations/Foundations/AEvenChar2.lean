import MultiplicativeBasisDeformations.Foundations.AEven
import MultiplicativeBasisDeformations.Foundations.ASort
import MultiplicativeBasisDeformations.Foundations.AReflectChar2
import MultiplicativeBasisDeformations.Foundations.TreeEmbed
import MultiplicativeBasisDeformations.Foundations.EvenLineTop

/-!
# The odd quotients of even `A` in characteristic two (Appendix B)

`characteristic-two-mesh-calculations.tex`: "For the odd quotient of `A_{2n}` with
period `r`, … If `r ≤ 2n − 1`, retain the first `(r+1)/2` levels. The top paths of the
resulting even-`A` tree have degree `r`, go to reflected vertices, and increase the
repetition coordinate by `r`. They are nonzero radical endomorphisms at every quotient
object. Thus `r > 2n − 1`. A path from `τv` to `v` starts and ends at the same level and
has degree `d ≡ 2` modulo `r`, whereas `d ≤ 2n − 1 < r`. Again no degree at least three
is possible."

This file: the second part (`a_even_long`). A row of degree `m + 1 ≥ 3` lifts to a path
of length `2 + n r ≥ 2 + r > 2n`, which vanishes in `Π(A_{2n})` (`ASort.long_mem`);
in characteristic two the all-one coefficients are the signed ones, so it gives the
zero class (`phiL_eq_zero_of_mem`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w

namespace StarTrace

open OrientedTree ScalarMeshCategory StarGauge EvenA

variable {L : Fin 1 → ℕ}
  {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : (starTree L).ZVert ⥤q V)
  {k : Type u} [Field k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]
  [Fintype Q.nonprojective]
  (hπ : π.IsCovering) (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y))
  (hsurj : ∀ x : V, ∃ X, π.obj X = x)
  (ρ : StarV L ≃ StarV L) (hρ : ∀ a b, (starTree L).G.Adj (ρ a) (ρ b) ↔ (starTree L).G.Adj a b)
  (c0 : ℕ) (hc0 : 0 < c0)
  (hρp : ∀ v, (starTree L).par (ρ v) = (starTree L).par v + ((c0 : ℤ) : ZMod 2))
  (hdeck : ∀ Z, π.obj (((starTree L).zAct ρ hρ (c0 : ℤ) hρp).obj Z) = π.obj Z)
  (hfib : ∀ X Y : (starTree L).ZVert, π.obj X = π.obj Y →
    ∃ n : ℕ, Y = (gZ ρ hρ c0 hρp)^[n] X ∨ X = (gZ ρ hρ c0 hρp)^[n] Y)

theorem zSigned_char2 {D : Type*} (T : OrientedTree D) [DecidableRel T.orient] (hchar : (2 : k) = 0) :
    T.zSigned k = fun _ _ _ ↦ 1 := by
  funext X Y A
  unfold OrientedTree.zSigned OrientedTree.sgn
  split_ifs
  · rfl
  · apply Units.ext
    simp only [Units.val_neg, Units.val_one]
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, hchar]

include hπ hτ hsurj hc0 hdeck hfib in
/-- **Odd quotients of `A_{2n}` with period at least `2n`**: in characteristic two the
derivatives are surjective. -/
theorem a_even_long (hchar : (2 : k) = 0) (h : ℕ) (hh : 1 ≤ h) (hL : L 0 = 2 * h - 2)
    (hrev : ∀ x, starDepth (ρ x) + starDepth x = L 0 + 1) (hr : 2 * h ≤ c0)
    (c : MeshCoefficients k Q) (m : ℕ) (hm : 2 ≤ m) : MeshDerivativeSurjective c m := by
  -- `c₀` is odd: the reversal changes the parity of depths
  have hodd : Odd c0 := by
    have h1 := hρp none
    have h3 := hrev none
    change ((starDepth (ρ none) : ℕ) : ZMod 2) = ((starDepth (none : StarV L) : ℕ) : ZMod 2) + _
      at h1
    have h3' : starDepth (ρ none) = 2 * h - 1 := by
      have h4 : starDepth (none : StarV L) = 0 := rfl
      rw [h4, add_zero, hL] at h3; omega
    rw [h3'] at h1
    simp only [starDepth, Nat.cast_zero, zero_add] at h1
    rcases Nat.even_or_odd c0 with he | ho
    · exfalso
      obtain ⟨r, hr⟩ := he
      rw [hr] at h1
      obtain ⟨q, hq⟩ : ∃ q, 2 * h - 1 = 2 * q + 1 := ⟨h - 1, by omega⟩
      rw [hq] at h1; push_cast at h1
      rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_mul, zero_add] at h1
      exact absurd h1 (by decide)
    · exact ho
  -- normalize the coefficients to one, which are the signed ones
  obtain ⟨μ, η, hone⟩ := OddGauge.exists_one_gauge hQ π hπ c ρ hρ c0 hρp hdeck h hh hL hrev hτ
    hsurj hfib hodd
  set c' : MeshCoefficients k Q := fun x y a ↦ η x * c x y a * μ (Q.mate x y a) * μ a
  have hgauge : ∀ (x : Q.nonprojective) (y : V) (a : y ⟶ x.1),
      c x y a = (η x)⁻¹ * c' x y a * (μ (Q.mate x y a))⁻¹ * (μ a)⁻¹ :=
    gauge_symm (fun a ↦ μ a) η c c' (fun _ _ _ ↦ rfl)
  refine surjective_gauge (fun a ↦ (μ a)⁻¹) (fun x ↦ (η x)⁻¹) c' c hgauge ?_
  have hsig : (starTree L).pullCoeff hQ π c' = (starTree L).zSigned k := by
    rw [hone, zSigned_char2 _ hchar]
  rw [surjective_iff_rows]
  intro x p hp
  rw [← Submodule.Quotient.mk_eq_zero]
  change rowClass c' m x p = 0
  obtain ⟨n, X, P, hn, hPlen, hrow⟩ := row_lift hQ π c' hπ hτ hsurj ρ hρ c0 hc0 hρp hfib
    (by omega) x p hp
  rw [hrow]
  set p' : Quiver.Path ((starTree L).toDbl X.v) (((gPow ρ hρ c0 hρp n).obj X).v) :=
    (starTree L).forget.mapPath P
  have r2 : (starTree L).rowZ hQ π c' m P = (starTree L).phiD hQ π c' m X p' := by
    apply (starTree L).rowZ_eq_of_pathStar
    apply (starTree L).pathStar_eq_of_forget
    rw [forget_mapPath_liftZ]
    rfl
  rw [r2]
  have hlen : L 0 + 2 ≤ p'.length := by
    rw [LinearPaths.length_mapPath, hPlen]
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | h'
      · simp at hn; omega
      · exact h'
    have : c0 ≤ n * c0 := Nat.le_mul_of_pos_left c0 hn1
    push_cast at hn
    omega
  have hmem := ASort.long_mem k p' hlen
  have := (starTree L).phiL_eq_zero_of_mem hQ π c' hπ hτ hsig m X hmem
  rwa [OrientedTree.phiL, LinearPaths.extend_path] at this

/-! ### Short periods: deletion to a middle interval -/

section Short

variable {t : ℕ} {L' : Fin t → ℕ}
  (π' : (starTree L').ZVert ⥤q V) (hπ' : π'.IsCovering)
  (hτ' : ∀ Y, π'.obj ((starTree L').ztau Y) = hQ.tauE (π'.obj Y))
  (hsurj' : ∀ x : V, ∃ X, π'.obj X = x)
  (ρ' : StarV L' ≃ StarV L') (hρ' : ∀ a b, (starTree L').G.Adj (ρ' a) (ρ' b) ↔ (starTree L').G.Adj a b)
  (c0' : ℕ) (hρp' : ∀ v, (starTree L').par (ρ' v) = (starTree L').par v + ((c0' : ℤ) : ZMod 2))
  (hdeck' : ∀ Z, π'.obj (((starTree L').zAct ρ' hρ' (c0' : ℤ) hρp').obj Z) = π'.obj Z)
  (hfib' : ∀ X Y : (starTree L').ZVert, π'.obj X = π'.obj Y →
    ∃ n : ℕ, Y = (gZ ρ' hρ' c0' hρp')^[n] X ∨ X = (gZ ρ' hρ' c0' hρp')^[n] Y)

include hπ' hτ' hsurj' hdeck' hfib' in
/-- `not_brick_star_to` with an arbitrary retained base vertex. -/
theorem not_brick_star_to' (c : MeshCoefficients k Q) (Del : Set (StarV L')) (v₀ : StarV L')
    (h0 : v₀ ∉ Del) (hDel : ∀ v, ρ' v ∈ Del ↔ v ∈ Del) (n d : ℕ) (hnd : n * c0' = d) (hd : 0 < d)
    (hNV : ∀ v : (starTree L').Dbl, (v : StarV L') ∉ Del →
      ∃ p : Quiver.Path v ((starTree L').toDbl ((ρ' ^ n) v)), p.length = d ∧
        LinearPaths.path (k := k) p ∉ (((starTree L').preproj k).del Del).ideal _ _) :
    ¬ BrickHypothesis c := by
  classical
  have hDelpow : ∀ (m : ℕ) (v : StarV L'), (ρ' ^ m) v ∈ Del ↔ v ∈ Del := by
    intro m
    induction m with
    | zero => intro v; rfl
    | succ m ih => intro v; rw [pow_succ', Equiv.Perm.mul_apply, hDel, ih]
  set Dset : Set V := {x | ∃ X : (starTree L').ZVert, π'.obj X = x ∧ X.v ∈ Del}
  have hD : ∀ Z : (starTree L').ZVert, π'.obj Z ∈ Dset → (starTree L').toDbl Z.v ∈ Del := by
    rintro Z ⟨X, hX, hXv⟩
    obtain ⟨m, h | h⟩ := hfib' X Z hX
    · rw [h, (gZ_iter ρ' hρ' c0' hρp' m X).1]
      exact (hDelpow m _).2 hXv
    · rw [h, (gZ_iter ρ' hρ' c0' hρp' m Z).1, hDelpow] at hXv
      exact hXv
  let X₀ : (starTree L').ZVert := ⟨v₀, starDepth v₀, by simp [starTree]⟩
  refine (starTree L').not_brick hQ π' c hπ' hτ' Dset Del hD hsurj' (π'.obj X₀)
    (fun h ↦ h0 (hD X₀ h)) fun X hX ↦ ?_
  have hXv : X.v ∉ Del := fun h ↦ hX ⟨X, rfl, h⟩
  obtain ⟨p, hpl, hp⟩ := hNV X.v hXv
  set E := (starTree L').liftEnd X p
  refine ⟨E, (starTree L').liftZ X p, fun h ↦ ?_, ?_, ?_, ?_⟩
  · have := congrArg OrientedTree.ZVert.t h
    simp only [E, OrientedTree.liftEnd] at this
    omega
  · have hE : E = (gZ ρ' hρ' c0' hρp')^[n] X := by
      apply OrientedTree.ZVert.ext
      · rw [(gZ_iter ρ' hρ' c0' hρp' n X).1]; rfl
      · rw [(gZ_iter ρ' hρ' c0' hρp' n X).2]
        simp only [E, OrientedTree.liftEnd, hpl, ← hnd]
        push_cast; ring
    rw [hE]
    exact π_gZ_iter π' ρ' hρ' c0' hρp' hdeck' n X
  · rw [(starTree L').forget_mapPath_liftZ]
    exact hp
  · exact (starTree L').nil_not_mem_del (k := k) Del hXv

end Short

/-! ### The shifted interval -/

section Interval

variable {L : Fin 1 → ℕ} {Ls : Fin 1 → ℕ}

/-- The embedding of a shorter line as an interval, shifting depths by `off`. -/
def intervalV (off : ℕ) (hoff : Ls 0 + off ≤ L 0) (y : StarV Ls) : StarV L :=
  ofDep L (starDepth y + off) (Nat.le_trans (Nat.add_le_add_right (depth_le (L := Ls) y) off)
    (by rw [Nat.add_right_comm]; exact Nat.add_le_add_right hoff 1))

variable (off : ℕ) (hoff : Ls 0 + off ≤ L 0)

theorem depth_intervalV (y : StarV Ls) : starDepth (intervalV off hoff y) = starDepth y + off :=
  starDepth_ofDep _ _

theorem intervalV_injective : Function.Injective (intervalV off hoff) := by
  intro x y h
  have := congrArg starDepth h
  rw [depth_intervalV, depth_intervalV] at this
  exact depth_injective (L := Ls) (by omega)

theorem intervalV_adj (x y : StarV Ls) :
    (starTree L).G.Adj (intervalV off hoff x) (intervalV off hoff y) ↔ (starTree Ls).G.Adj x y := by
  change starAdj _ _ ↔ starAdj _ _
  rw [ReRoot.adj_one, ReRoot.adj_one, depth_intervalV, depth_intervalV]
  omega

theorem intervalV_orient (x y : StarV Ls) :
    (starTree L).orient (intervalV off hoff x) (intervalV off hoff y) ↔ (starTree Ls).orient x y := by
  change starOrient _ _ ↔ starOrient _ _
  unfold starOrient
  rw [ReRoot.adj_one, ReRoot.adj_one, depth_intervalV, depth_intervalV]
  omega

theorem mem_range_intervalV (x : StarV L) :
    x ∈ Set.range (intervalV off hoff) ↔ off ≤ starDepth x ∧ starDepth x ≤ Ls 0 + 1 + off := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [depth_intervalV]
    have := depth_le (L := Ls) y
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨ofDep Ls (starDepth x - off) (by omega), depth_injective (L := L) ?_⟩
    rw [depth_intervalV, starDepth_ofDep]; omega

end Interval

include hπ hτ hsurj hc0 hdeck hfib in
/-- **Odd quotients of `A_{2n}` with period at most `2n − 1` contradict the brick
hypothesis** (any characteristic). -/
theorem a_even_short (h : ℕ) (hh : 1 ≤ h) (hL : L 0 = 2 * h - 2)
    (hrev : ∀ x, starDepth (ρ x) + starDepth x = L 0 + 1) (hodd : Odd c0) (hr : c0 ≤ 2 * h - 1)
    (c : MeshCoefficients k Q) : ¬ BrickHypothesis c := by
  classical
  obtain ⟨q', hq'⟩ := hodd
  set q := q' + 1 with hq
  have hc0q : c0 = 2 * q - 1 := by omega
  have hqh : q ≤ h := by omega
  set Ls : Fin 1 → ℕ := fun _ ↦ 2 * q - 2
  have hoff : Ls 0 + (h - q) ≤ L 0 := by simp only [Ls]; omega
  set f := intervalV (L := L) (Ls := Ls) (h - q) hoff
  have hf := intervalV_injective (h - q) hoff
  have hadj := intervalV_adj (h - q) hoff
  have hor := intervalV_orient (h - q) hoff
  set Del : Set (StarV L) := TreeEmbed.Out (starTree L) (starTree Ls) f hadj
  have hDel_iff : ∀ x : StarV L, x ∈ Del ↔ ¬ (h - q ≤ starDepth x ∧ starDepth x ≤ h + q - 1) := by
    intro x
    have r1 := TreeEmbed.mem_range_iff (starTree L) (starTree Ls) f hadj x
    have r2 := mem_range_intervalV (h - q) hoff x
    simp only [Ls] at r2
    constructor
    · intro hx hb
      exact (r1.1 (r2.2 (by omega))) hx
    · intro hnb
      by_contra hx
      exact hnb (by have := r2.1 (r1.2 hx); omega)
  have hρd : ∀ x, starDepth (ρ x) = 2 * h - 1 - starDepth x := by
    intro x
    have := hrev x
    have := depth_le (L := L) x
    omega
  refine not_brick_star_to' hQ π hπ hτ hsurj ρ hρ c0 hρp hdeck hfib c Del (f none)
    (fun h0 ↦ ?_) (fun v ↦ ?_) 1 c0 (one_mul c0) hc0 (fun v hv ↦ ?_)
  · rw [hDel_iff] at h0
    apply h0
    simp only [f, depth_intervalV]
    simp only [starDepth]; omega
  · rw [hDel_iff, hDel_iff, hρd]
    have := depth_le (L := L) v
    omega
  · have hv' : v ∈ Set.range f := by
      rw [TreeEmbed.mem_range_iff (starTree L) (starTree Ls) f hadj]; exact hv
    obtain ⟨y, rfl⟩ := hv'
    have hyb := depth_le (L := Ls) y
    simp only [Ls] at hyb
    have hy' : 2 * q - 1 - starDepth y ≤ Ls 0 + 1 := by simp only [Ls]; omega
    set y' := ofDep Ls (2 * q - 1 - starDepth y) hy'
    have hy'd : starDepth y' = 2 * q - 1 - starDepth y := starDepth_ofDep _ _
    obtain ⟨p, hpl, hp⟩ := LineTop.end_return (L := Ls) (k := k) y y'
      (by simp only [LineTop.psn, hy'd, Ls]; omega)
    have heq : (starTree L).toDbl ((ρ ^ 1) (f y)) = (TreeEmbed.ιq (starTree L) (starTree Ls) f hadj).obj y' := by
      apply depth_injective (L := L)
      change starDepth ((ρ ^ 1) (f y)) = starDepth (f y')
      rw [pow_one, hρd, depth_intervalV, depth_intervalV, hy'd]
      omega
    rw [heq]
    exact ⟨(TreeEmbed.ιq (starTree L) (starTree Ls) f hadj).mapPath p,
      by rw [LinearPaths.length_mapPath, hpl]; simp only [Ls]; omega,
      TreeEmbed.not_mem_del (starTree L) (starTree Ls) f hf hadj hor p hp⟩

include hπ hτ hsurj hc0 hdeck hfib in
/-- **Odd quotients of even `A` in characteristic two**, under the brick hypothesis: the
derivatives are surjective. -/
theorem a_even_surj (hchar : (2 : k) = 0) (c : MeshCoefficients k Q) (hbrick : BrickHypothesis c)
    (h : ℕ) (hh : 1 ≤ h) (hL : L 0 = 2 * h - 2)
    (hrev : ∀ x, starDepth (ρ x) + starDepth x = L 0 + 1) (m : ℕ) (hm : 2 ≤ m) :
    MeshDerivativeSurjective c m := by
  by_cases hr : 2 * h ≤ c0
  · exact a_even_long hQ π hπ hτ hsurj ρ hρ c0 hc0 hρp hdeck hfib hchar h hh hL hrev hr c m hm
  · exfalso
    have hodd : Odd c0 := by
      have h1 := hρp none
      have h3 := hrev none
      change ((starDepth (ρ none) : ℕ) : ZMod 2) = ((starDepth (none : StarV L) : ℕ) : ZMod 2) + _
        at h1
      have h3' : starDepth (ρ none) = 2 * h - 1 := by
        have h4 : starDepth (none : StarV L) = 0 := rfl
        rw [h4, add_zero, hL] at h3; omega
      rw [h3'] at h1
      simp only [starDepth, Nat.cast_zero, zero_add] at h1
      rcases Nat.even_or_odd c0 with he | ho
      · exfalso
        obtain ⟨r, hr'⟩ := he
        rw [hr'] at h1
        obtain ⟨q, hq⟩ : ∃ q, 2 * h - 1 = 2 * q + 1 := ⟨h - 1, by omega⟩
        rw [hq] at h1; push_cast at h1
        rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_mul, zero_add] at h1
        exact absurd h1 (by decide)
      · exact ho
    exact a_even_short hQ π hπ hτ hsurj ρ hρ c0 hc0 hρp hdeck hfib h hh hL hrev hodd (by omega) c
      hbrick

end StarTrace

end MultiplicativeBasisDeformations
