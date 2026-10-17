import MultiplicativeBasisDeformations.Foundations.ConnectedCase
import MultiplicativeBasisDeformations.Foundations.BrickExclusion
import MultiplicativeBasisDeformations.Foundations.D4Return
import MultiplicativeBasisDeformations.Foundations.E7Return
import MultiplicativeBasisDeformations.Foundations.SubstarRestriction
import MultiplicativeBasisDeformations.Foundations.TraceE6
import MultiplicativeBasisDeformations.Foundations.TraceE78

/-!
# The types `E`: traces and the brick hypothesis

Appendix A, `periodic-mesh-calculations.tex`: the possible
correction classes of `E₆`, `E₇`, `E₈` live in path degrees six, ten and
eighteen; their periods are excluded by deletion to `D₄` (Lemma A.5) or to `E₇`
(Lemma A.7) and the brick hypothesis.

First the exclusion on a periodic star model: if the deck generator `g` fixes the
retained vertices after `n` steps and `n c₀ = d`, closed paths of degree `d`
of `Π` of the retained part lift to closed paths of `Q`, and the brick
hypothesis fails (`not_brick_star`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w

namespace StarTrace

open OrientedTree ScalarMeshCategory StarGauge StarCorner

section General

variable {t : ℕ} {L : Fin t → ℕ}
  {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : (starTree L).ZVert ⥤q V)
  {k : Type u} [Field k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)
  (hπ : π.IsCovering) (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y))
  (hsurj : ∀ x : V, ∃ X, π.obj X = x)
  (ρ : StarV L ≃ StarV L) (hρ : ∀ a b, (starTree L).G.Adj (ρ a) (ρ b) ↔ (starTree L).G.Adj a b)
  (c0 : ℕ) (hρp : ∀ v, (starTree L).par (ρ v) = (starTree L).par v + ((c0 : ℤ) : ZMod 2))
  (hdeck : ∀ Z, π.obj (((starTree L).zAct ρ hρ (c0 : ℤ) hρp).obj Z) = π.obj Z)
  (hfib : ∀ X Y : (starTree L).ZVert, π.obj X = π.obj Y →
    ∃ n : ℕ, Y = (gZ ρ hρ c0 hρp)^[n] X ∨ X = (gZ ρ hρ c0 hρp)^[n] Y)

include hπ hτ hsurj hdeck hfib in
/-- **Exclusion of a period by deletion.** Let `Del` be a `ρ`-stable set of
vertices of the star not containing the centre, let `n c₀ = d > 0`, and let
`ρ^n` fix every retained vertex. If each retained vertex carries a closed path of
degree `d` that is nonzero in `Π` modulo `Del`, the brick hypothesis fails. -/
theorem not_brick_star (Del : Set (StarV L)) (h0 : none ∉ Del) (hDel : ∀ v, ρ v ∈ Del ↔ v ∈ Del)
    (n d : ℕ) (hnd : n * c0 = d) (hd : 0 < d) (hfix : ∀ v, v ∉ Del → (ρ ^ n) v = v)
    (hNV : ∀ v : (starTree L).Dbl, (v : StarV L) ∉ Del → ∃ p : Quiver.Path v v, p.length = d ∧
      LinearPaths.path (k := k) p ∉ (((starTree L).preproj k).del Del).ideal _ _) :
    ¬ BrickHypothesis c := by
  classical
  have hDelpow : ∀ (m : ℕ) (v : StarV L), (ρ ^ m) v ∈ Del ↔ v ∈ Del := by
    intro m
    induction m with
    | zero => intro v; rfl
    | succ m ih => intro v; rw [pow_succ', Equiv.Perm.mul_apply, hDel, ih]
  set Dset : Set V := {x | ∃ X : (starTree L).ZVert, π.obj X = x ∧ X.v ∈ Del}
  have hD : ∀ Z : (starTree L).ZVert, π.obj Z ∈ Dset → (starTree L).toDbl Z.v ∈ Del := by
    rintro Z ⟨X, hX, hXv⟩
    obtain ⟨m, h | h⟩ := hfib X Z hX
    · rw [h, (gZ_iter ρ hρ c0 hρp m X).1]
      exact (hDelpow m _).2 hXv
    · rw [h, (gZ_iter ρ hρ c0 hρp m Z).1, hDelpow] at hXv
      exact hXv
  let X₀ : (starTree L).ZVert := ⟨none, 0, by simp [starTree, starDepth]⟩
  refine (starTree L).not_brick hQ π c hπ hτ Dset Del hD hsurj (π.obj X₀)
    (fun h ↦ h0 (hD X₀ h)) fun X hX ↦ ?_
  have hXv : X.v ∉ Del := fun h ↦ hX ⟨X, rfl, h⟩
  obtain ⟨p, hpl, hp⟩ := hNV X.v hXv
  set E := (starTree L).liftEnd X p
  refine ⟨E, (starTree L).liftZ X p, fun h ↦ ?_, ?_, ?_, ?_⟩
  · have := congrArg OrientedTree.ZVert.t h
    simp only [E, OrientedTree.liftEnd] at this
    omega
  · have hE : E = (gZ ρ hρ c0 hρp)^[n] X := by
      apply OrientedTree.ZVert.ext
      · rw [(gZ_iter ρ hρ c0 hρp n X).1, hfix _ hXv]; rfl
      · rw [(gZ_iter ρ hρ c0 hρp n X).2]
        simp only [E, OrientedTree.liftEnd, hpl, ← hnd]
        push_cast; ring
    rw [hE]
    exact π_gZ_iter π ρ hρ c0 hρp hdeck n X
  · rw [(starTree L).forget_mapPath_liftZ]
    exact hp
  · exact (starTree L).nil_not_mem_del (k := k) Del hXv

end General

section Three

variable {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) {k : Type u} [Field k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (c : MeshCoefficients k Q)
  {L : Fin 3 → ℕ} {π : (starTree L).ZVert ⥤q V}
  (hπ : π.IsCovering) (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y))
  (hsurj : ∀ x : V, ∃ X, π.obj X = x)
  (ρ : StarV L ≃ StarV L) (hρ : ∀ a b, (starTree L).G.Adj (ρ a) (ρ b) ↔ (starTree L).G.Adj a b)
  (c0 : ℕ) (hρp : ∀ v, (starTree L).par (ρ v) = (starTree L).par v + ((c0 : ℤ) : ZMod 2))
  (hdeck : ∀ Z, π.obj (((starTree L).zAct ρ hρ (c0 : ℤ) hρp).obj Z) = π.obj Z)
  (hfib : ∀ X Y : (starTree L).ZVert, π.obj X = π.obj Y →
    ∃ n : ℕ, Y = (gZ ρ hρ c0 hρp)^[n] X ∨ X = (gZ ρ hρ c0 hρp)^[n] Y)
  (h0 : ρ none = none) (θ : Equiv.Perm (Fin 3)) (hL : ∀ i, L (θ i) = L i)
  (hθ : ∀ i j (hj : j ≤ L i), ρ (ch i j hj) = ch (θ i) j (by rw [hL]; exact hj))

include hπ hτ hsurj hdeck hfib h0 hθ in
/-- **Periods dividing two: deletion to `D₄`** (Lemma A.5 and
`periodic-mesh-calculations.tex`). -/
theorem not_brick_D4 (n : ℕ) (hn : n * c0 = 4) (hθn : ∀ i, (θ ^ n) i = i) :
    ¬ BrickHypothesis c := by
  refine not_brick_star hQ π c hπ hτ hsurj ρ hρ c0 hρp hdeck hfib
    {v | 2 ≤ starDepth (L := L) v} (by simp [starDepth])
    (fun v ↦ by simp only [Set.mem_ofPred_eq, depth_ρ ρ hρ h0 θ hL hθ]) n 4 hn (by norm_num)
    (fun v hv ↦ ?_) (fun v hv ↦ ?_)
  · simp only [Set.mem_ofPred_eq, not_le] at hv
    rcases v with _ | ⟨i, ⟨j, hj⟩⟩
    · clear hv hn hθn
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, h0]
    · obtain rfl : j = 0 := by simp [starDepth] at hv; omega
      have := pow_ch' ρ θ hL hθ n i 0 (Nat.zero_le _)
      change (ρ ^ n) (av L i 0 (Nat.zero_le _)) = av L i 0 (Nat.zero_le _)
      rw [this]
      exact ch_congr (hθn i) 0 (by rw [L_pow θ hL]; exact Nat.zero_le _) (Nat.zero_le _)
  · have hv' : ¬ 2 ≤ starDepth (L := L) v := hv
    exact D4Return.d4_return v (by omega)

include hπ hτ hsurj hdeck hfib in
/-- **Periods four and eight of `E₈`: deletion to `E₇`** (Lemma A.7 and
`periodic-mesh-calculations.tex`). -/
theorem not_brick_E7 {a b c' : Fin 3} (hab : a ≠ b) (hac : a ≠ c') (hbc : b ≠ c') (hLa : L a = 0)
    (hLb : L b = 1) (hLc : L c' = 3) (hρid : ∀ v, ρ v = v) (n : ℕ) (hn : n * c0 = 16) :
    ¬ BrickHypothesis c := by
  set L' : Fin 3 → ℕ := Function.update L c' 2
  have hle : ∀ i, L' i ≤ L i := by
    intro i
    by_cases h : i = c'
    · subst h; simp [L', hLc]
    · simp [L', h]
  have hL'a : L' a = 0 := by simp [L', hac, hLa]
  have hL'b : L' b = 1 := by simp [L', hbc, hLb]
  have hL'c : L' c' = 2 := by simp [L']
  refine not_brick_star hQ π c hπ hτ hsurj ρ hρ c0 hρp hdeck hfib (Substar.Out hle)
    (fun h ↦ h none rfl) (fun v ↦ by rw [hρid]) n 16 hn (by norm_num) (fun v _ ↦ ?_) (fun v hv ↦ ?_)
  · have : ρ = 1 := Equiv.ext hρid
    rw [this, one_pow]; rfl
  · simp only [Substar.Out, Set.mem_ofPred_eq, not_forall, not_not] at hv
    obtain ⟨y, rfl⟩ := hv
    obtain ⟨p, hpl, hp⟩ := E7Return.e7_return hab hac hbc hL'a hL'b hL'c (k := k) y
    refine ⟨(Substar.ιq hle).mapPath p, by rw [LinearPaths.length_mapPath, hpl],
      Substar.not_mem_del hle p hp⟩

end Three

/-- The periods allowed by the degrees six, ten and eighteen. -/
theorem period_cases (c0 n N : ℕ) (h : n * c0 = N) (hN : N = 4 ∨ N = 8 ∨ N = 16) (he : Even c0)
    (hpos : 0 < c0) : (∃ n', n' * c0 = 4) ∨ (N ≠ 4 ∧ ∃ n', n' * c0 = 16) := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h'
    · omega
    · exact h'
  have hc : c0 ≤ 16 := by
    have : c0 ≤ n * c0 := Nat.le_mul_of_pos_left c0 hn
    omega
  obtain ⟨r, rfl⟩ := he
  have hr : r ≤ 8 := by omega
  interval_cases r
  · omega
  · left; exact ⟨2, rfl⟩
  · left; exact ⟨1, rfl⟩
  · exfalso; rcases hN with h4 | h4 | h4 <;> subst h4 <;> omega
  · right; exact ⟨by rcases hN with h4 | h4 | h4 <;> subst h4 <;> omega, 2, rfl⟩
  · exfalso; rcases hN with h4 | h4 | h4 <;> subst h4 <;> omega
  · exfalso; rcases hN with h4 | h4 | h4 <;> subst h4 <;> omega
  · exfalso; rcases hN with h4 | h4 | h4 <;> subst h4 <;> omega
  · right; exact ⟨by rcases hN with h4 | h4 | h4 <;> subst h4 <;> omega, 1, rfl⟩

theorem perm_sq_one {a b c' : Fin 3} (hab : a ≠ b) (hac : a ≠ c') (hbc : b ≠ c') (θ : Equiv.Perm (Fin 3))
    (ha : θ a = a) (hb : θ b = c') (hc : θ c' = b) (n : ℕ) :
    (Even n → ∀ i, (θ ^ n) i = i) ∧ (Odd n → θ ^ n = θ) := by
  have hsq : θ ^ 2 = 1 := by
    ext i
    rcases TraceAlg.fin_three_cases hab hac hbc i with rfl | rfl | rfl <;>
      simp [sq, Equiv.Perm.mul_apply, ha, hb, hc]
  constructor
  · rintro ⟨r, rfl⟩ i
    rw [← two_mul, pow_mul, hsq, one_pow]; rfl
  · rintro ⟨r, rfl⟩
    rw [pow_succ, pow_mul, hsq, one_pow, one_mul]

section Main

variable {V : Type v'} [Quiver.{w} V] [Fintype V] [DecidableEq V] [∀ x y : V, Subsingleton (x ⟶ y)]
  [∀ x y : V, Fintype (x ⟶ y)] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] [∀ x y : V, DecidableEq (x ⟶ y)]
  {Q : TranslationQuiver V} (hQ : Q.IsStable) [DecidablePred (· ∈ Q.nonprojective)]
  [Fintype Q.nonprojective]
  {k : Type u} [Field k] (c : MeshCoefficients k Q)

/-- **Mesh corrections vanish for the types `E`** under the brick hypothesis,
when two is invertible (`periodic-mesh-calculations.tex`). -/
theorem e_surjective (hbrick : BrickHypothesis c) (h2 : (2 : k) ≠ 0) (L : Fin 3 → ℕ)
    (π : (starTree L).ZVert ⥤q V) (hπ : π.IsCovering)
    (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y)) (hsurj : ∀ x : V, ∃ X, π.obj X = x)
    (hEL : ∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ L a = 0 ∧ L b = 1 ∧ 1 ≤ L c ∧ L c ≤ 3)
    (m : ℕ) (hm : 2 ≤ m) : MeshDerivativeSurjective c m := by
  obtain ⟨ρ, hρ, c0, hρp, hc0, hρ', hdeck, hfib⟩ :=
    StarDeck.deck_data hQ π hπ hτ (by norm_num) (Or.inr rfl)
  have h0 : ρ none = none := fixes_centre_three rfl ρ hρ'
  obtain ⟨θ, hL, hθ⟩ := arm_perm ρ hρ' h0
  have hθ' : ∀ i j (hj : j ≤ L i), ρ (ch i j hj) = ch (θ i) j (by rw [hL]; exact hj) := by
    intro i j hj
    obtain ⟨_, h⟩ := hθ i j (Nat.lt_succ_iff.2 hj)
    exact h
  have hc0e : Even c0 := by
    have := hρp none
    rw [h0, left_eq_add] at this
    exact (ZMod.natCast_eq_zero_iff_even).1 (by exact_mod_cast this)
  obtain ⟨a, b, c', hab, hac, hbc, hLa, hLb, hLc1, hLc3⟩ := hEL
  have hθa : θ a = a := by
    have := hL a
    rcases TraceAlg.fin_three_cases hab hac hbc (θ a) with h | h | h
    · exact h
    · rw [h, hLb, hLa] at this; omega
    · rw [h, hLa] at this; omega
  have hD4 : ∀ n', n' * c0 = 4 → (∀ i, (θ ^ n') i = i) → False := fun n' hn' hθn ↦
    not_brick_D4 hQ c hπ hτ hsurj ρ hρ c0 hρp hdeck hfib h0 θ hL hθ' n' hn' hθn hbrick
  refine star_surjective_deg hQ π hπ hτ hsurj ρ hρ h0 θ hL hθ' c0 hρp hdeck hfib hc0 ?_ c m hm
  intro M _ _ D n hDn w hw2 hdeg
  have h2' : ∀ x : M, x + x = 0 → x = 0 := TraceAlg.two_cancel h2
  rcases (show L c' = 1 ∨ 2 ≤ L c' by omega) with hc1 | hc23
  · -- `E₆`
    have hθbc : θ b = b ∨ θ b = c' := by
      have := hL b
      rcases TraceAlg.fin_three_cases hab hac hbc (θ b) with h | h | h
      · rw [h, hLa, hLb] at this; omega
      · exact Or.inl h
      · exact Or.inr h
    have hid : (∀ i, D.θ i = i) → D.tr w = 0 := by
      intro hDθ
      have := TraceAlg.trace_E6_id D h2' hab hac hbc hLa hLb hc1 (hDθ a) (hDθ b) (hDθ c') w
        (by omega)
      by_cases h3 : w.length = 3
      · exfalso
        exact hD4 n (by omega) (fun i ↦ by rw [← hDn]; exact hDθ i)
      · exact this.1 h3
    rcases hθbc with hθb | hθb
    · have hθc : θ c' = c' := by
        rcases TraceAlg.fin_three_cases hab hac hbc (θ c') with h | h | h
        · exact absurd (θ.injective (h.trans hθa.symm)) hac.symm
        · exact absurd (θ.injective (h.trans hθb.symm)) hbc.symm
        · exact h
      have hθ1 : θ = 1 := by
        ext i
        rcases TraceAlg.fin_three_cases hab hac hbc i with rfl | rfl | rfl <;> simp [hθa, hθb, hθc]
      exact hid fun i ↦ by rw [hDn, hθ1, one_pow]; rfl
    · have hθc : θ c' = b := by
        rcases TraceAlg.fin_three_cases hab hac hbc (θ c') with h | h | h
        · exact absurd (θ.injective (h.trans hθa.symm)) hac.symm
        · exact h
        · exact absurd (θ.injective (h.trans hθb.symm)) hbc.symm
      obtain ⟨hev, hodd⟩ := perm_sq_one hab hac hbc θ hθa hθb hθc n
      rcases Nat.even_or_odd n with hn | hn
      · exact hid fun i ↦ by rw [hDn]; exact hev hn i
      · have hDθ : D.θ = θ := by rw [hDn, hodd hn]
        exact TraceAlg.trace_E6_swap D h2' hab hac hbc hLa hLb hc1 (by rw [hDθ, hθa])
          (by rw [hDθ, hθb]) (by rw [hDθ, hθc]) w (by omega)
  · -- `E₇`, `E₈`
    have hθb : θ b = b := by
      have := hL b
      rcases TraceAlg.fin_three_cases hab hac hbc (θ b) with h | h | h
      · rw [h, hLa, hLb] at this; omega
      · exact h
      · rw [h, hLb] at this; omega
    have hθc : θ c' = c' := by
      rcases TraceAlg.fin_three_cases hab hac hbc (θ c') with h | h | h
      · exact absurd (θ.injective (h.trans hθa.symm)) hac.symm
      · exact absurd (θ.injective (h.trans hθb.symm)) hbc.symm
      · exact h
    have hθ1 : θ = 1 := by
      ext i
      rcases TraceAlg.fin_three_cases hab hac hbc i with rfl | rfl | rfl <;> simp [hθa, hθb, hθc]
    have hθn : ∀ (n' : ℕ) i, (θ ^ n') i = i := fun n' i ↦ by rw [hθ1, one_pow]; rfl
    have hρid : ∀ v, ρ v = v := by
      rintro (_ | ⟨i, ⟨j, hj⟩⟩)
      · exact h0
      · have := hθ' i j (by omega)
        change ρ (ch i j (by omega)) = ch i j (by omega)
        rw [this]
        exact ch_congr (by rw [hθ1]; rfl) j _ _
    by_contra hne
    have hlen : w.length = 3 ∨ (L c' = 3 ∧ (w.length = 5 ∨ w.length = 9)) := by
      by_contra hl
      push Not at hl
      exact hne (TraceAlg.trace_E78 D h2' hab hac hbc hLa hLb (by omega)
        (fun i ↦ by rw [hDn]; exact hθn n i) w (by omega) hl.1 (fun h ↦ hl.2 h))
    have hN : ∃ N, n * c0 = N ∧ (N = 4 ∨ N = 8 ∨ N = 16) ∧ (N ≠ 4 → L c' = 3) := by
      rcases hlen with h3 | ⟨h3, h5 | h9⟩
      · exact ⟨4, by omega, Or.inl rfl, fun h ↦ absurd rfl h⟩
      · exact ⟨8, by omega, Or.inr (Or.inl rfl), fun _ ↦ h3⟩
      · exact ⟨16, by omega, Or.inr (Or.inr rfl), fun _ ↦ h3⟩
    obtain ⟨N, hnN, hNv, hN3⟩ := hN
    rcases period_cases c0 n N hnN hNv hc0e hc0 with ⟨n', hn'⟩ | ⟨hN4, n', hn'⟩
    · exact hD4 n' hn' (hθn n')
    · exact not_brick_E7 hQ c hπ hτ hsurj ρ hρ c0 hρp hdeck hfib hab hac hbc hLa hLb (hN3 hN4)
        hρid n' hn' hbrick

end Main

end StarTrace

end MultiplicativeBasisDeformations
