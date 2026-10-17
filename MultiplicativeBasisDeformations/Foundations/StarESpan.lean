import MultiplicativeBasisDeformations.Foundations.StarDSpan
import MultiplicativeBasisDeformations.Foundations.TraceEChar2

/-!
# The types `E` in characteristic two (Appendix B)

`characteristic-two-mesh-calculations.tex:330–352`: "Lemma A.2 now bounds the possible
positive correction degrees. Ordinary degree `d` requires `s ∣ (d/2 − 1)`; for
`d = 4, 8, 16, 28` these integers are `1, 3, 7, 13`. … Period one is excluded in every
case by the central `D₄` deletion and Lemma A.5. … For each fixed component, the list
permits at most one degree, `d = 2s + 2`, spanned by a single central row path."

A row of word degree `j` occurs with twist `θ^n` only when `j = 1 + n s`. With `s ≥ 2`,
the candidate degrees `4, 8, 14` (ordinary) and `5` (reflection of `E₆`) force `n = 1`,
so `j = s + 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w u₂

namespace StarTrace

open OrientedTree StarCorner ScalarMeshCategory StarGauge TraceAlg

variable {V : Type v'} [Quiver.{w} V] [Fintype V] [DecidableEq V] [∀ x y : V, Subsingleton (x ⟶ y)]
  [∀ x y : V, Fintype (x ⟶ y)] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] [∀ x y : V, DecidableEq (x ⟶ y)]
  {Q : TranslationQuiver V} (hQ : Q.IsStable) [DecidablePred (· ∈ Q.nonprojective)]
  [Fintype Q.nonprojective]
  {k : Type u} [Field k] (c : MeshCoefficients k Q)

theorem prime_cases (n s j : ℕ) (hs : 2 ≤ s) (hj : j = 1 + n * s)
    (hc : j = 4 ∨ j = 8 ∨ j = 14) : n = 1 ∧ j = s + 1 := by
  rcases hc with rfl | rfl | rfl
  · have : n * s = 3 := by omega
    have hn : n ∣ 3 := ⟨s, this.symm⟩
    rcases (Nat.dvd_prime (by norm_num)).1 hn with rfl | rfl <;> omega
  · have : n * s = 7 := by omega
    have hn : n ∣ 7 := ⟨s, this.symm⟩
    rcases (Nat.dvd_prime (by norm_num)).1 hn with rfl | rfl <;> omega
  · have : n * s = 13 := by omega
    have hn : n ∣ 13 := ⟨s, this.symm⟩
    rcases (Nat.dvd_prime (by norm_num)).1 hn with rfl | rfl <;> omega

/-- **The types `E` in characteristic two**: on a periodic star model of type `E`, the
cokernels are spanned by the row of one word of length `c₀/2 + 1` at the centre, under
the brick hypothesis. -/
theorem e_cokerSpan (hbrick : BrickHypothesis c) (hchar : (2 : k) = 0) (L : Fin 3 → ℕ)
    (π : (starTree L).ZVert ⥤q V) (hπ : π.IsCovering)
    (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y)) (hsurj : ∀ x : V, ∃ X, π.obj X = x)
    (hEL : ∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ L a = 0 ∧ L b = 1 ∧ 1 ≤ L c ∧ L c ≤ 3) :
    ∃ (ρ : StarV L ≃ StarV L) (hρ : ∀ a b, (starTree L).G.Adj (ρ a) (ρ b) ↔ (starTree L).G.Adj a b)
      (c0 : ℕ) (hρp : ∀ v, (starTree L).par (ρ v) = (starTree L).par v + ((c0 : ℤ) : ZMod 2)),
      0 < c0 ∧ ρ none = none ∧
      (∀ Z, π.obj (((starTree L).zAct ρ hρ (c0 : ℤ) hρp).obj Z) = π.obj Z) ∧
      (∀ X Y, π.obj X = π.obj Y → ∃ n : ℕ,
        Y = (StarGauge.gZ ρ hρ c0 hρp)^[n] X ∨ X = (StarGauge.gZ ρ hρ c0 hρp)^[n] Y) ∧
      ∃ W₀ : List (Fin 3), W₀.length = c0 / 2 + 1 ∧ CokerSpan c (candRow hQ π W₀) ∧
        TwoRows.{u₂} Q (candRow hQ π W₀) := by
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
  obtain ⟨s, hs⟩ := hc0e
  have hc0s : c0 = 2 * s := by omega
  have hs2' : c0 / 2 = s := by omega
  obtain ⟨a, b, c', hab, hac, hbc, hLa, hLb, hLc1, hLc3⟩ := hEL
  have hθa : θ a = a := by
    have := hL a
    rcases TraceAlg.fin_three_cases hab hac hbc (θ a) with h | h | h
    · exact h
    · rw [h, hLb, hLa] at this; omega
    · rw [h, hLa] at this; omega
  have hD4 : ∀ n', n' * c0 = 4 → (∀ i, (θ ^ n') i = i) → False := fun n' hn' hθn ↦
    not_brick_D4 hQ c hπ hτ hsurj ρ hρ c0 hρp hdeck hfib h0 θ hL hθ' n' hn' hθn hbrick
  have hθ2 : ∀ i, (θ ^ 2) i = i := by
    intro i
    rw [sq, Equiv.Perm.mul_apply]
    have hθb : θ b = b ∨ θ b = c' := by
      have := hL b
      rcases TraceAlg.fin_three_cases hab hac hbc (θ b) with h | h | h
      · rw [h, hLa, hLb] at this; omega
      · exact Or.inl h
      · exact Or.inr h
    have hθc : θ b = b → θ c' = c' := fun hb ↦ by
      rcases TraceAlg.fin_three_cases hab hac hbc (θ c') with h | h | h
      · exact absurd (θ.injective (h.trans hθa.symm)) hac.symm
      · exact absurd (θ.injective (h.trans hb.symm)) hbc.symm
      · exact h
    have hθc' : θ b = c' → θ c' = b := fun hb ↦ by
      rcases TraceAlg.fin_three_cases hab hac hbc (θ c') with h | h | h
      · exact absurd (θ.injective (h.trans hθa.symm)) hac.symm
      · exact h
      · exact absurd (θ.injective (h.trans hb.symm)) hbc.symm
    rcases TraceAlg.fin_three_cases hab hac hbc i with h | h | h <;> subst i
    · rw [hθa, hθa]
    · rcases hθb with hb | hb
      · rw [hb, hb]
      · rw [hb, hθc' hb]
    · rcases hθb with hb | hb
      · rw [hθc hb, hθc hb]
      · rw [hθc' hb, hb]
  -- period one is excluded
  have hs2 : 2 ≤ s := by
    by_contra h
    have : s = 1 := by omega
    exact hD4 2 (by omega) hθ2
  have h2M : ∀ (M : Type (max u v' w)) [AddCommGroup M] [Module k M] (m : M), m + m = 0 := by
    intro M _ _ m
    rw [← two_smul k m, hchar, zero_smul]
  refine ⟨ρ, hρ, c0, hρp, hc0, h0, hdeck, hfib, ?_⟩
  rcases (show L c' = 1 ∨ 2 ≤ L c' by omega) with hc1 | hc23
  · -- `E₆`
    have hθbc : θ b = b ∨ θ b = c' := by
      have := hL b
      rcases TraceAlg.fin_three_cases hab hac hbc (θ b) with h | h | h
      · rw [h, hLa, hLb] at this; omega
      · exact Or.inl h
      · exact Or.inr h
    -- ordinary traces vanish in the relevant degrees
    have hid : ∀ (M : Type (max u v' w)) [AddCommGroup M] [Module k M] (D : TraceData L M)
        (w : List (Fin 3)), (∀ i, D.θ i = i) → 3 ≤ w.length → D.tr w = 0 := by
      intro M _ _ D w hDθ hw
      obtain ⟨zz, hz⟩ := TraceAlg.trace_E_c2 D (h2M M) hab hac hbc hLa hLb (Or.inl hc1) hDθ w
        (by omega)
      rw [hz]
      split_ifs with hn
      · -- the candidates of degree at least four contain `x³ = 0`
        have hX3 : z L c' ^ 3 = 0 := by have := z_pow L c'; rwa [hc1] at this
        have key : D.tr (candE b c' w.length) = 0 := by
          rw [← D.trc_word (h2M M)]
          rcases hn with h | h | h | h
          · omega
          all_goals rw [h]; simp [candE, pow_succ, mul_assoc, ← mul_assoc (z L c') (z L c'),
            show z L c' * z L c' * z L c' = 0 by rw [← sq, ← pow_succ, hX3]]
        rw [key, smul_zero]
      · rw [smul_zero]
    rcases hθbc with hθb | hθb
    · have hθc : θ c' = c' := by
        rcases TraceAlg.fin_three_cases hab hac hbc (θ c') with h | h | h
        · exact absurd (θ.injective (h.trans hθa.symm)) hac.symm
        · exact absurd (θ.injective (h.trans hθb.symm)) hbc.symm
        · exact h
      have hθ1 : θ = 1 := by
        ext i
        rcases TraceAlg.fin_three_cases hab hac hbc i with rfl | rfl | rfl <;> simp [hθa, hθb, hθc]
      refine ⟨List.replicate (s + 1) a, by rw [List.length_replicate, hs2'], ?_, ?_⟩
      · exact star_span_deg hQ π c hπ hτ hsurj ρ hρ h0 θ hL hθ' c0 hρp hdeck hfib hc0 _
          fun M _ _ D n hDn w hw2 hdeg ↦ ⟨0, by
            rw [zero_smul]
            exact hid M D w (fun i ↦ by rw [hDn, hθ1, one_pow]; rfl) (by
              rcases Nat.eq_zero_or_pos n with rfl | hn
              · omega
              · have : 2 * s ≤ n * c0 := by rw [hc0s]; nlinarith
                omega)⟩
      · exact twoRows_candRow hQ π hπ hτ hsurj ρ hρ h0 θ hL hθ' c0 hρp hdeck hfib hc0 _
          fun M _ D n hDn _ ↦ by
            rw [D.fixed a (by rw [hDn, hθ1, one_pow]; rfl) (s + 1) (by omega), add_zero]
    · have hθc : θ c' = b := by
        rcases TraceAlg.fin_three_cases hab hac hbc (θ c') with h | h | h
        · exact absurd (θ.injective (h.trans hθa.symm)) hac.symm
        · exact h
        · exact absurd (θ.injective (h.trans hθb.symm)) hbc.symm
      have hpo := perm_sq_one hab hac hbc θ hθa hθb hθc
      have hθan : ∀ n : ℕ, (θ ^ n) a = a := fun n ↦ by
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hθa]
      refine ⟨if s = 4 then [c', c', b, c', c'] else List.replicate (s + 1) a, ?_, ?_, ?_⟩
      · split_ifs with h
        · rw [hs2', h]; rfl
        · rw [List.length_replicate, hs2']
      rotate_left
      · refine twoRows_candRow hQ π hπ hτ hsurj ρ hρ h0 θ hL hθ' c0 hρp hdeck hfib hc0 _
          fun M _ D n hDn hd ↦ ?_
        split_ifs at hd ⊢ with h4
        · have hn1 : n = 1 := by
            simp only [List.length_cons, List.length_nil] at hd
            rw [hc0s, h4] at hd
            omega
          subst hn1
          rw [pow_one] at hDn
          exact TraceAlg.trace_E6r_two D hab hac hbc hLa hLb hc1 (by rw [hDn, hθc])
        · rw [D.fixed a (by rw [hDn, hθan]) (s + 1) (by omega), add_zero]
      refine star_span_deg hQ π c hπ hτ hsurj ρ hρ h0 θ hL hθ' c0 hρp hdeck hfib hc0 _
        fun M _ _ D n hDn w hw2 hdeg ↦ ?_
      have hj : w.length = 1 + n * s := by
        have : 2 * w.length = 2 * (1 + n * s) := by rw [hdeg, hc0s]; ring
        omega
      have hn0 : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with rfl | h
        · omega
        · exact h
      have hns : 2 ≤ n * s := le_trans hs2 (Nat.le_mul_of_pos_left s hn0)
      rcases Nat.even_or_odd n with hn | hn
      · refine ⟨0, ?_⟩
        rw [zero_smul]
        have h2n : 2 ≤ n := by obtain ⟨r, hr⟩ := hn; omega
        have : 2 * s ≤ n * s := Nat.mul_le_mul_right s h2n
        exact hid M D w (fun i ↦ by rw [hDn]; exact (hpo n).1 hn i) (by omega)
      · have hDθ : D.θ = θ := by rw [hDn, (hpo n).2 hn]
        have T := TraceAlg.trace_E6_twist_c2 D (h2M M) hab hac hbc hLa hLb hc1
          (by rw [hDθ, hθb]) (by rw [hDθ, hθc]) w
        by_cases h5 : w.length = 5
        · have h4 : n * s = 4 := by omega
          have hs4 : s = 4 := by
            have hn4 : n ∣ 4 := ⟨s, h4.symm⟩
            have : n ≤ 4 := Nat.le_of_dvd (by norm_num) hn4
            obtain ⟨r, rfl⟩ := hn
            have hr : r ≤ 1 := by omega
            interval_cases r <;> omega
          obtain ⟨z, hz⟩ := T.2 h5
          exact ⟨z, by rw [hz, if_pos hs4]⟩
        · exact ⟨0, by rw [zero_smul]; exact T.1 (by omega)⟩
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
    refine ⟨if s + 1 = 4 ∨ s + 1 = 8 ∨ s + 1 = 14 then candE b c' (s + 1)
      else List.replicate (s + 1) a, ?_, ?_, ?_⟩
    · split_ifs with h
      · rw [hs2']; rcases h with h | h | h <;> rw [h] <;> rfl
      · rw [List.length_replicate, hs2']
    rotate_left
    · refine twoRows_candRow hQ π hπ hτ hsurj ρ hρ h0 θ hL hθ' c0 hρp hdeck hfib hc0 _
        fun M _ D n hDn _ ↦ ?_
      have hDθ : ∀ i, D.θ i = i := fun i ↦ by rw [hDn, hθ1, one_pow]; rfl
      have T := TraceAlg.trace_E78_two D hab hac hbc hLa hLb hLc3 hDθ
      split_ifs with h
      · rcases h with h | h | h <;> rw [h]
        · exact T.1
        · exact T.2.1
        · exact T.2.2
      · rw [D.fixed a (hDθ a) (s + 1) (by omega), add_zero]
    refine star_span_deg hQ π c hπ hτ hsurj ρ hρ h0 θ hL hθ' c0 hρp hdeck hfib hc0 _
      fun M _ _ D n hDn w hw2 hdeg ↦ ?_
    have hj : w.length = 1 + n * s := by
      have : 2 * w.length = 2 * (1 + n * s) := by rw [hdeg, hc0s]; ring
      omega
    have hn0 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · omega
      · exact h
    have hns : 2 ≤ n * s := le_trans hs2 (Nat.le_mul_of_pos_left s hn0)
    obtain ⟨z, hz⟩ := TraceAlg.trace_E_c2 D (h2M M) hab hac hbc hLa hLb (Or.inr (by omega))
      (fun i ↦ by rw [hDn, hθ1, one_pow]; rfl) w (by omega)
    rw [hz]
    by_cases hn : w.length = 2 ∨ w.length = 4 ∨ w.length = 8 ∨ w.length = 14
    · rw [if_pos hn]
      have hn' : w.length = 4 ∨ w.length = 8 ∨ w.length = 14 := by omega
      obtain ⟨-, hjs⟩ := prime_cases n s w.length hs2 hj hn'
      have hW : s + 1 = 4 ∨ s + 1 = 8 ∨ s + 1 = 14 := by rw [← hjs]; exact hn'
      rw [if_pos hW, hjs]
      exact ⟨z, rfl⟩
    · rw [if_neg hn]
      exact ⟨0, by rw [smul_zero, zero_smul]⟩

end StarTrace

end MultiplicativeBasisDeformations
