import MultiplicativeBasisDeformations.Foundations.StarTwo
import MultiplicativeBasisDeformations.Foundations.TraceDSpan
import MultiplicativeBasisDeformations.Foundations.DTopPaths
import MultiplicativeBasisDeformations.Foundations.ECase

/-!
# Type `D` in characteristic two (Appendix B)

`characteristic-two-mesh-calculations.tex`. On a periodic star model
of type `D_n` (`N = n − 2`) with period `c₀ = 2s`, a row of path degree `2j` exists
only for `j = 1 + n s` with twist `θ^n` (Lemma A.2(1)), and its class is an integer
multiple of the alternating word `w_j` (`trace_D_span`), which vanishes for `j > N`.
"The brick hypothesis forces `N < 2s`. Otherwise delete the terminal part of the
long arm, retaining `D_{2s+2}`. Its top paths have degree `4s`, fix the tree
vertices, and increase the repetition coordinate by `2s`. They become radical
endomorphisms at every object, for either trivial action or an interchange." Hence
only `j = s + 1` remains: all cokernel classes are multiples of the class of the
row of `w_{s+1}` at the centre.

For the three-cycle of the arms of `D_4`, all classes vanish.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w u₂

namespace TraceAlg

open TraceData

/-- The alternating word of length `n` in the arms `a, b`, starting with `a`. -/
def altL (a b : Fin 3) : ℕ → List (Fin 3)
  | 0 => []
  | n + 1 => a :: altL b a n

theorem length_altL (a b : Fin 3) : ∀ n, (altL a b n).length = n
  | 0 => rfl
  | n + 1 => by rw [altL, List.length_cons, length_altL b a n]

theorem altE_succ_left {S : Type*} [Ring S] (p q : S) (n : ℕ) :
    p * altE q p n = altE p q (n + 1) := by
  rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨r, hr⟩
  · rw [show n = 2 * r by omega, altE_even, show 2 * r + 1 = 2 * r + 1 from rfl, altE_odd]
    exact q_mul_pq_pow q p r
  · rw [show n = 2 * r + 1 by omega, altE_odd, show 2 * r + 1 + 1 = 2 * (r + 1) by ring, altE_even,
      ← mul_assoc, q_mul_pq_pow q p r, mul_assoc, ← pow_succ]

theorem prod_altL {L : Fin 3 → ℕ} : ∀ (n : ℕ) (a b : Fin 3),
    ((altL a b n).map (x L)).prod = altE (x L a) (x L b) n
  | 0, a, b => by simp [altL, altE]
  | n + 1, a, b => by
      rw [altL, List.map_cons, List.prod_cons, prod_altL n b a, altE_succ_left]

theorem perm_three_fpf (θ : Equiv.Perm (Fin 3)) (hθ : ∀ i, θ i ≠ i) (n : ℕ) :
    (θ ^ n = 1 ∧ 3 ∣ n) ∨ ∀ i, (θ ^ n) i ≠ i := by
  have h3 : θ ^ 3 = 1 := by revert θ; decide
  have h1 : ∀ i, (θ ^ 1) i ≠ i := by simpa using hθ
  have h2 : ∀ i, (θ ^ 2) i ≠ i := by revert θ; decide
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ n = 3 * q + r := ⟨n / 3, n % 3, Nat.mod_lt _ (by norm_num),
    (Nat.div_add_mod n 3).symm⟩
  rw [pow_add, pow_mul, h3, one_pow, one_mul]
  interval_cases r
  · left; exact ⟨pow_zero θ, ⟨q, by ring⟩⟩
  · right; exact h1
  · right; exact h2

variable {M : Type*} [AddCommGroup M]

/-- **The spanning hypothesis for type `D`**: every trace of a word of length
`j = 1 + n s` with twist `θ^n` is a multiple of the trace of `w_{s+1}`, when either
`θ` fixes the long arm and `N < 2s`, or `θ` is a three-cycle. -/
theorem trace_D_hspan {L : Fin 3 → ℕ} {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hLa : L a = 0) (hLb : L b = 0) (θ : Equiv.Perm (Fin 3)) (hθL : ∀ i, L (θ i) = L i)
    (s : ℕ) (hcase : (θ c = c ∧ L c + 2 < 2 * s) ∨ (∀ i, θ i ≠ i))
    (D : TraceData L M) (n : ℕ) (hn : D.θ = θ ^ n) (w : List (Fin 3)) (hw : 2 ≤ w.length)
    (hd : 2 * w.length = 2 + n * (2 * s)) :
    ∃ z : ℤ, D.tr w = z • D.tr (altL a b (s + 1)) := by
  have hne : w ≠ [] := by rintro rfl; simp at hw
  have hj : w.length = 1 + n * s := by
    have : 2 * w.length = 2 * (1 + n * s) := by rw [hd]; ring
    omega
  -- the alternating word of length `s + 1`
  have hW : D.tr (altL a b (s + 1)) = D.trR (altE (x L a) (x L b) (s + 1)) := by
    rw [← prod_altL, D.trR_word]
  have hs1 : 1 ≤ n * s := by omega
  -- with a twist preserving `{a, b}` and fixing `c`
  have main : D.θ c = c → (w.length ≠ s + 1 → altE (x L a) (x L b) w.length = 0) →
      ∃ z : ℤ, D.tr w = z • D.tr (altL a b (s + 1)) := by
    intro hθc hbig
    have hθab : (D.θ a = a ∧ D.θ b = b) ∨ (D.θ a = b ∧ D.θ b = a) := by
      have ha : D.θ a ≠ c := fun h ↦ hac (D.θ.injective (h.trans hθc.symm))
      have hb : D.θ b ≠ c := fun h ↦ hbc (D.θ.injective (h.trans hθc.symm))
      rcases fin_three_cases hab hac hbc (D.θ a) with h1 | h1 | h1
      · left; refine ⟨h1, ?_⟩
        rcases fin_three_cases hab hac hbc (D.θ b) with h3 | h3 | h3
        · exact absurd (D.θ.injective (h3.trans h1.symm)) (Ne.symm hab)
        · exact h3
        · exact absurd h3 hb
      · right; refine ⟨h1, ?_⟩
        rcases fin_three_cases hab hac hbc (D.θ b) with h3 | h3 | h3
        · exact h3
        · exact absurd (D.θ.injective (h3.trans h1.symm)) (Ne.symm hab)
        · exact absurd h3 hb
      · exact absurd h1 ha
    obtain ⟨z, hz⟩ := trace_D_span D hab hac hbc hLa hLb hθab hne
    by_cases hjs : w.length = s + 1
    · exact ⟨z, by rw [hz, hjs, hW]⟩
    · exact ⟨0, by rw [zero_smul, hz, hbig hjs, map_zero, smul_zero]⟩
  have powfix : ∀ m : ℕ, θ c = c → (θ ^ m) c = c := by
    intro m h
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, h]
  rcases hcase with ⟨hθc, hN⟩ | hfpf
  · refine main (by rw [hn]; exact powfix n hθc) fun hjs ↦ ?_
    apply altE_zero hab hac hbc hLa hLb
    have hn2 : 2 ≤ n := by
      by_contra h
      interval_cases n <;> omega
    have : 2 * s ≤ n * s := Nat.mul_le_mul_right s hn2
    omega
  · rcases perm_three_fpf θ hfpf n with ⟨hid, ⟨q, rfl⟩⟩ | hfp
    · -- the twist is trivial and `n ≥ 3`
      have hLc : L c = 0 := by
        have h1 := hθL c
        rcases fin_three_cases hab hac hbc (θ c) with h | h | h
        · rw [h, hLa] at h1; exact h1.symm
        · rw [h, hLb] at h1; exact h1.symm
        · exact absurd h (hfpf c)
      refine main (by rw [hn, hid]; rfl) fun _ ↦ ?_
      apply altE_zero hab hac hbc hLa hLb
      have hq : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with rfl | h
        · simp at hs1
        · exact h
      have hs : 1 ≤ s := by
        rcases Nat.eq_zero_or_pos s with h | h
        · simp [h] at hs1
        · exact h
      have : 3 * s ≤ (3 * q) * s := Nat.mul_le_mul_right s (by omega)
      omega
    · refine ⟨0, ?_⟩
      rw [zero_smul]
      have hall : ∀ i, L i = 0 := by
        intro i
        rcases fin_three_cases hab hac hbc i with rfl | rfl | rfl
        · exact hLa
        · exact hLb
        · have h1 := hθL i
          rcases fin_three_cases hab hac hbc (θ i) with h | h | h
          · rw [h, hLa] at h1; exact h1.symm
          · rw [h, hLb] at h1; exact h1.symm
          · exact absurd h (hfpf i)
      exact trace_D4_cycle hall D (fun i ↦ by rw [hn]; exact hfp i) hw

end TraceAlg

namespace Substar

variable {t : ℕ} {L L' : Fin t → ℕ} (hle : ∀ i, L' i ≤ L i)

theorem mem_Out_iff (x : StarV L) :
    x ∈ Out hle ↔ ∃ (i : Fin t) (j : Fin (L i + 1)), x = some ⟨i, j⟩ ∧ L' i < j := by
  rw [← not_iff_not, ← mem_range_iff]
  constructor
  · rintro ⟨y, rfl⟩ ⟨i, j, h, hlt⟩
    rcases y with _ | ⟨i', j'⟩
    · simp [ιv] at h
    · simp only [ιv, Option.map_some, Option.some.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h⟩ := h
      have := congrArg Fin.val (eq_of_heq h)
      simp only [Fin.coe_castLE] at this
      have := j'.2
      omega
  · intro h
    rcases x with _ | ⟨i, j⟩
    · exact ⟨none, rfl⟩
    · have hj : (j : ℕ) ≤ L' i := by
        by_contra hc
        exact h ⟨i, j, rfl, by omega⟩
      exact ⟨some ⟨i, ⟨j, by omega⟩⟩, rfl⟩

end Substar

namespace StarTrace

open OrientedTree StarCorner ScalarMeshCategory StarGauge TraceAlg

variable {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) {k : Type u} [Field k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]
  [Fintype Q.nonprojective]
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
/-- **The brick hypothesis bounds the long arm of type `D`**: if `θ` fixes the long arm
`c` and `c₀ ≤ N = L c + 2`, the brick hypothesis fails (deletion to `D_{c₀ + 2}` and
Lemma B.1). -/
theorem not_brick_D_long {a b c' : Fin 3} (hab : a ≠ b) (hac : a ≠ c') (hbc : b ≠ c')
    (hLa : L a = 0) (hLb : L b = 0) (hθc : θ c' = c') (hc0e : Even c0) (hc0 : 0 < c0)
    (hN : c0 ≤ L c' + 2) : ¬ BrickHypothesis c := by
  classical
  set L' : Fin 3 → ℕ := Function.update L c' (c0 - 2)
  have hle : ∀ i, L' i ≤ L i := by
    intro i
    by_cases h : i = c'
    · subst h; simp only [L', Function.update_self]; omega
    · simp [L', h]
  have hL'a : L' a = 0 := by simp [L', hac, hLa]
  have hL'b : L' b = 0 := by simp [L', hbc, hLb]
  have hL'c : L' c' = c0 - 2 := by simp [L']
  have hθab : ∀ i, i ≠ c' → θ i ≠ c' := fun i hi h ↦ hi (θ.injective (h.trans hθc.symm))
  have hL'θ : ∀ i, L' (θ i) = L' i := by
    intro i
    by_cases h : i = c'
    · subst h; rw [hθc]
    · simp only [L', Function.update_of_ne (hθab i h), Function.update_of_ne h, hL]
  have hθ2 : ∀ i, (θ ^ 2) i = i := by
    intro i
    rw [sq, Equiv.Perm.mul_apply]
    by_cases h : i = c'
    · subst h; rw [hθc, hθc]
    · have h1 := hθab i h
      rcases fin_three_cases hab hac hbc i with h' | h' | h' <;> subst i
      · rcases fin_three_cases hab hac hbc (θ a) with h2 | h2 | h2
        · rw [h2, h2]
        · have h3 : θ b ≠ c' := hθab b (Ne.symm (Ne.symm hbc))
          rcases fin_three_cases hab hac hbc (θ b) with h4 | h4 | h4
          · rw [h2, h4]
          · exact absurd (θ.injective (h4.trans h2.symm)) (Ne.symm hab)
          · exact absurd h4 h3
        · exact absurd h2 h1
      · rcases fin_three_cases hab hac hbc (θ b) with h2 | h2 | h2
        · have h3 : θ a ≠ c' := hθab a hac
          rcases fin_three_cases hab hac hbc (θ a) with h4 | h4 | h4
          · exact absurd (θ.injective (h4.trans h2.symm)) hab
          · rw [h2, h4]
          · exact absurd h4 h3
        · rw [h2, h2]
        · exact absurd h2 h1
      · exact absurd rfl h
  have hρ2 : ∀ v, (ρ ^ 2) v = v := by
    rintro (_ | ⟨i, ⟨j, hj⟩⟩)
    · rw [sq, Equiv.Perm.mul_apply, h0, h0]
    · have := pow_ch' ρ θ hL hθ 2 i j (by omega)
      change (ρ ^ 2) (av L i j (by omega)) = av L i j (by omega)
      rw [this]
      exact av_congr (hθ2 i) j _ _
  refine not_brick_star hQ π c hπ hτ hsurj ρ hρ c0 hρp hdeck hfib (Substar.Out hle)
    (fun h ↦ h none rfl) (fun v ↦ ?_) 2 (2 * c0) (by ring) (by omega) (fun v _ ↦ hρ2 v)
    (fun v hv ↦ ?_)
  · -- the deleted set is stable under `ρ`
    rw [Substar.mem_Out_iff, Substar.mem_Out_iff]
    rcases v with _ | ⟨i, ⟨j, hj⟩⟩
    · rw [h0]
    · have hρi : ρ (some ⟨i, ⟨j, hj⟩⟩) = some ⟨θ i, ⟨j, by rw [hL]; exact hj⟩⟩ :=
        hθ i j (by omega)
      rw [hρi]
      constructor
      · rintro ⟨i', j', he, hlt⟩
        simp only [Option.some.injEq, Sigma.mk.inj_iff] at he
        obtain ⟨h1, he⟩ := he
        subst h1
        have hval : (j' : ℕ) = j := by rw [← eq_of_heq he]
        refine ⟨i, ⟨j, hj⟩, rfl, ?_⟩
        show L' i < j
        rw [← hL'θ i]; omega
      · rintro ⟨i', j', he, hlt⟩
        simp only [Option.some.injEq, Sigma.mk.inj_iff] at he
        obtain ⟨h1, he⟩ := he
        subst h1
        have hval : (j' : ℕ) = j := by rw [← eq_of_heq he]
        refine ⟨θ i, ⟨j, by rw [hL]; exact hj⟩, rfl, ?_⟩
        show L' (θ i) < j
        rw [hL'θ]; omega
  · simp only [Substar.Out, Set.mem_ofPred_eq, not_forall, not_not] at hv
    obtain ⟨y, rfl⟩ := hv
    have hev : Even (L' c') := by rw [hL'c]; obtain ⟨e, he⟩ := hc0e; exact ⟨e - 1, by omega⟩
    obtain ⟨p, hpl, hp⟩ := DTop.d_return hab hac hbc hL'a hL'b hev (k := k) y
    have hc02 : 2 ≤ c0 := by obtain ⟨e, he⟩ := hc0e; omega
    refine ⟨(Substar.ιq hle).mapPath p, by rw [LinearPaths.length_mapPath, hpl, hL'c]; omega,
      Substar.not_mem_del hle p hp⟩

omit [∀ x y : V, Subsingleton (x ⟶ y)] in
include hπ hτ hsurj hdeck hfib in
/-- **Type `D` in characteristic two**: on a periodic star model of type `D` whose deck
generator fixes the centre, the cokernels are spanned by the row of one word of
length `c₀/2 + 1` at the centre, under the brick hypothesis. -/
theorem d_cokerSpan [∀ x y : V, Subsingleton (x ⟶ y)] (hbrick : BrickHypothesis c)
    (hρ' : ∀ a b, starAdj a b ↔ starAdj (ρ a) (ρ b)) (h0 : ρ none = none) (hc0 : 0 < c0)
    {a b c' : Fin 3} (hab : a ≠ b) (hac : a ≠ c') (hbc : b ≠ c') (hLa : L a = 0)
    (hLb : L b = 0) :
    ∃ W₀ : List (Fin 3), W₀.length = c0 / 2 + 1 ∧ CokerSpan c (candRow hQ π W₀) ∧
      TwoRows.{u₂} Q (candRow hQ π W₀) := by
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
  have hs2 : c0 / 2 = s := by omega
  -- the spanning statement for a triple of arms
  have key : ∀ a b c'' : Fin 3, a ≠ b → a ≠ c'' → b ≠ c'' → L a = 0 → L b = 0 →
      ((θ c'' = c'' ∧ L c'' + 2 < 2 * s) ∨ (∀ i, θ i ≠ i)) →
      ∃ W₀ : List (Fin 3), W₀.length = c0 / 2 + 1 ∧ CokerSpan c (candRow hQ π W₀) ∧
        TwoRows.{u₂} Q (candRow hQ π W₀) := by
    intro a b c'' hab hac hbc hLa hLb hcase
    refine ⟨altL a b (s + 1), by rw [length_altL, hs2], ?_, ?_⟩
    · exact star_span_deg hQ π c hπ hτ hsurj ρ hρ h0 θ hL hθ' c0 hρp hdeck hfib hc0 _
        fun M _ _ D n hn w hw hd ↦ trace_D_hspan hab hac hbc hLa hLb θ hL s hcase D n hn w hw
          (by rw [hd, hc0s])
    · exact twoRows_candRow hQ π hπ hτ hsurj ρ hρ h0 θ hL hθ' c0 hρp hdeck hfib hc0 _
        fun M _ D n _ _ ↦ TraceAlg.trace_D_any_two D hab hac hbc hLa hLb
          (by rw [length_altL]; omega)
  by_cases hfix : θ c' = c'
  · by_cases hN : L c' + 2 < 2 * s
    · exact key a b c' hab hac hbc hLa hLb (Or.inl ⟨hfix, hN⟩)
    · exact absurd hbrick (not_brick_D_long hQ c hπ hτ hsurj ρ hρ c0 hρp hdeck hfib h0 θ hL hθ'
        hab hac hbc hLa hLb hfix ⟨s, hs⟩ hc0 (by omega))
  · -- `θ` moves the arm `c'`: all arms have one vertex (`D₄`)
    have hLc : L c' = 0 := by
      have h1 := hL c'
      rcases fin_three_cases hab hac hbc (θ c') with h | h | h
      · rw [h, hLa] at h1; exact h1.symm
      · rw [h, hLb] at h1; exact h1.symm
      · exact absurd h hfix
    have hall : ∀ i, L i = 0 := fun i ↦ by
      rcases fin_three_cases hab hac hbc i with h | h | h <;> subst i <;> assumption
    by_cases hfp : ∃ e, θ e = e
    · obtain ⟨e, he⟩ := hfp
      obtain ⟨a', b', ha'b', ha'e, hb'e⟩ : ∃ a' b' : Fin 3, a' ≠ b' ∧ a' ≠ e ∧ b' ≠ e := by
        fin_cases e
        · exact ⟨1, 2, by decide, by decide, by decide⟩
        · exact ⟨0, 2, by decide, by decide, by decide⟩
        · exact ⟨0, 1, by decide, by decide, by decide⟩
      by_cases hN : L e + 2 < 2 * s
      · exact key a' b' e ha'b' ha'e hb'e (hall a') (hall b') (Or.inl ⟨he, hN⟩)
      · exact absurd hbrick (not_brick_D_long hQ c hπ hτ hsurj ρ hρ c0 hρp hdeck hfib h0 θ hL hθ'
          ha'b' ha'e hb'e (hall a') (hall b') he ⟨s, hs⟩ hc0 (by omega))
    · push Not at hfp
      exact key a b c' hab hac hbc hLa hLb (Or.inr hfp)

end StarTrace

end MultiplicativeBasisDeformations
