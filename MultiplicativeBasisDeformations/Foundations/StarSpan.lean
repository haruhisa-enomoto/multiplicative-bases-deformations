import MultiplicativeBasisDeformations.Foundations.StarCase
import MultiplicativeBasisDeformations.Foundations.RowSpan

/-!
# Cokernels on a periodic star model spanned by one row (Appendix B)

`characteristic-two-mesh-calculations.tex:13–20`: "We will show that each periodic
component contributes at most one correction line, represented by a single path."
On a periodic star model, the twisted-trace surjection of Lemma A.2 (`rowClass_mem_span`)
sends words at the centre onto the row classes. If every twisted trace of a word in
an allowed degree is an integer multiple of the trace of one word `W₀`, then all
cokernel classes are multiples of the class of the row given by `W₀` at the centre
(`star_span_deg`). This is the analogue of `star_surjective_deg` with a spanning
word instead of vanishing traces.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w

namespace StarTrace

open OrientedTree StarCorner ScalarMeshCategory StarGauge

variable {t : ℕ} {L : Fin t → ℕ}
  {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : (starTree L).ZVert ⥤q V)
  {k : Type u} [CommRing k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]
  [Fintype Q.nonprojective]

/-- The centre of the star at height zero. -/
def X₀ : (starTree L).ZVert := ⟨o L, 0, par_o⟩

/-- The lift of the word `W` at the centre, from `τ X₀`. -/
abbrev liftW (W : List (Fin t)) := (starTree L).liftZ ((starTree L).ztau (X₀ (L := L))) (wordP W)

/-- **The candidate row** of a word: the image of its lift, when it is a row. -/
def candRow (W : List (Fin t)) : RowSet Q :=
  {R | ∃ e : π.obj ((starTree L).ztau X₀) =
      hQ.tauE (π.obj ((starTree L).liftEnd ((starTree L).ztau X₀) (wordP W))),
    R = ⟨⟨_, hQ.mem_nonprojective _⟩, (π.mapPath (liftW W)).cast e rfl⟩}

theorem candRow_subsingleton (W : List (Fin t)) : (candRow hQ π W).Subsingleton := by
  rintro R ⟨e, rfl⟩ R' ⟨e', rfl⟩
  rfl

theorem candRow_length (W : List (Fin t)) : ∀ R ∈ candRow hQ π W, R.2.length = 2 * W.length := by
  rintro R ⟨e, rfl⟩
  simp only
  rw [length_cast, LinearPaths.length_mapPath, length_liftZ, length_wordP]

theorem rowZ_liftW_mem (c : MeshCoefficients k Q) (m : ℕ) (W : List (Fin t))
    (hW : 2 * W.length = m + 1) :
    (starTree L).rowZ hQ π c m (liftW W) ∈ rowSpan c m (candRow hQ π W) := by
  unfold OrientedTree.rowZ rowQ
  split_ifs with e
  · refine Submodule.subset_span ⟨_, ⟨⟨e, rfl⟩, ?_⟩, rfl⟩
    simp only
    rw [length_cast, LinearPaths.length_mapPath, length_liftZ, length_wordP, hW]
  · exact zero_mem _

theorem liftZ_cast_pathStar (Y : (starTree L).ZVert) {b b' : (starTree L).Dbl}
    (p : Quiver.Path ((starTree L).toDbl Y.v) b) (e : b = b') :
    (⟨_, (starTree L).liftZ Y (p.cast rfl e)⟩ : Quiver.PathStar Y) = ⟨_, (starTree L).liftZ Y p⟩ := by
  subst e; rfl

variable (c : MeshCoefficients k Q) (σ : StarV L ≃ StarV L)
  (hσ : ∀ a b, (starTree L).G.Adj (σ a) (σ b) ↔ (starTree L).G.Adj a b) (m : ℕ)
  (hσo : σ none = none)

theorem wordTr_mem (W : List (Fin t)) :
    wordTr hQ π c σ hσ m hσo W ∈ rowSpan c m (candRow hQ π W) := by
  unfold wordTr
  split_ifs with hW
  · unfold phiV OrientedTree.phiD
    rw [(starTree L).rowZ_eq_of_pathStar hQ π c (liftZ_cast_pathStar _ _ _)]
    exact rowZ_liftW_mem hQ π c m W hW
  · exact zero_mem _

variable (hπ : π.IsCovering) (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y))
  (hsurj : ∀ x : V, ∃ X, π.obj X = x)
  (ρ : StarV L ≃ StarV L) (hρ : ∀ a b, (starTree L).G.Adj (ρ a) (ρ b) ↔ (starTree L).G.Adj a b)
  (h0 : ρ none = none) (θ : Equiv.Perm (Fin t)) (hL : ∀ i, L (θ i) = L i)
  (hθ : ∀ i j (hj : j ≤ L i), ρ (ch i j hj) = ch (θ i) j (by rw [hL]; exact hj))
  (c0 : ℕ) (hρp : ∀ v, (starTree L).par (ρ v) = (starTree L).par v + ((c0 : ℤ) : ZMod 2))
  (hdeck : ∀ Z, π.obj (((starTree L).zAct ρ hρ (c0 : ℤ) hρp).obj Z) = π.obj Z)
  (hfib : ∀ X Y : (starTree L).ZVert, π.obj X = π.obj Y →
    ∃ n : ℕ, Y = (gZ ρ hρ c0 hρp)^[n] X ∨ X = (gZ ρ hρ c0 hρp)^[n] Y)

include hπ hτ hsurj hρ h0 hθ hdeck hfib in
/-- **On a periodic star model, the cokernels are spanned by the row of one word**,
when every twisted trace of a word in an allowed degree is a multiple of the trace
of that word. -/
theorem star_span_deg (hc0 : 0 < c0) (W₀ : List (Fin t))
    (hspan : ∀ (M : Type (max u v' w)) [AddCommGroup M] [Module k M]
      (D : TraceAlg.TraceData L M) (n : ℕ), D.θ = θ ^ n →
        ∀ w : List (Fin t), 2 ≤ w.length → 2 * w.length = 2 + n * c0 →
          ∃ z : ℤ, D.tr w = z • D.tr W₀) :
    CokerSpan c (candRow hQ π W₀) := by
  have hc0e : Even c0 := by
    have := hρp none
    rw [h0, left_eq_add] at this
    exact (ZMod.natCast_eq_zero_iff_even).1 (by exact_mod_cast this)
  obtain ⟨μ, η, hsig⟩ := exists_signed_gauge hQ π c ρ hρ c0 hρp hdeck θ hL h0 hθ hπ hsurj hfib hτ
    hc0 hc0e
  set c' : MeshCoefficients k Q := fun x y a ↦ η x * c x y a * μ (Q.mate x y a) * μ a
  have hgauge : ∀ (x : Q.nonprojective) (y : V) (a : y ⟶ x.1),
      c x y a = (η x)⁻¹ * c' x y a * (μ (Q.mate x y a))⁻¹ * (μ a)⁻¹ :=
    gauge_symm (fun a ↦ μ a) η c c' (fun _ _ _ ↦ rfl)
  refine cokerSpan_gauge c' (fun a ↦ (μ a)⁻¹) (fun x ↦ (η x)⁻¹) c hgauge ?_
  have hc' : OppositeOnMates c' hQ :=
    (starTree L).oppositeOnMates_of_signed hQ π c' hπ hτ hsurj hsig
  intro m hm x p hp
  -- lift the row to find the deck transformation of its degree
  obtain ⟨X, hX⟩ := hsurj x.1
  have e1 : π.obj ((starTree L).ztau X) = (Q.tau x).1 := by rw [hτ, hX]; rfl
  obtain ⟨E, hE, P, hP⟩ := RelSystem.exists_lift π hπ ((starTree L).ztau X) (p.cast e1.symm rfl)
  have hPlen : P.length = m + 1 := by
    rw [← LinearPaths.length_mapPath π P, hP, length_cast, length_cast, hp]
  have hEt : E.t = X.t + (m - 1 : ℤ) := by
    have := (starTree L).t_path P
    rw [hPlen] at this; simp only [ztau] at this; push_cast at this; omega
  have hgt : ∀ (n : ℕ) (Z : (starTree L).ZVert), ((gZ ρ hρ c0 hρp)^[n] Z).t = Z.t + n * c0 :=
    fun n Z ↦ (gZ_iter ρ hρ c0 hρp n Z).2
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) * c0 = m - 1 := by
    obtain ⟨n, hn | hn⟩ := hfib X E (hE.trans hX.symm).symm
    · exact ⟨n, by have := hgt n X; rw [← hn] at this; omega⟩
    · exfalso
      have := hgt n E; rw [← hn] at this
      have : (0 : ℤ) ≤ n * c0 := by positivity
      omega
  set s : ℤ := n * c0
  have hσ' := adj_pow ρ hρ n
  have hd : ∀ v, starDepth ((ρ ^ n) v) = starDepth v :=
    depth_pow ρ (depth_ρ ρ hρ h0 θ hL hθ) n
  have hseven : ((s : ℤ) : ZMod 2) = 0 := by
    obtain ⟨r, hr⟩ := hc0e
    simp only [s, hr]; push_cast; rw [← two_mul, show (2 : ZMod 2) = 0 from rfl]; ring
  have hσp' : ∀ v, (starTree L).par ((ρ ^ n) v) = (starTree L).par v + s := by
    intro v; rw [hseven, add_zero]; change ((starDepth _ : ℕ) : ZMod 2) = _; rw [hd]; rfl
  have hiter : ∀ Z, ((starTree L).zAct (ρ ^ n) hσ' s hσp').obj Z = (gZ ρ hρ c0 hρp)^[n] Z := by
    intro Z
    apply OrientedTree.ZVert.ext
    · exact (gZ_iter ρ hρ c0 hρp n Z).1.symm
    · exact (hgt n Z).symm
  have hdeck' : ∀ Z, π.obj (((starTree L).zAct (ρ ^ n) hσ' s hσp').obj Z) = π.obj Z := by
    intro Z; rw [hiter]; exact π_gZ_iter π ρ hρ c0 hρp hdeck n Z
  have hfib' : ∀ X' E' : (starTree L).ZVert, π.obj E' = π.obj X' → E'.t = X'.t + s →
      E' = ((starTree L).zAct (ρ ^ n) hσ' s hσp').obj X' := by
    intro X' E' h1 h2
    rw [hiter]
    obtain ⟨n', hn' | hn'⟩ := hfib X' E' h1.symm
    · have := hgt n' X'
      rw [← hn', h2] at this
      have : n' = n := by
        have h3 : (n' : ℤ) * c0 = n * c0 := by omega
        exact_mod_cast mul_right_cancel₀ (by positivity) h3
      subst this; exact hn'
    · have := hgt n' E'
      rw [← hn', h2] at this
      have h4 : (0 : ℤ) ≤ n * c0 := by positivity
      have h5 : (0 : ℤ) ≤ n' * c0 := by positivity
      have hn0 : n = 0 := by
        by_contra hne
        have : (0 : ℤ) < n * c0 := by positivity
        omega
      subst hn0
      have hn'0 : n' = 0 := by
        by_contra hne
        have : (0 : ℤ) < n' * c0 := by positivity
        omega
      subst hn'0
      exact hn'.symm
  have hs' : (m : ℤ) + 1 = 2 + s := by simp only [s]; omega
  have hσo' : (ρ ^ n) none = none := by
    clear_value s
    clear hσ' hσp' hiter hdeck' hfib' hs' hseven hd hn
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, h0]
  have hL' : ∀ i, L ((θ ^ n) i) = L i := L_pow θ hL n
  have hθ' := pow_ch' ρ θ hL hθ n
  have hmem := rowClass_mem_span hQ π c' (ρ ^ n) hσ' m s hσp' hπ hτ hsig hc' hdeck' hs' hσo'
    (θ ^ n) hL' hθ' hsurj hfib' x p hp
  refine Submodule.span_le.2 ?_ hmem
  rintro _ ⟨w', rfl⟩
  by_cases hd' : 2 * w'.length = m + 1
  · obtain ⟨z, hz⟩ := hspan _ (traceData hQ π c' (ρ ^ n) hσ' m s hσp' hπ hτ hsig hc' hdeck' hs'
      hσo' (θ ^ n) hL' hθ') n rfl w' (by omega) (by simp only [s] at hs'; omega)
    change wordTr hQ π c' (ρ ^ n) hσ' m hσo' w' ∈ _
    change wordTr hQ π c' (ρ ^ n) hσ' m hσo' w' =
      z • wordTr hQ π c' (ρ ^ n) hσ' m hσo' W₀ at hz
    rw [hz]
    exact Submodule.smul_of_tower_mem _ z (wordTr_mem hQ π c' (ρ ^ n) hσ' m hσo' W₀)
  · change wordTr hQ π c' (ρ ^ n) hσ' m hσo' w' ∈ _
    unfold wordTr
    rw [if_neg hd']
    exact zero_mem _

end StarTrace

end MultiplicativeBasisDeformations
