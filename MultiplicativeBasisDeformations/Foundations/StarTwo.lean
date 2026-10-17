import MultiplicativeBasisDeformations.Foundations.StarSpan
import MultiplicativeBasisDeformations.Foundations.TraceTwoTorsion

/-!
# Candidate rows killed by two (Lemma B.2 on a periodic star model)

`characteristic-two-mesh-calculations.tex:396–417` (proof of `lem:integral-mesh-cokernels`):
"The proofs of Lemmas A.1 and A.2 apply over `𝒪` without change … Lemma A.2 gives a
surjection from the twisted trace module over `𝒪` onto the integral derivative cokernel."

Over any commutative coefficient ring: on a periodic star model, if the twisted trace of a
word `W₀` is killed by two in every twisted trace module, then so is the class of its
candidate row (`star_two`). The coefficients are first normalized (Lemma A.1, which divides
only by units); the candidate row is then the trace of `W₀`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w

namespace ScalarMeshCategory

variable {V : Type v'} [Quiver.{w} V] {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  [DecidableEq V]

variable (Q) in
/-- **Rows killed by two over every coefficient ring** (the form of Lemma B.2 used here): for
all coefficients `c` over a commutative ring `O`, twice the class of each row is zero. -/
def TwoRows (S : RowSet Q) : Prop :=
  ∀ (O : Type u) [CommRing O] (c : MeshCoefficients O Q) (m : ℕ), 2 ≤ m → ∀ R ∈ S,
    R.2.length = m + 1 → (2 : O) • rowClass c m R.1 R.2 = 0

theorem twoRows_empty : TwoRows.{u} Q ∅ := fun _ _ _ _ _ _ h ↦ absurd h (Set.notMem_empty _)

theorem TwoRows.mono {S S' : RowSet Q} (h : TwoRows.{u} Q S') (hS : S ⊆ S') : TwoRows.{u} Q S :=
  fun O _ c m hm R hR ↦ h O c m hm R (hS hR)

end ScalarMeshCategory

namespace StarTrace

open OrientedTree StarCorner ScalarMeshCategory StarGauge

variable {t : ℕ} {L : Fin t → ℕ}
  {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : (starTree L).ZVert ⥤q V)
  {k : Type u} [CommRing k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]
  [Fintype Q.nonprojective]

theorem rowClass_candRow (c : MeshCoefficients k Q) (σ : StarV L ≃ StarV L)
    (hσ : ∀ a b, (starTree L).G.Adj (σ a) (σ b) ↔ (starTree L).G.Adj a b) (m : ℕ)
    (hσo : σ none = none) (W : List (Fin t)) (hW : 2 * W.length = m + 1)
    (e : π.obj ((starTree L).ztau X₀) =
      hQ.tauE (π.obj ((starTree L).liftEnd ((starTree L).ztau X₀) (wordP W)))) :
    rowClass c m ⟨_, hQ.mem_nonprojective _⟩ ((π.mapPath (liftW W)).cast e rfl) =
      wordTr hQ π c σ hσ m hσo W := by
  unfold wordTr
  rw [if_pos hW]
  unfold phiV OrientedTree.phiD
  rw [(starTree L).rowZ_eq_of_pathStar hQ π c (liftZ_cast_pathStar _ _ _), OrientedTree.rowZ, rowQ]
  split_ifs with h
  · rfl
  · exact absurd e h

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
/-- **Candidate rows killed by two**: if the twisted trace of `W₀` is killed by two in every
twisted trace module (for the twists `θⁿ` of its degrees), so is the class of its candidate
row, over any commutative coefficient ring. -/
theorem star_two (hc0 : 0 < c0) (W₀ : List (Fin t))
    (htwo : ∀ (M : Type (max u v' w)) [AddCommGroup M] [Module k M]
      (D : TraceAlg.TraceData L M) (n : ℕ), D.θ = θ ^ n → 2 * W₀.length = 2 + n * c0 →
        D.tr W₀ + D.tr W₀ = 0)
    (c : MeshCoefficients k Q) (m : ℕ) (hm : 2 ≤ m) :
    ∀ R ∈ candRow hQ π W₀, R.2.length = m + 1 → (2 : k) • rowClass c m R.1 R.2 = 0 := by
  rintro R ⟨e, rfl⟩ hlen
  have hW : 2 * W₀.length = m + 1 := by
    rw [← candRow_length hQ π W₀ _ ⟨e, rfl⟩]; exact hlen
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
  have hc' : OppositeOnMates c' hQ :=
    (starTree L).oppositeOnMates_of_signed hQ π c' hπ hτ hsurj hsig
  -- the degree of the deck transformation
  set E := (starTree L).liftEnd ((starTree L).ztau X₀) (wordP W₀)
  have hEX : π.obj E = π.obj (X₀ (L := L)) := by
    have h1 : hQ.tauE (π.obj E) = hQ.tauE (π.obj (X₀ (L := L))) := by rw [← e, hτ]
    exact hQ.tauE.injective h1
  have hPlen : (liftW (L := L) W₀).length = m + 1 := by
    rw [length_liftZ, length_wordP, hW]
  have hEt : E.t = (X₀ (L := L)).t + (m - 1 : ℤ) := by
    have h1 := (starTree L).t_path (liftW (L := L) W₀)
    rw [hPlen] at h1
    have h2 : ((starTree L).ztau (X₀ (L := L))).t = (X₀ (L := L)).t - 2 := rfl
    rw [h2] at h1
    push_cast at h1
    change E.t = _ at h1
    omega
  have hgt : ∀ (n : ℕ) (Z : (starTree L).ZVert), ((gZ ρ hρ c0 hρp)^[n] Z).t = Z.t + n * c0 :=
    fun n Z ↦ (gZ_iter ρ hρ c0 hρp n Z).2
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) * c0 = m - 1 := by
    obtain ⟨n, hn | hn⟩ := hfib X₀ E hEX.symm
    · exact ⟨n, by have := hgt n X₀; rw [← hn] at this; omega⟩
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
  have hs' : (m : ℤ) + 1 = 2 + s := by simp only [s]; omega
  have hσo' : (ρ ^ n) none = none := by
    clear_value s
    clear hσ' hσp' hiter hdeck' hs' hseven hd hn
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, h0]
  have hL' : ∀ i, L ((θ ^ n) i) = L i := L_pow θ hL n
  have hθ' := pow_ch' ρ θ hL hθ n
  -- the candidate row is the trace of `W₀`
  set D := traceData hQ π c' (ρ ^ n) hσ' m s hσp' hπ hτ hsig hc' hdeck' hs' hσo' (θ ^ n) hL' hθ'
  have hD : rowClass c' m ⟨_, hQ.mem_nonprojective _⟩ ((π.mapPath (liftW W₀)).cast e rfl) =
      D.tr W₀ := rowClass_candRow hQ π c' (ρ ^ n) hσ' m hσo' W₀ hW e
  have h2' : (2 : k) • rowClass c' m ⟨_, hQ.mem_nonprojective _⟩
      ((π.mapPath (liftW W₀)).cast e rfl) = 0 := by
    rw [hD, two_smul]
    exact htwo _ D n rfl (by simp only [s] at hs'; omega)
  -- back along the gauge
  set g := gaugeCoker c' (fun a ↦ (μ a)⁻¹) (fun x ↦ (η x)⁻¹) c hgauge m
  have hg := gaugeCoker_rowClass c' (fun a ↦ (μ a)⁻¹) (fun x ↦ (η x)⁻¹) c hgauge m
    ⟨_, hQ.mem_nonprojective _⟩ ((π.mapPath (liftW W₀)).cast e rfl)
  have h3 := congrArg g h2'
  rw [map_smul, hg, map_zero, smul_smul, mul_comm, ← smul_smul] at h3
  set u : kˣ := (fun x ↦ (η x)⁻¹) (⟨_, hQ.mem_nonprojective _⟩ : Q.nonprojective) *
    pathWt (fun a ↦ (μ a)⁻¹) ((π.mapPath (liftW W₀)).cast e rfl) with hu
  have h4 := congrArg (fun z ↦ ((u⁻¹ : kˣ) : k) • z) h3
  simp only [smul_zero] at h4
  rw [smul_smul, show ((u⁻¹ : kˣ) : k) * ((((fun x ↦ (η x)⁻¹)
      (⟨_, hQ.mem_nonprojective _⟩ : Q.nonprojective) : kˣ) : k) *
      ((pathWt (fun a ↦ (μ a)⁻¹) ((π.mapPath (liftW W₀)).cast e rfl) : kˣ) : k)) = 1 by
    rw [← Units.val_mul, ← Units.val_mul, hu, inv_mul_cancel, Units.val_one], one_smul] at h4
  exact h4

include hπ hτ hsurj hρ h0 hθ hdeck hfib in
/-- **Candidate rows of words whose traces are killed by two.** -/
theorem twoRows_candRow (hc0 : 0 < c0) (W₀ : List (Fin t))
    (htwo : ∀ (M : Type (max u v' w)) [AddCommGroup M] (D : TraceAlg.TraceData L M) (n : ℕ),
      D.θ = θ ^ n → 2 * W₀.length = 2 + n * c0 → D.tr W₀ + D.tr W₀ = 0) :
    TwoRows.{u} Q (candRow hQ π W₀) := fun O _ c m hm ↦
  star_two (k := O) hQ π hπ hτ hsurj ρ hρ h0 θ hL hθ c0 hρp hdeck hfib hc0 W₀
    (fun M _ _ D n hn hd ↦ htwo M D n hn hd) c m hm

end StarTrace

end MultiplicativeBasisDeformations
