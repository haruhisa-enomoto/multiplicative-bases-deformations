module

public import MultiplicativeBasisDeformations.Foundations.StarDSpan
public import MultiplicativeBasisDeformations.Foundations.LineTopPaths
public import MultiplicativeBasisDeformations.Foundations.APaths

/-!
# The reflected models of type `A` in characteristic two (Appendix B)

`characteristic-two-mesh-calculations.tex`: "For the reflected model
`ℤA_{2m+1}/⟨τ^s ρ⟩`, the brick hypothesis forces `s > m`. Otherwise, retaining the central
vertex and the first `s` vertices of each arm gives the reflected `A_{2s+1}` model. The
degree-`2s` paths just constructed go from each vertex to its reflection and increase
the repetition coordinate by `s`. They become nonzero radical endomorphisms at every
object of this quotient. This contradicts the existence of a brick. In the original
model a path from `τv` to `v` has degree `d = 2q` with `s ∣ q − 1`. But `q ≤ m < s`, so a
nonzero such path of degree at least three is impossible."

We re-root at the middle vertex. The twisted traces of words of length at least `m + 1`
vanish (`x^{m+1} = 0` on an arm), and a row of word degree `j` has `j = 1 + n s`; so
for `s ≥ m` all classes vanish. For `s < m`, the deletion to `A_{2s+1}` and the top paths
of `LineTop.line_return` contradict the brick hypothesis (`not_brick_star_to`, the
version of `not_brick_star` with paths ending at the deck image).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w

namespace TraceAlg

variable {M : Type*} [AddCommGroup M]

/-- **Long words on two equal arms vanish**: `x₁ = −x₀` and `x₀^{L+2} = 0`. -/
theorem trace_two_long {L : Fin 2 → ℕ} (hL : L 0 = L 1) (D : TraceData L M) {w : List (Fin 2)}
    (hw : L 0 + 2 ≤ w.length) : D.tr w = 0 := by
  have hx1 : x L 1 = -x L 0 := by
    have := sum_x L
    rw [Fin.sum_univ_two] at this
    exact eq_neg_of_add_eq_zero_right this
  have hprod : ∀ w : List (Fin 2), (w.map (x L)).prod = x L 0 ^ w.length ∨
      (w.map (x L)).prod = -(x L 0 ^ w.length) := by
    intro w
    induction w with
    | nil => simp
    | cons i w ih =>
        rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
        fin_cases i
        · rcases ih with h | h <;> rw [h]
          · exact Or.inl rfl
          · exact Or.inr (mul_neg _ _)
        · simp only [Fin.mk_one, hx1]
          rcases ih with h | h <;> rw [h]
          · exact Or.inr (neg_mul _ _)
          · exact Or.inl (by rw [neg_mul, mul_neg, neg_neg])
  have hpow : x L 0 ^ w.length = 0 := by
    rw [show w.length = (L 0 + 2) + (w.length - (L 0 + 2)) by omega, pow_add, x_pow, zero_mul]
  rw [← D.trR_word]
  rcases hprod w with h | h <;> rw [h, hpow]
  · exact map_zero _
  · rw [neg_zero, map_zero]

end TraceAlg

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
/-- **Exclusion of a period by deletion, with paths to the deck image.** Let `Del` be a
`ρ`-stable set of vertices not containing the centre, and `n c₀ = d > 0`. If each
retained vertex `v` carries a path of degree `d` to `ρⁿ v` that is nonzero in `Π`
modulo `Del`, the brick hypothesis fails. -/
theorem not_brick_star_to (Del : Set (StarV L)) (h0 : none ∉ Del) (hDel : ∀ v, ρ v ∈ Del ↔ v ∈ Del)
    (n d : ℕ) (hnd : n * c0 = d) (hd : 0 < d)
    (hNV : ∀ v : (starTree L).Dbl, (v : StarV L) ∉ Del →
      ∃ p : Quiver.Path v ((starTree L).toDbl ((ρ ^ n) v)), p.length = d ∧
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
      · rw [(gZ_iter ρ hρ c0 hρp n X).1]; rfl
      · rw [(gZ_iter ρ hρ c0 hρp n X).2]
        simp only [E, OrientedTree.liftEnd, hpl, ← hnd]
        push_cast; ring
    rw [hE]
    exact π_gZ_iter π ρ hρ c0 hρp hdeck n X
  · rw [(starTree L).forget_mapPath_liftZ]
    exact hp
  · exact (starTree L).nil_not_mem_del (k := k) Del hXv

end General

/-! ### Positions under the substar embedding -/

theorem pos_ιv {s h : ℕ} (hle : ∀ i, ReRoot.Lmid s i ≤ ReRoot.Lmid h i) (y : StarV (ReRoot.Lmid s)) :
    ReRoot.pos (Substar.ιv hle y) = ReRoot.pos y := by
  rcases y with _ | ⟨i, j⟩
  · rfl
  · simp [Substar.ιv, ReRoot.pos]

theorem mem_Out_Lmid {s h : ℕ} (hs : 1 ≤ s) (hle : ∀ i, ReRoot.Lmid s i ≤ ReRoot.Lmid h i)
    (v : StarV (ReRoot.Lmid h)) : v ∈ Substar.Out hle ↔ (s : ℤ) < |ReRoot.pos v| := by
  rw [Substar.mem_Out_iff, ← ReRoot.depth_eq_abs_pos]
  constructor
  · rintro ⟨i, j, rfl, hlt⟩
    simp only [ReRoot.Lmid] at hlt
    simp only [starDepth]; omega
  · intro hv
    rcases v with _ | ⟨i, j⟩
    · simp [starDepth] at hv; omega
    · refine ⟨i, j, rfl, ?_⟩
      simp only [ReRoot.Lmid]
      simp only [starDepth] at hv; omega

section Reflect

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

include hπ hτ hsurj hc0 hdeck hfib in
/-- **Reflected type `A` under the brick hypothesis** (any characteristic): the
derivatives are surjective. -/
theorem a_reflect_surj (c : MeshCoefficients k Q) (hbrick : BrickHypothesis c) (h : ℕ) (hh : 1 ≤ h)
    (hL : L 0 = 2 * h - 1) (hrev : ∀ x, starDepth (ρ x) + starDepth x = L 0 + 1)
    (m : ℕ) (hm : 2 ≤ m) : MeshDerivativeSurjective c m := by
  set e := ReRoot.midEquiv h hh L hL
  have he := ReRoot.midEquiv_adj h hh L hL
  have hδ := ReRoot.midEquiv_par h hh L hL
  set ρ₁ := ReRoot.ρ' e ρ
  -- `ρ₁` is the reflection of the re-rooted line
  have hrefl : ∀ v, ReRoot.pos (ρ₁ v) = -ReRoot.pos v := by
    intro v
    simp only [ρ₁, ReRoot.ρ', Equiv.trans_apply]
    rw [ReRoot.pos_midEquiv]
    have h1 := hrev (e.symm v)
    have h2 := ReRoot.pos_midEquiv h hh L hL (e.symm v)
    rw [Equiv.apply_symm_apply] at h2
    rw [hL] at h1
    rw [h2]; omega
  have h0 : ρ₁ none = none := by
    apply ReRoot.pos_injective
    rw [hrefl]; simp [ReRoot.pos]
  set π₁ := ReRoot.π' e he (h : ℤ) hδ π
  have hρ₁ := ReRoot.ρ'_adj e he ρ hρ
  have hρ₁' : ∀ a b, starAdj a b ↔ starAdj (ρ₁ a) (ρ₁ b) := fun a b ↦ (hρ₁ a b).symm
  have hρ₁p := ReRoot.ρ'_par e (h : ℤ) hδ ρ c0 hρp
  have hdeck₁ := ReRoot.π'_deck e he (h : ℤ) hδ π ρ hρ c0 hρp hdeck
  have hfib₁ := ReRoot.π'_fib e he (h : ℤ) hδ π ρ hρ c0 hρp hfib
  have hπ₁ := ReRoot.π'_isCovering e he (h : ℤ) hδ π hπ
  have hτ₁ := ReRoot.π'_tau e he (h : ℤ) hδ hQ π hτ
  have hsurj₁ := ReRoot.π'_surj e he (h : ℤ) hδ π hsurj
  -- `c₀` is even
  have hc0e : Even c0 := by
    have := hρ₁p none
    rw [h0, left_eq_add] at this
    exact (ZMod.natCast_eq_zero_iff_even).1 (by exact_mod_cast this)
  obtain ⟨s, hs⟩ := hc0e
  obtain ⟨θ, hLθ, hθ⟩ := arm_perm ρ₁ hρ₁' h0
  have hθ' : ∀ i j (hj : j ≤ ReRoot.Lmid h i), ρ₁ (ch i j hj) = ch (θ i) j (by rw [hLθ]; exact hj) := by
    intro i j hj
    obtain ⟨_, h'⟩ := hθ i j (Nat.lt_succ_iff.2 hj)
    exact h'
  by_cases hsh : h ≤ s
  · refine star_surjective_deg hQ π₁ hπ₁ hτ₁ hsurj₁ ρ₁ hρ₁ h0 θ hLθ hθ' c0 hρ₁p hdeck₁ hfib₁ hc0
      (fun M _ _ D n _ w hw2 hd ↦ ?_) c m hm
    refine TraceAlg.trace_two_long (L := ReRoot.Lmid h) rfl D ?_
    simp only [ReRoot.Lmid]
    have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · omega
      · exact hn
    have : 2 * s ≤ n * c0 := by rw [hs]; nlinarith
    omega
  · exfalso
    have hs1 : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with rfl | h'
      · omega
      · exact h'
    have hle : ∀ i, ReRoot.Lmid s i ≤ ReRoot.Lmid h i := fun _ ↦ by simp only [ReRoot.Lmid]; omega
    refine not_brick_star_to hQ π₁ c hπ₁ hτ₁ hsurj₁ ρ₁ hρ₁ c0 hρ₁p hdeck₁ hfib₁ (Substar.Out hle)
      (fun h' ↦ h' none rfl) (fun v ↦ ?_) 1 c0 (one_mul c0) hc0 (fun v hv ↦ ?_) hbrick
    · rw [mem_Out_Lmid hs1, mem_Out_Lmid hs1, hrefl, abs_neg]
    · simp only [Substar.Out, Set.mem_ofPred_eq, not_forall, not_not] at hv
      obtain ⟨y, rfl⟩ := hv
      have hyb := LineTop.pos_le s hs1 y
      obtain ⟨q, hql, hq⟩ := LineTop.line_return s hs1 (k := k) y
        (ReRoot.ofPos s (-ReRoot.pos (y : StarV (ReRoot.Lmid s))) (by omega))
        (ReRoot.pos_ofPos s _ _)
      have heq : (starTree (ReRoot.Lmid h)).toDbl ((ρ₁ ^ 1) ((Substar.ιq hle).obj y)) =
          (Substar.ιq hle).obj (ReRoot.ofPos s (-ReRoot.pos (y : StarV (ReRoot.Lmid s))) (by omega)) := by
        apply ReRoot.pos_injective
        change ReRoot.pos ((ρ₁ ^ 1) (Substar.ιv hle y)) =
          ReRoot.pos (Substar.ιv hle (ReRoot.ofPos s _ _))
        rw [pow_one, hrefl, pos_ιv, pos_ιv, ReRoot.pos_ofPos]
      rw [heq]
      exact ⟨(Substar.ιq hle).mapPath q, by rw [LinearPaths.length_mapPath, hql, hs]; ring,
        Substar.not_mem_del hle q hq⟩

end Reflect

end StarTrace

end MultiplicativeBasisDeformations
