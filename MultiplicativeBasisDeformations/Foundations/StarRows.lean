import MultiplicativeBasisDeformations.Foundations.StarTrace

/-!
# Every row class is a word trace (Lemmas A.2 and A.4)

`lem:twisted-trace-surjection` (surjectivity) and `lem:arm-trace-reduction`
(first part), `periodic-mesh-calculations.tex`: "Lift a row path from
`τ(x, j)`. … The map from twisted paths to row classes is well defined and
surjective." and "If a path from `v` to `θ v` meets the centre `o`, cut it there.
Twisted rotation gives a path from `o` to `θ o = o`, and Lemma A.3 expresses it
in the `x_i`. A path avoiding `o` stays on one arm. That arm is fixed pointwise
by `θ` … the process ends in zero."
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w

namespace Quiver.Path

variable {W : Type*} [Quiver W]

theorem vertices_cast' {a b a' b' : W} (p : Quiver.Path a b) (ha : a = a') (hb : b = b') :
    (p.cast ha hb).vertices = p.vertices := by
  subst ha hb; rfl

theorem mem_of_mem_left {a b x y : W} (U : Quiver.Path a x) (V' : Quiver.Path x b)
    (hy : y ∈ U.vertices) : y ∈ (U.comp V').vertices := by
  rw [Quiver.Path.vertices_comp]
  rw [← Quiver.Path.dropLast_append_end_eq U, List.mem_append, List.mem_singleton] at hy
  rcases hy with hy | rfl
  · exact List.mem_append_left _ hy
  · exact List.mem_append_right _ (StarTrace.start_mem_vertices V')

theorem mem_of_mem_right {a b x y : W} (U : Quiver.Path a x) (V' : Quiver.Path x b)
    (hy : y ∈ V'.vertices) : y ∈ (U.comp V').vertices := by
  rw [Quiver.Path.vertices_comp]; exact List.mem_append_right _ hy

theorem mem_rotate {a x y : W} (U : Quiver.Path a x) (V' : Quiver.Path x a)
    (hy : y ∈ (V'.comp U).vertices) : y ∈ (U.comp V').vertices := by
  rw [Quiver.Path.vertices_comp] at hy
  rcases List.mem_append.1 hy with hy | hy
  · exact mem_of_mem_right U V' (List.mem_of_mem_dropLast hy)
  · exact mem_of_mem_left U V' hy

end Quiver.Path

namespace OrientedTree

variable {D : Type*} (T : OrientedTree D)

theorem t_path {X : T.ZVert} : ∀ {E : T.ZVert} (P : Quiver.Path X E), E.t = X.t + P.length
  | _, Quiver.Path.nil => by simp
  | _, Quiver.Path.cons P a => by
      rw [Quiver.Path.length_cons, a.down.2, t_path P]; push_cast; ring

end OrientedTree

namespace StarTrace

open OrientedTree StarCorner ScalarMeshCategory

variable {t : ℕ} {L : Fin t → ℕ}

theorem av_eq_of {i : Fin t} {j j' : ℕ} (e : j = j') (h : j ≤ L i) (h' : j' ≤ L i) :
    av L i j h = av L i j' h' := by subst e; rfl

/-- A path avoiding the centre stays on its arm. -/
theorem arm_of_avoid (i : Fin t) (j : ℕ) (hj : j ≤ L i) {b : (starTree L).Dbl}
    (p : Quiver.Path (av L i j hj) b) (hp : o L ∉ p.vertices) :
    ∀ y ∈ p.vertices, ∃ (j' : ℕ) (h' : j' ≤ L i), y = av L i j' h' := by
  induction p with
  | nil =>
      intro y hy
      rw [Quiver.Path.vertices_nil, List.mem_singleton] at hy
      exact ⟨j, hj, hy⟩
  | @cons b c p e ih =>
      have ih' := ih (fun h ↦ hp (by
        rw [Quiver.Path.mem_vertices_cons]; exact Or.inl h))
      intro y hy
      rw [Quiver.Path.mem_vertices_cons] at hy
      rcases hy with hy | rfl
      · exact ih' y hy
      · obtain ⟨jb, hjb, rfl⟩ := ih' _ (Quiver.Path.end_mem_vertices p)
        have ha := e.down
        rcases y with _ | ⟨i', ⟨j', hj'⟩⟩
        · exact absurd (Quiver.Path.end_mem_vertices _) hp
        · change starAdj (some ⟨i, ⟨jb, _⟩⟩) (some ⟨i', ⟨j', hj'⟩⟩) at ha
          obtain ⟨rfl, -⟩ := ha
          exact ⟨j', Nat.lt_succ_iff.1 hj', rfl⟩

/-- A path all of whose vertices coincide is trivial (the star has no loops). -/
theorem length_eq_zero_of_const {a : (starTree L).Dbl} {b : (starTree L).Dbl}
    (p : Quiver.Path a b) (hp : ∀ y ∈ p.vertices, y = a) : p.length = 0 := by
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
      exfalso
      have hb : b = a := hp b (by rw [Quiver.Path.mem_vertices_cons]
                                  exact Or.inl (Quiver.Path.end_mem_vertices p))
      have hc : c = a := hp c (Quiver.Path.end_mem_vertices _)
      have := e.down
      rw [hb, hc] at this
      exact (starTree L).G.irrefl this

variable {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : (starTree L).ZVert ⥤q V)
  {k : Type u} [CommRing k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)
  [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]
  (σ : StarV L ≃ StarV L) (hσ : ∀ a b, (starTree L).G.Adj (σ a) (σ b) ↔ (starTree L).G.Adj a b)
  (m : ℕ) (s : ℤ) (hσp : ∀ v, (starTree L).par (σ v) = (starTree L).par v + s)
  (hπ : π.IsCovering) (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y))
  (hsig : (starTree L).pullCoeff hQ π c = (starTree L).zSigned k) (hc : OppositeOnMates c hQ)
  (hdeck : ∀ Z, π.obj (((starTree L).zAct σ hσ s hσp).obj Z) = π.obj Z)
  (hs : (m : ℤ) + 1 = 2 + s)
  (hσo : σ none = none) (θ : Equiv.Perm (Fin t)) (hL : ∀ i, L (θ i) = L i)
  (hθ : ∀ i j (hj : j ≤ L i), σ (av L i j hj) = av L (θ i) j (by rw [hL]; exact hj))

include hπ hτ hsig hc hdeck hs hθ in
/-- **Lemma A.4, first part**: the lifted row class of a path from `v` to `σ v`
is a word trace at the centre, or zero. -/
theorem phiD_mem_span (v : (starTree L).Dbl) (h : ℤ) (hh : (h : ZMod 2) = (starTree L).par v)
    (p : Quiver.Path ((starTree L).toDbl v) (((starTree L).dAct σ hσ).obj ((starTree L).toDbl v)))
    (hp : p.length = m + 1) :
    (starTree L).phiD hQ π c m ⟨v, h, hh⟩ p ∈
      Submodule.span k (Set.range (wordTr hQ π c σ hσ m hσo)) := by
  by_cases ho : o L ∈ p.vertices
  · -- cut at the centre and rotate
    obtain ⟨U, W, rfl⟩ := Quiver.Path.exists_eq_comp_of_mem_vertices p ho
    rw [(starTree L).phiD_rotate_path hQ π c hτ σ hσ s hσp hc hdeck hs ⟨v, h, hh⟩ U W
      (by rw [← Quiver.Path.length_comp]; exact hp)]
    set C := W.comp (((starTree L).dAct σ hσ).mapPath U)
    have hC : C.length = m + 1 := by
      rw [Quiver.Path.length_comp, LinearPaths.length_mapPath, add_comm,
        ← Quiver.Path.length_comp, hp]
    obtain ⟨w', hw', hl⟩ := normal_form k (C.cast rfl (show ((starTree L).dAct σ hσ).obj (o L) =
      o L from hσo))
    have key : (starTree L).phiD hQ π c m ((starTree L).liftEnd ⟨v, h, hh⟩ U) C =
        phiV hQ π c σ hσ m (o L) hσo _ ((starTree L).liftEnd ⟨v, h, hh⟩ U).ht
          (C.cast rfl (show ((starTree L).dAct σ hσ).obj (o L) = o L from hσo)) := by
      unfold phiV
      rw [Quiver.Path.cast_cast]
      rfl
    rw [length_cast, hC] at hl
    have h0 : starDepth (L := L) (o L) = 0 := rfl
    rw [key, phiV_congr hQ π c σ hσ m hπ hτ hsig _ _ _ _ hw',
      phiV_height hQ π c σ hσ m s hσp hτ hc hdeck hs (o L) hσo _ 0 _ par_o _
        (by rw [Quiver.Path.length_comp, length_wordP, length_geod, h0]; omega)]
    refine Submodule.subset_span ⟨w', ?_⟩
    rw [wordTr, if_pos (by rw [h0] at hl; omega)]
    rfl
  · -- a path avoiding the centre lies on a fixed arm
    rcases v with _ | ⟨i, ⟨j, hj⟩⟩
    · exact absurd (start_mem_vertices p) ho
    have hj' : j ≤ L i := Nat.lt_succ_iff.1 hj
    have harm := arm_of_avoid i j hj' p ho
    obtain ⟨j'', hj'', hend⟩ := harm _ (Quiver.Path.end_mem_vertices p)
    have hi : θ i = i := by
      have e1 := hθ i j hj'
      change σ (av L i j hj') = _ at hend
      rw [e1] at hend
      exact (Sigma.mk.inj_iff.1 (Option.some.inj hend)).1
    have hfix : ((starTree L).dAct σ hσ).obj (av L i j hj') = av L i j hj' :=
      fix_av σ θ hL hθ hi j hj'
    have key : (starTree L).phiD hQ π c m ⟨av L i j hj', h, hh⟩ p =
        phiV hQ π c σ hσ m (av L i j hj') hfix h hh (p.cast rfl hfix) := by
      unfold phiV
      rw [Quiver.Path.cast_cast]
      rfl
    change (starTree L).phiD hQ π c m ⟨av L i j hj', h, hh⟩ p ∈ _
    rw [key]
    set p' := p.cast rfl hfix
    have hp'v : ∀ y ∈ p'.vertices, ∃ (j' : ℕ) (h' : j' ≤ L i), y = av L i j' h' := by
      intro y hy; rw [Quiver.Path.vertices_cast'] at hy; exact harm y hy
    -- the vertex of minimal depth
    classical
    obtain ⟨u, hu, hmin⟩ := p'.vertices.toFinset.exists_min_image (fun y ↦ starDepth (L := L) y)
      ⟨_, List.mem_toFinset.2 (start_mem_vertices p')⟩
    rw [List.mem_toFinset] at hu
    obtain ⟨r, hr, rfl⟩ := hp'v u hu
    obtain ⟨U, W, hUW⟩ := Quiver.Path.exists_eq_comp_of_mem_vertices p' hu
    have hfixU : ∀ x ∈ U.vertices, σ x = x := by
      intro x hx
      obtain ⟨j', h', rfl⟩ := hp'v x (by rw [hUW]; exact Quiver.Path.mem_of_mem_left U W hx)
      exact fix_av σ θ hL hθ hi j' h'
    have hlen : U.length + W.length = m + 1 := by
      rw [← Quiver.Path.length_comp, ← hUW, length_cast, hp]
    rw [hUW, phiV_rotate_fixed hQ π c σ hσ m s hσp hτ hc hdeck hs _ _ hfix
      (fix_av σ θ hL hθ hi r hr) h hh U W hfixU hlen]
    set R := W.comp U
    have hR : ∀ y ∈ R.vertices, ∃ (n : ℕ) (h' : r + n ≤ L i), y = av L i (r + n) h' := by
      intro y hy
      have hy' : y ∈ p'.vertices := by rw [hUW]; exact Quiver.Path.mem_rotate U W hy
      obtain ⟨j', h', rfl⟩ := hp'v y hy'
      have := hmin _ (List.mem_toFinset.2 hy')
      simp only [av, OrientedTree.toDbl, starDepth] at this
      exact ⟨j' - r, by omega, av_eq_of (by omega) _ _⟩
    have hRlen : R.length = m + 1 := by rw [Quiver.Path.length_comp, add_comm, hlen]
    have hr' : r + 1 ≤ L i := by
      by_contra hcon
      have : R.length = 0 := length_eq_zero_of_const R fun y hy ↦ by
        obtain ⟨n, h', rfl⟩ := hR y hy
        exact av_eq_of (by omega) _ _
      omega
    obtain ⟨q, n, hn, hb, hmem, hl⟩ := arm_normal_form k i r hr' R hR
    obtain rfl : n = 0 := by
      have := congrArg (fun y : (starTree L).Dbl ↦ starDepth (L := L) y) hb
      simp only [av, OrientedTree.toDbl, starDepth] at this
      omega
    have hq : R.length = 2 * q := by rw [hl]; rfl
    rw [phiV_congr hQ π c σ hσ m hπ hτ hsig _ _ _ _ hmem]
    have e0 : (cpow (yb (L := L) i r hr') q).comp ((geodR i r 0 hn).cast rfl hb) =
        cpow (yb i r hr') q := rfl
    rw [e0, phiV_yb_zero hQ π c σ hσ m s hσp hπ hτ hsig hc hdeck hs θ hL hθ hi _ r hr' rfl _ _ q
      (by omega) (by omega)]
    exact zero_mem _

include hπ hτ hsig hc hdeck hs hθ in
/-- **Lemma A.2, surjectivity**: every row class of degree `m + 1 = 2 + s` is a
combination of word traces at the centre. -/
theorem rowClass_mem_span (hsurj : ∀ x : V, ∃ X, π.obj X = x)
    (hfib : ∀ X E : (starTree L).ZVert, π.obj E = π.obj X → E.t = X.t + s →
      E = ((starTree L).zAct σ hσ s hσp).obj X)
    (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1) (hw : w.length = m + 1) :
    rowClass c m x w ∈ Submodule.span k (Set.range (wordTr hQ π c σ hσ m hσo)) := by
  obtain ⟨X, hX⟩ := hsurj x.1
  have e1 : π.obj ((starTree L).ztau X) = (Q.tau x).1 := by rw [hτ, hX]; rfl
  obtain ⟨E, hE, P, hP⟩ := RelSystem.exists_lift π hπ ((starTree L).ztau X) (w.cast e1.symm rfl)
  have hPlen : P.length = m + 1 := by
    rw [← LinearPaths.length_mapPath π P, hP, length_cast, length_cast, hw]
  have hEt : E.t = X.t + s := by
    have := (starTree L).t_path P
    rw [hPlen] at this
    simp only [ztau] at this
    push_cast at this
    omega
  have hEX : E = ((starTree L).zAct σ hσ s hσp).obj X := hfib X E (hE.trans hX.symm) hEt
  have r1 : rowClass c m x w = (starTree L).rowZ hQ π c m P := by
    rw [OrientedTree.rowZ, hP, rowQ_cast, rowQ_cast]
    exact (rowQ_eq c hQ m w).symm
  set p' : Quiver.Path ((starTree L).toDbl X.v)
      (((starTree L).dAct σ hσ).obj ((starTree L).toDbl X.v)) :=
    ((starTree L).forget.mapPath P).cast rfl (congrArg OrientedTree.ZVert.v hEX)
  have r2 : (starTree L).rowZ hQ π c m P = (starTree L).phiD hQ π c m X p' := by
    apply (starTree L).rowZ_eq_of_pathStar
    apply (starTree L).pathStar_eq_of_forget
    refine Sigma.ext (by have := congrArg OrientedTree.ZVert.v hEX; exact this) ?_
    rw [forget_mapPath_liftZ]
    dsimp only
    exact (Quiver.Path.cast_heq _ _ _).symm
  rw [r1, r2]
  exact phiD_mem_span hQ π c σ hσ m s hσp hπ hτ hsig hc hdeck hs hσo θ hL hθ X.v X.t X.ht p'
    (by rw [length_cast, LinearPaths.length_mapPath, hPlen])

end StarTrace

end MultiplicativeBasisDeformations
