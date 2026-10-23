module

public import MultiplicativeBasisDeformations.Foundations.TwistedTrace
public import MultiplicativeBasisDeformations.Foundations.StarCorner
public import MultiplicativeBasisDeformations.Foundations.PathShape

/-!
# Twisted traces on a star (Lemmas A.2 and A.4)

`lem:twisted-trace-surjection`, `lem:arm-trace-reduction`
(`periodic-mesh-calculations.tex`). Let `π : ℤΔ → Q` be a covering of a
star model with signed coefficients, and let `(v, t) ↦ (σ v, t + s)` be a deck
transformation with `σ` fixing the centre. In degree `d = m + 1 = 2 + s`, the row
class of a closed path at a `σ`-fixed vertex `v` (`phiV`) is independent of the
height, kills the relations of `Π(Δ)`, and satisfies twisted rotation.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w

namespace StarTrace

open OrientedTree StarCorner ScalarMeshCategory

variable {t : ℕ} {L : Fin t → ℕ}
  {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : (starTree L).ZVert ⥤q V)
  {k : Type u} [CommRing k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)
  [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]
  (σ : StarV L ≃ StarV L) (hσ : ∀ a b, (starTree L).G.Adj (σ a) (σ b) ↔ (starTree L).G.Adj a b)
  (m : ℕ)

/-- The row class of a closed path at a `σ`-fixed vertex, lifted at height `h`. -/
def phiV (v : (starTree L).Dbl) (hv : σ v = v) (h : ℤ) (hh : (h : ZMod 2) = (starTree L).par v)
    (p : Quiver.Path v v) : Coker c m :=
  (starTree L).phiD hQ π c m ⟨v, h, hh⟩
    (p.cast rfl (show v = ((starTree L).dAct σ hσ).obj ((starTree L).toDbl v) from hv.symm))

theorem start_mem_vertices {W : Type*} [Quiver W] {a b : W} (U : Quiver.Path a b) :
    a ∈ U.vertices :=
  List.mem_of_mem_head? (by rw [Quiver.Path.vertices_head?]; rfl)

theorem dAct_mapPath_eq_cast {a b : (starTree L).Dbl} (U : Quiver.Path a b)
    (hU : ∀ x ∈ U.vertices, σ x = x) :
    ((starTree L).dAct σ hσ).mapPath U =
      U.cast (show a = ((starTree L).dAct σ hσ).obj a from (hU a (start_mem_vertices U)).symm)
        (show b = ((starTree L).dAct σ hσ).obj b from
          (hU b (Quiver.Path.end_mem_vertices U)).symm) := by
  apply Quiver.Path.eq_cast_of_vertices_eq
  rw [LinearPaths.vertices_mapPath]
  conv_rhs => rw [← List.map_id U.vertices]
  exact List.map_congr_left (fun x hx ↦ hU x hx)

theorem length_cast {W : Type*} [Quiver W] {a b a' b' : W} (p : Quiver.Path a b) (ha : a = a')
    (hb : b = b') : (p.cast ha hb).length = p.length := by
  subst ha hb; rfl

theorem comp_cast_right {W : Type*} [Quiver W] {a b c c' : W} (p : Quiver.Path a b)
    (q : Quiver.Path b c) (h : c = c') : (p.comp q).cast rfl h = p.comp (q.cast rfl h) := by
  subst h; rfl

theorem cast_comp_cast {W : Type*} [Quiver W] {a b b' c c' : W} (p : Quiver.Path a b)
    (q : Quiver.Path b c) (hb : b = b') (hc : c = c') :
    (p.cast rfl hb).comp (q.cast hb hc) = (p.comp q).cast rfl hc := by
  subst hb hc; rfl

variable (s : ℤ) (hσp : ∀ v, (starTree L).par (σ v) = (starTree L).par v + s)
  (hπ : π.IsCovering) (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y))
  (hsig : (starTree L).pullCoeff hQ π c = (starTree L).zSigned k) (hc : OppositeOnMates c hQ)
  (hdeck : ∀ Z, π.obj (((starTree L).zAct σ hσ s hσp).obj Z) = π.obj Z)
  (hs : (m : ℤ) + 1 = 2 + s)

include hτ hc hdeck hs in
theorem phiV_height (v : (starTree L).Dbl) (hv : σ v = v) (h h' : ℤ)
    (hh : (h : ZMod 2) = (starTree L).par v) (hh' : (h' : ZMod 2) = (starTree L).par v)
    (p : Quiver.Path v v) (hp : p.length = m + 1) :
    phiV hQ π c σ hσ m v hv h hh p = phiV hQ π c σ hσ m v hv h' hh' p :=
  (starTree L).phiD_height hQ π c hτ σ hσ s hσp hc hdeck hs ⟨v, h, hh⟩ _
    (by rw [length_cast, hp]) h' hh'

include hτ hc hdeck hs in
/-- **Twisted rotation** in terms of `phiV`. -/
theorem phiV_rotate (v z : (starTree L).Dbl) (hv : σ v = v) (hz : σ z = z) (h : ℤ)
    (hh : (h : ZMod 2) = (starTree L).par v) (U : Quiver.Path v z) (W : Quiver.Path z v)
    (U' : Quiver.Path v z)
    (hU : ((starTree L).dAct σ hσ).mapPath U =
      U'.cast (show v = ((starTree L).dAct σ hσ).obj v from hv.symm)
        (show z = ((starTree L).dAct σ hσ).obj z from hz.symm))
    (hlen : U.length + W.length = m + 1) :
    phiV hQ π c σ hσ m v hv h hh (U.comp W) =
      phiV hQ π c σ hσ m z hz (h + U.length) ((starTree L).liftEnd ⟨v, h, hh⟩ U).ht (W.comp U') := by
  unfold phiV
  rw [comp_cast_right]
  rw [(starTree L).phiD_rotate_path hQ π c hτ σ hσ s hσp hc hdeck hs ⟨v, h, hh⟩ U _
    (by rw [length_cast, hlen]), hU, cast_comp_cast]
  rfl

include hτ hc hdeck hs in
/-- Rotation of an initial segment whose vertices are fixed by `σ`. -/
theorem phiV_rotate_fixed (v z : (starTree L).Dbl) (hv : σ v = v) (hz : σ z = z) (h : ℤ)
    (hh : (h : ZMod 2) = (starTree L).par v) (U : Quiver.Path v z) (W : Quiver.Path z v)
    (hU : ∀ x ∈ U.vertices, σ x = x) (hlen : U.length + W.length = m + 1) :
    phiV hQ π c σ hσ m v hv h hh (U.comp W) =
      phiV hQ π c σ hσ m z hz (h + U.length) ((starTree L).liftEnd ⟨v, h, hh⟩ U).ht (W.comp U) :=
  phiV_rotate hQ π c σ hσ m s hσp hτ hc hdeck hs v z hv hz h hh U W U
    (dAct_mapPath_eq_cast σ hσ U hU) hlen

/-- The linear extension of `phiV`. -/
def phiVL (v : (starTree L).Dbl) (hv : σ v = v) (h : ℤ) (hh : (h : ZMod 2) = (starTree L).par v) :
    (LinearPaths.obj (k := k) v ⟶ LinearPaths.obj v) →ₗ[k] Coker c m :=
  LinearPaths.extend (phiV hQ π c σ hσ m v hv h hh)

theorem phiVL_eq (v : (starTree L).Dbl) (hv : σ v = v) (h : ℤ)
    (hh : (h : ZMod 2) = (starTree L).par v) (f : LinearPaths.obj (k := k) v ⟶ LinearPaths.obj v) :
    phiVL hQ π c σ hσ m v hv h hh f = (starTree L).phiL hQ π c m ⟨v, h, hh⟩ _
      (f ≫ eqToHom (congrArg LinearPaths.obj
        (show v = ((starTree L).dAct σ hσ).obj ((starTree L).toDbl v) from hv.symm))) := by
  induction f using LinearPaths.induction_on with
  | h0 => simp
  | hadd f g hf hg => rw [map_add, hf, hg, Preadditive.add_comp, map_add]
  | hsingle p a =>
      rw [map_smul, Linear.smul_comp, map_smul]
      congr 1
      rw [phiVL, LinearPaths.extend_path, phiV, OrientedTree.phiL, ← LinearPaths.extend_path
        (k := k) ((starTree L).phiD hQ π c m _), RelSystem.path_cast]
      simp

include hπ hτ hsig in
theorem phiVL_eq_zero_of_mem (v : (starTree L).Dbl) (hv : σ v = v) (h : ℤ)
    (hh : (h : ZMod 2) = (starTree L).par v) {f : LinearPaths.obj (k := k) v ⟶ LinearPaths.obj v}
    (hf : f ∈ ((starTree L).preproj k).ideal _ _) : phiVL hQ π c σ hσ m v hv h hh f = 0 := by
  rw [phiVL_eq]
  exact (starTree L).phiL_eq_zero_of_mem hQ π c hπ hτ hsig m _
    (((starTree L).preproj k).mem_ideal_comp hf _)

/-! ### Traces of words at the centre -/

variable (hσo : σ none = none) (θ : Equiv.Perm (Fin t)) (hL : ∀ i, L (θ i) = L i)
  (hθ : ∀ i j (hj : j ≤ L i), σ (av L i j hj) = av L (θ i) j (hj.trans (hL i).ge))

theorem vertices_wordP (i : Fin t) (w : List (Fin t)) :
    (wordP (L := L) (i :: w)).vertices = [o L, av L i 0 (Nat.zero_le _)] ++ (wordP w).vertices := by
  rw [wordP, Quiver.Path.vertices_comp]
  congr 1

include hσo hθ in
theorem map_vertices_wordP (w : List (Fin t)) :
    (wordP (L := L) w).vertices.map σ = (wordP (w.map θ)).vertices := by
  induction w with
  | nil => simp only [wordP, Quiver.Path.vertices_nil, List.map_cons, List.map_nil, List.map];
           exact congrArg (· :: []) hσo
  | cons i w ih =>
      rw [vertices_wordP, List.map_cons, vertices_wordP, List.map_append, ih]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [hθ i 0 (Nat.zero_le _)]
      exact congrArg (· :: _) hσo

include hσo hθ in
theorem dAct_wordP (w : List (Fin t)) :
    ((starTree L).dAct σ hσ).mapPath (wordP w) =
      (wordP (w.map θ)).cast (show o L = ((starTree L).dAct σ hσ).obj (o L) from hσo.symm)
        (show o L = ((starTree L).dAct σ hσ).obj (o L) from hσo.symm) := by
  apply Quiver.Path.eq_cast_of_vertices_eq
  rw [LinearPaths.vertices_mapPath]
  exact map_vertices_wordP σ hσo θ hL hθ w

theorem par_o : ((0 : ℤ) : ZMod 2) = (starTree L).par (o L) := by
  simp [starTree, o, OrientedTree.toDbl, starDepth]

/-- **The trace of a word** `w` in the `x_i`: the row class of the closed path at
the centre, in path degree `2 |w| = m + 1`, and zero in other degrees. -/
def wordTr (w : List (Fin t)) : Coker c m :=
  if 2 * w.length = m + 1 then phiV hQ π c σ hσ m (o L) hσo 0 par_o (wordP w) else 0

include hτ hc hdeck hs hθ in
/-- **Twisted rotation of words**: `[u v] = [v θ(u)]`. -/
theorem wordTr_rotate (u v : List (Fin t)) :
    wordTr hQ π c σ hσ m hσo (u ++ v) = wordTr hQ π c σ hσ m hσo (v ++ u.map θ) := by
  unfold wordTr
  simp only [List.length_append, List.length_map]
  by_cases hd : 2 * (u.length + v.length) = m + 1
  · rw [if_pos hd, if_pos (by omega), wordP_append,
      phiV_rotate hQ π c σ hσ m s hσp hτ hc hdeck hs (o L) (o L) hσo hσo 0 par_o _ _
        (wordP (u.map θ)) (dAct_wordP σ hσ hσo θ hL hθ u)
        (by rw [length_wordP, length_wordP]; omega),
      phiV_height hQ π c σ hσ m s hσp hτ hc hdeck hs (o L) hσo _ 0 _ par_o _
        (by rw [Quiver.Path.length_comp, length_wordP, length_wordP, List.length_map]; omega),
      ← wordP_append]
  · rw [if_neg hd, if_neg (by omega)]

theorem phiVL_path (v : (starTree L).Dbl) (hv : σ v = v) (h : ℤ)
    (hh : (h : ZMod 2) = (starTree L).par v) (p : Quiver.Path v v) :
    phiVL hQ π c σ hσ m v hv h hh (LinearPaths.path p) = phiV hQ π c σ hσ m v hv h hh p :=
  LinearPaths.extend_path _ _

include hπ hτ hsig in
/-- **The centre relation** `∑ x_i = 0` in traces. -/
theorem wordTr_centre (u v : List (Fin t)) :
    ∑ i, wordTr hQ π c σ hσ m hσo (u ++ i :: v) = 0 := by
  unfold wordTr
  simp only [List.length_append, List.length_cons]
  by_cases hd : 2 * (u.length + (v.length + 1)) = m + 1
  · simp only [if_pos hd]
    have hmem := ((starTree L).preproj k).comp_mem_ideal (LinearPaths.path (wordP u))
      (((starTree L).preproj k).mem_ideal_comp (sum_xp_mem (L := L) k) (LinearPaths.path (wordP v)))
    have := phiVL_eq_zero_of_mem hQ π c σ hσ m hπ hτ hsig (o L) hσo 0 par_o hmem
    rw [Preadditive.sum_comp, Preadditive.comp_sum, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [LinearPaths.path_comp_path, LinearPaths.path_comp_path, phiVL_path, wordP_append]
    rfl
  · simp [if_neg hd]

include hπ hτ hsig in
/-- **The arm relation** `x_i^{L_i+1} = 0` in traces. -/
theorem wordTr_arm (u v : List (Fin t)) (i : Fin t) :
    wordTr hQ π c σ hσ m hσo (u ++ List.replicate (L i + 2) i ++ v) = 0 := by
  unfold wordTr
  split_ifs with hd
  · have hmem := ((starTree L).preproj k).comp_mem_ideal (LinearPaths.path (wordP u))
      (((starTree L).preproj k).mem_ideal_comp (xp_pow_mem (L := L) k i)
        (LinearPaths.path (wordP v)))
    have := phiVL_eq_zero_of_mem hQ π c σ hσ m hπ hτ hsig (o L) hσo 0 par_o hmem
    rw [LinearPaths.path_comp_path, LinearPaths.path_comp_path, phiVL_path] at this
    rw [wordP_append, wordP_append, Quiver.Path.comp_assoc]
    exact this
  · rfl

/-! ### Arms fixed by the twist (Lemma A.4, second part) -/

theorem av_congr {i i' : Fin t} (e : i' = i) (j : ℕ) (h : j ≤ L i') (h' : j ≤ L i) :
    av L i' j h = av L i j h' := by subst e; rfl

include hθ in
theorem fix_av {i : Fin t} (hi : θ i = i) (j : ℕ) (hj : j ≤ L i) : σ (av L i j hj) = av L i j hj :=
  (hθ i j hj).trans (av_congr hi j _ hj)

include hπ hτ hsig in
/-- Closed paths with the same class modulo the relations have the same row class. -/
theorem phiV_congr (v : (starTree L).Dbl) (hv : σ v = v) (h : ℤ)
    (hh : (h : ZMod 2) = (starTree L).par v) {p p' : Quiver.Path v v}
    (hp : LinearPaths.path p - LinearPaths.path p' ∈ ((starTree L).preproj k).ideal _ _) :
    phiV hQ π c σ hσ m v hv h hh p = phiV hQ π c σ hσ m v hv h hh p' := by
  have := phiVL_eq_zero_of_mem hQ π c σ hσ m hπ hτ hsig v hv h hh hp
  rw [map_sub, phiVL_path, phiVL_path, sub_eq_zero] at this
  exact this

include hπ hτ hsig in
theorem phiV_mem (v : (starTree L).Dbl) (hv : σ v = v) (h : ℤ)
    (hh : (h : ZMod 2) = (starTree L).par v) {p : Quiver.Path v v}
    (hp : LinearPaths.path p ∈ ((starTree L).preproj k).ideal _ _) :
    phiV hQ π c σ hσ m v hv h hh p = 0 := by
  rw [← phiVL_path]; exact phiVL_eq_zero_of_mem hQ π c σ hσ m hπ hτ hsig v hv h hh hp

theorem cpow_zb_succ_eq (i : Fin t) (r : ℕ) (h : r + 1 ≤ L i) (q : ℕ) :
    ((cpow (zb (L := L) i (r + 1) h) q).comp (inS i r h).toPath).comp (outS i r h).toPath =
      cpow (zb i (r + 1) h) (q + 1) := by
  rw [cpow_succ', Quiver.Path.comp_assoc]; rfl

theorem cpow_zb_zero_succ_eq (i : Fin t) (q : ℕ) :
    ((cpow (zb (L := L) i 0 (Nat.zero_le _)) q).comp (in0 i).toPath).comp (out0 i).toPath =
      cpow (zb i 0 (Nat.zero_le _)) (q + 1) := by
  rw [cpow_succ', Quiver.Path.comp_assoc]; rfl

include hπ hτ hsig hc hdeck hs hθ in
/-- **Outward backtracks on a fixed arm have zero trace**: rotating the first
arrow turns `y_r^q` into `z_{r+1}^q`, which the mesh at `r + 1` identifies with
`y_{r+1}^q`, or kills at the leaf. -/
theorem phiV_yb_zero {i : Fin t} (hi : θ i = i) : ∀ (n r : ℕ) (hr : r + 1 ≤ L i), L i - r = n →
    ∀ (h : ℤ) (hh : (h : ZMod 2) = (starTree L).par (av L i r (Nat.le_of_succ_le hr))) (q : ℕ),
      1 ≤ q → 2 * q = m + 1 →
      phiV hQ π c σ hσ m _ (fix_av σ θ hL hθ hi r _) h hh (cpow (yb i r hr) q) = 0
  | 0, r, hr, hn, _, _, _, _, _ => absurd hn (by omega)
  | n + 1, r, hr, hn, h, hh, q, hq, hqm => by
      obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      rw [cpow_yb_succ,
        phiV_rotate_fixed hQ π c σ hσ m s hσp hτ hc hdeck hs _ _ _ (fix_av σ θ hL hθ hi (r + 1) hr)
          h hh _ _ (by
            intro x hx
            simp only [Quiver.Path.vertices_toPath, List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · exact fix_av σ θ hL hθ hi r _
            · exact fix_av σ θ hL hθ hi (r + 1) hr)
          (by simp only [Quiver.Path.length_toPath, Quiver.Path.length_comp, length_cpow]
              simp only [zb, Quiver.Path.length_comp, Quiver.Path.length_toPath]; omega),
        cpow_zb_succ_eq]
      by_cases hleaf : r + 1 = L i
      · apply phiV_mem hQ π c σ hσ m hπ hτ hsig
        exact cpow_zb_mem k i 0 (r + 1) hr (by omega) (q + 1) (by omega) (by omega)
      · have hr' : r + 1 + 1 ≤ L i := by omega
        rw [phiV_congr hQ π c σ hσ m hπ hτ hsig _ _ _ _
          ((Submodule.neg_mem_iff _).1 (by
            rw [neg_sub]; exact cpow_sub_mem k (yb_sub_zb_mem k i (r + 1) hr') (q + 1)))]
        exact phiV_yb_zero hi n (r + 1) hr' (by omega) _ _ (q + 1) (by omega) hqm

include hπ hτ hsig hc hdeck hs hθ in
/-- **`[x_i^q] = 0` on an arm fixed by the twist** (`eq:arm-power-trace-zero`). -/
theorem wordTr_replicate {i : Fin t} (hi : θ i = i) (q : ℕ) (hq : 1 ≤ q) :
    wordTr hQ π c σ hσ m hσo (List.replicate q i) = 0 := by
  unfold wordTr
  split_ifs with hd
  · rw [List.length_replicate] at hd
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [wordP_replicate, cpow_xp_succ,
      phiV_rotate_fixed hQ π c σ hσ m s hσp hτ hc hdeck hs _ _ _ (fix_av σ θ hL hθ hi 0 (Nat.zero_le _))
        0 par_o _ _ (by
          intro x hx
          simp only [Quiver.Path.vertices_toPath, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact hσo
          · exact fix_av σ θ hL hθ hi 0 _)
        (by simp only [Quiver.Path.length_toPath, Quiver.Path.length_comp, length_cpow]
            simp only [zb, Quiver.Path.length_comp, Quiver.Path.length_toPath]; omega),
      cpow_zb_zero_succ_eq]
    by_cases hleaf : L i = 0
    · apply phiV_mem hQ π c σ hσ m hπ hτ hsig
      exact cpow_zb_mem k i 0 0 (Nat.zero_le _) (by omega) (q + 1) (by omega) (by omega)
    · have hr' : 0 + 1 ≤ L i := by omega
      rw [phiV_congr hQ π c σ hσ m hπ hτ hsig _ _ _ _
        ((Submodule.neg_mem_iff _).1 (by
          rw [neg_sub]; exact cpow_sub_mem k (yb_sub_zb_mem k i 0 hr') (q + 1)))]
      exact phiV_yb_zero hQ π c σ hσ m s hσp hπ hτ hsig hc hdeck hs θ hL hθ hi _ 0 hr' rfl _ _
        (q + 1) (by omega) (by omega)
  · rfl

end StarTrace

end MultiplicativeBasisDeformations
