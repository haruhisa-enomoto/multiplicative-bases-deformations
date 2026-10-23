module

public import MultiplicativeBasisDeformations.Foundations.StarTree
public import MultiplicativeBasisDeformations.Foundations.CoveringIdeals

/-!
# The centre corner of the preprojective category of a star (Lemma A.3)

`lem:star-return-reduction` (`periodic-mesh-calculations.tex`). For a
star rooted at its centre `o`, oriented away from `o`, let `x_i` be the closed
path of length two along arm `i`. The vertices of arm `i` are `v_0 = o, v_1, …`.
"For `j ≥ 2`, the mesh at `v_{j-1}` replaces the backtrack `v_{j-1} v_j v_{j-1}`
by `v_{j-1} v_{j-2} v_{j-1}`. … Iteration expresses every closed path at `o` as
a word in the `x_i`. The centre mesh gives `∑ x_i = 0`. Moving a power down its
arm gives `x_i^{L_i+1} = 0`."

We prove the iteration in the following form: every path from `o` to `v` is,
modulo the relations, a word in the `x_i` followed by the geodesic from `o` to
`v` (`normal_form`). (In `StarV L` the arm `i` has `L i + 1` vertices, so the
manuscript's `L_i` is `L i + 1`.)
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace StarCorner

variable {t : ℕ} (L : Fin t → ℕ)

instance : DecidableRel (starTree L).orient := inferInstanceAs (DecidableRel (starOrient (L := L)))

/-- The centre. -/
def o : (starTree L).Dbl := (starTree L).toDbl none

/-- The vertex `j` of arm `i`, at depth `j + 1`. -/
def av (i : Fin t) (j : ℕ) (h : j ≤ L i) : (starTree L).Dbl :=
  (starTree L).toDbl (some ⟨i, ⟨j, Nat.lt_succ_of_le h⟩⟩)

variable {L}

def out0 (i : Fin t) : o L ⟶ av L i 0 (Nat.zero_le _) :=
  ⟨by simp [starTree, starGraph, starAdj, o, av, OrientedTree.toDbl]⟩
def in0 (i : Fin t) : av L i 0 (Nat.zero_le _) ⟶ o L :=
  ⟨by simp [starTree, starGraph, starAdj, o, av, OrientedTree.toDbl]⟩
def outS (i : Fin t) (j : ℕ) (h : j + 1 ≤ L i) : av L i j (by omega) ⟶ av L i (j + 1) h :=
  ⟨by simp [starTree, starGraph, starAdj, o, av, OrientedTree.toDbl]⟩
def inS (i : Fin t) (j : ℕ) (h : j + 1 ≤ L i) : av L i (j + 1) h ⟶ av L i j (by omega) :=
  ⟨by simp [starTree, starGraph, starAdj, o, av, OrientedTree.toDbl]⟩

/-- The closed path `x_i` of length two along arm `i`. -/
def xp (i : Fin t) : Quiver.Path (o L) (o L) := (out0 i).toPath.comp (in0 i).toPath

/-- The path of a word in the `x_i`. -/
def wordP : List (Fin t) → Quiver.Path (o L) (o L)
  | [] => Quiver.Path.nil
  | i :: w => (xp i).comp (wordP w)

theorem wordP_append (w w' : List (Fin t)) :
    wordP (L := L) (w ++ w') = (wordP w).comp (wordP w') := by
  induction w with
  | nil => simp [wordP]
  | cons i w ih => simp [wordP, ih, Quiver.Path.comp_assoc]

theorem length_wordP (w : List (Fin t)) : (wordP (L := L) w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [wordP, ih, xp]; ring

/-- The geodesic from the centre to the vertex `j` of arm `i`. -/
def geodA (i : Fin t) : ∀ (j : ℕ) (h : j ≤ L i), Quiver.Path (o L) (av L i j h)
  | 0, _ => (out0 i).toPath
  | j + 1, h => (geodA i j (by omega)).cons (outS i j h)

/-- The geodesic from the centre. -/
def geod : ∀ v : (starTree L).Dbl, Quiver.Path (o L) v
  | none => Quiver.Path.nil
  | some ⟨i, ⟨j, hj⟩⟩ => geodA i j (by omega)

theorem length_geodA (i : Fin t) : ∀ (j : ℕ) (h : j ≤ L i), (geodA i j h).length = j + 1
  | 0, _ => rfl
  | j + 1, h => by rw [geodA, Quiver.Path.length_cons, length_geodA i j]

theorem length_geod : ∀ v : (starTree L).Dbl, (geod v).length = starDepth (L := L) v
  | none => rfl
  | some ⟨i, ⟨j, hj⟩⟩ => length_geodA i j _

/-- The outward backtrack at the vertex `j` of arm `i`. -/
def yb (i : Fin t) (j : ℕ) (h : j + 1 ≤ L i) : Quiver.Path (av L i j (by omega)) (av L i j (by omega)) :=
  (outS i j h).toPath.comp (inS i j h).toPath

/-- The inward backtrack at the vertex `j` of arm `i`. -/
def zb (i : Fin t) : ∀ (j : ℕ) (h : j ≤ L i), Quiver.Path (av L i j h) (av L i j h)
  | 0, _ => (in0 i).toPath.comp (out0 i).toPath
  | j + 1, h => (inS i j h).toPath.comp (outS i j h).toPath

/-- The edge from the vertex `j` of arm `i` towards the centre. -/
def pe (i : Fin t) : ∀ (j : ℕ) (h : j ≤ L i), Σ y : (starTree L).Dbl, av L i j h ⟶ y
  | 0, _ => ⟨o L, in0 i⟩
  | j + 1, h => ⟨av L i j (by omega), inS i j h⟩

theorem sigma_ext' {x : (starTree L).Dbl} (e e' : Σ y : (starTree L).Dbl, x ⟶ y)
    (h : e.1 = e'.1) : e = e' := by
  obtain ⟨y, a⟩ := e
  obtain ⟨y', a'⟩ := e'
  simp only at h
  subst h
  rw [Subsingleton.elim a a']

/-- The neighbours of an arm vertex: towards the centre, or one step out. -/
theorem nbr_arm (i : Fin t) (j : ℕ) (h : j ≤ L i) (e : Σ y : (starTree L).Dbl, av L i j h ⟶ y) :
    e = pe i j h ∨ ∃ h' : j + 1 ≤ L i, e = ⟨_, outS i j h'⟩ := by
  obtain ⟨y, a⟩ := e
  have ha := a.down
  rcases y with _ | ⟨i', ⟨j', hj'⟩⟩
  · left
    change starAdj (some ⟨i, ⟨j, _⟩⟩) none at ha
    simp only [starAdj] at ha
    subst ha
    exact sigma_ext' _ _ rfl
  · change starAdj (some ⟨i, ⟨j, _⟩⟩) (some ⟨i', ⟨j', hj'⟩⟩) at ha
    simp only [starAdj] at ha
    obtain ⟨rfl, hj | hj⟩ := ha
    · right
      subst hj
      exact ⟨by omega, sigma_ext' _ _ rfl⟩
    · left
      subst hj
      exact sigma_ext' _ _ rfl

/-- The neighbours of the centre: one per arm. -/
theorem nbr_centre (e : Σ y : (starTree L).Dbl, o L ⟶ y) : ∃ i, e = ⟨_, out0 i⟩ := by
  obtain ⟨y, a⟩ := e
  have ha := a.down
  rcases y with _ | ⟨i, ⟨j, hj⟩⟩
  · exact (ha : False).elim
  · change starAdj none (some ⟨i, ⟨j, hj⟩⟩) at ha
    simp only [starAdj] at ha
    subst ha
    exact ⟨i, sigma_ext' _ _ rfl⟩

variable (k : Type u) [CommRing k]

theorem path_back {a b : (starTree L).Dbl} (e : a ⟶ b) (f g : b ⟶ a) :
    LinearPaths.path (k := k) (e.toPath.comp f.toPath) = LinearPaths.path (e.toPath.comp g.toPath) := by
  rw [Subsingleton.elim f g]

/-- The summand of the relation at `x` for the edge `e`. -/
abbrev term {x : (starTree L).Dbl} (e : Σ y : (starTree L).Dbl, x ⟶ y) :
    LinearPaths.obj (k := k) x ⟶ LinearPaths.obj x :=
  (((starTree L).sgn k (x : StarV L) (e.1 : StarV L) : kˣ) : k) •
    LinearPaths.path (e.2.toPath.comp (Quiver.Hom.toPath (show e.1 ⟶ x from ⟨e.2.down.symm⟩)))

theorem preprojRel_eq (x : (starTree L).Dbl) :
    (starTree L).preprojRel k x = ∑ e : Σ y : (starTree L).Dbl, x ⟶ y, term k e := rfl

theorem term_out (i : Fin t) (j : ℕ) (h : j + 1 ≤ L i) :
    term k (⟨_, outS i j h⟩ : Σ y : (starTree L).Dbl, av L i j (by omega) ⟶ y) =
      LinearPaths.path (yb i j h) := by
  have hs : (starTree L).sgn k (av L i j (by omega) : StarV L) (av L i (j + 1) h) = 1 := by
    unfold OrientedTree.sgn
    rw [if_pos]
    exact ⟨(outS i j h).down, by simp [starDepth, av, OrientedTree.toDbl]⟩
  rw [term, hs, Units.val_one, one_smul, yb]
  exact path_back k _ _ _

theorem term_pe (i : Fin t) (j : ℕ) (h : j ≤ L i) :
    term k (pe i j h) = -LinearPaths.path (zb i j h) := by
  have hs : (starTree L).sgn k (av L i j h : StarV L) ((pe i j h).1 : StarV L) = -1 := by
    unfold OrientedTree.sgn
    rw [if_neg]
    rintro ⟨-, hd⟩
    rcases j with _ | j <;> simp [pe, starDepth, av, o, OrientedTree.toDbl] at hd
  rw [term, hs, Units.val_neg, Units.val_one, neg_one_smul]
  rcases j with _ | j
  · rw [zb]; exact congrArg Neg.neg (path_back k _ _ _)
  · rw [zb]; exact congrArg Neg.neg (path_back k _ _ _)

theorem term_out0 (i : Fin t) :
    term k (⟨_, out0 i⟩ : Σ y : (starTree L).Dbl, o L ⟶ y) = LinearPaths.path (xp i) := by
  have hs : (starTree L).sgn k (o L : StarV L) (av L i 0 (Nat.zero_le _)) = 1 := by
    unfold OrientedTree.sgn
    rw [if_pos]
    exact ⟨(out0 i).down, by simp [starDepth, av, o, OrientedTree.toDbl]⟩
  rw [term, hs, Units.val_one, one_smul, xp]
  exact path_back k _ _ _

/-- The centre relation `∑ x_i`. -/
theorem preprojRel_centre :
    (starTree L).preprojRel k (o L) = ∑ i, LinearPaths.path (xp (L := L) i) := by
  rw [preprojRel_eq]
  symm
  refine Fintype.sum_bijective (fun i ↦ (⟨_, out0 i⟩ : Σ y : (starTree L).Dbl, o L ⟶ y))
    ⟨fun i i' hii ↦ ?_, fun e ↦ ?_⟩ _ _ fun i ↦ (term_out0 k i).symm
  · have := congrArg Sigma.fst hii
    exact (Sigma.mk.inj_iff.1 (Option.some.inj this)).1
  · obtain ⟨i, rfl⟩ := nbr_centre e
    exact ⟨i, rfl⟩

/-- The relation at an arm vertex with a successor: `y_j - z_j`. -/
theorem preprojRel_arm (i : Fin t) (j : ℕ) (h : j + 1 ≤ L i) :
    (starTree L).preprojRel k (av L i j (Nat.le_of_succ_le h)) =
      LinearPaths.path (yb i j h) - LinearPaths.path (zb i j (Nat.le_of_succ_le h)) := by
  classical
  rw [preprojRel_eq, Fintype.sum_eq_add (⟨_, outS i j h⟩) (pe i j (by omega)), term_out,
    term_pe, sub_eq_add_neg]
  · intro hab
    have := congrArg (fun e ↦ starDepth (L := L) (e.1 : StarV L)) hab
    rcases j with _ | j <;> simp [pe, starDepth, av, o, OrientedTree.toDbl] at this <;> omega
  · rintro e ⟨h1, h2⟩
    rcases nbr_arm i j (by omega) e with he | ⟨h', he⟩
    · exact absurd he h2
    · exact absurd he h1

/-- The relation at the leaf of an arm: `-z`. -/
theorem preprojRel_leaf (i : Fin t) :
    (starTree L).preprojRel k (av L i (L i) le_rfl) = -LinearPaths.path (zb i (L i) le_rfl) := by
  classical
  rw [preprojRel_eq, Fintype.sum_eq_single (pe i (L i) le_rfl), term_pe]
  intro e he
  rcases nbr_arm i (L i) le_rfl e with he' | ⟨h', -⟩
  · exact absurd he' he
  · omega

/-! ### The normal form -/

/-- The ideal of `Π(Δ)` on the star. -/
abbrev I (x y : (starTree L).Dbl) :=
  ((starTree L).preproj k).ideal (LinearPaths.obj (k := k) x) (LinearPaths.obj y)

theorem rel_mem (x : (starTree L).Dbl) : (starTree L).preprojRel k x ∈ I k x x := by
  have := ((starTree L).preproj k).comp_rel_comp_mem (X := x) (Y := x) x (𝟙 _) (𝟙 _)
  simp only [Category.id_comp, Category.comp_id] at this
  exact this

/-- `x_i` lies in the arm `i`; the mesh at an arm vertex with a successor
identifies its two backtracks. -/
theorem yb_sub_zb_mem (i : Fin t) (j : ℕ) (h : j + 1 ≤ L i) :
    LinearPaths.path (yb i j h) - LinearPaths.path (zb i j (Nat.le_of_succ_le h)) ∈
      I k (av L i j (Nat.le_of_succ_le h)) (av L i j (Nat.le_of_succ_le h)) := by
  rw [← preprojRel_arm]; exact rel_mem k _

theorem zb_leaf_mem (i : Fin t) :
    LinearPaths.path (zb i (L i) le_rfl) ∈ I k (av L i (L i) le_rfl) (av L i (L i) le_rfl) := by
  have := Submodule.neg_mem _ (rel_mem k (av L i (L i) le_rfl))
  rwa [preprojRel_leaf, neg_neg] at this

theorem sum_xp_mem : ∑ i, LinearPaths.path (k := k) (xp (L := L) i) ∈ I k (o L) (o L) := by
  rw [← preprojRel_centre]; exact rel_mem k _

theorem sub_comp_mem {x y z : (starTree L).Dbl} {f g : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y}
    (h : f - g ∈ I k x y) (q : LinearPaths.obj (k := k) y ⟶ LinearPaths.obj z) :
    f ≫ q - g ≫ q ∈ I k x z := by
  rw [← Preadditive.sub_comp]; exact ((starTree L).preproj k).mem_ideal_comp h q

theorem comp_sub_mem {x y z : (starTree L).Dbl} {f g : LinearPaths.obj (k := k) y ⟶ LinearPaths.obj z}
    (q : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) (h : f - g ∈ I k y z) :
    q ≫ f - q ≫ g ∈ I k x z := by
  rw [← Preadditive.comp_sub]; exact ((starTree L).preproj k).comp_mem_ideal q h

/-- **Claim**: `γ_j y_j ≡ x_i γ_j`, where `γ_j` is the geodesic to the vertex `j`
of arm `i`. -/
theorem geod_yb (i : Fin t) : ∀ (j : ℕ) (h : j + 1 ≤ L i),
    LinearPaths.path ((geodA i j (Nat.le_of_succ_le h)).comp (yb i j h)) -
      LinearPaths.path ((xp i).comp (geodA i j (Nat.le_of_succ_le h))) ∈
        I k (o L) (av L i j (Nat.le_of_succ_le h))
  | 0, h => by
      have h1 := comp_sub_mem k (LinearPaths.path (geodA i 0 (Nat.zero_le _)))
        (yb_sub_zb_mem k i 0 h)
      rw [LinearPaths.path_comp_path, LinearPaths.path_comp_path] at h1
      have e : (geodA (L := L) i 0 (Nat.zero_le _)).comp (zb i 0 (Nat.zero_le _)) =
          (xp i).comp (geodA (L := L) i 0 (Nat.zero_le _)) := by
        simp only [geodA, zb, xp, Quiver.Path.comp_assoc]
      rw [e] at h1
      exact h1
  | j + 1, h => by
      have h1 := comp_sub_mem k (LinearPaths.path (geodA i (j + 1) (Nat.le_of_succ_le h)))
        (yb_sub_zb_mem k i (j + 1) h)
      have h2 := sub_comp_mem k (geod_yb i j (by omega)) (LinearPaths.arrow (outS i j (by omega)))
      have h3 := add_mem h1 h2
      rw [sub_add_sub_comm] at h3
      simp only [LinearPaths.arrow, LinearPaths.path_comp_path] at h3
      convert h3 using 1
      have e1 : (geodA i (j + 1) (Nat.le_of_succ_le h)).comp (zb i (j + 1) (Nat.le_of_succ_le h)) =
          ((geodA i j (by omega)).comp (yb i j (by omega))).comp (outS i j (by omega)).toPath := by
        simp only [geodA, zb, yb, Quiver.Path.comp_assoc]; rfl
      have e2 : (xp i).comp (geodA i (j + 1) (Nat.le_of_succ_le h)) =
          ((xp i).comp (geodA i j (by omega))).comp (outS i j (by omega)).toPath := by
        simp only [geodA, Quiver.Path.comp_assoc]; rfl
      rw [e1, e2]
      abel

/-- **Lemma A.3, iteration**: every path from the centre is a word in the `x_i`
followed by a geodesic, modulo the relations. -/
theorem normal_form {b : (starTree L).Dbl} (p : Quiver.Path (o L) b) :
    ∃ w : List (Fin t), LinearPaths.path p - LinearPaths.path ((wordP w).comp (geod b)) ∈
      I k (o L) b ∧ p.length = 2 * w.length + starDepth (L := L) b := by
  induction p with
  | nil => exact ⟨[], by simp [wordP, geod, o, OrientedTree.toDbl], rfl⟩
  | @cons b c p e ih =>
      obtain ⟨w, hw, hl⟩ := ih
      have h := sub_comp_mem k hw (LinearPaths.arrow e)
      simp only [LinearPaths.arrow, LinearPaths.path_comp_path] at h
      have ha := e.down
      rcases b with _ | ⟨i, ⟨j, hj⟩⟩ <;> rcases c with _ | ⟨i', ⟨j', hj'⟩⟩
      · exact (ha : False).elim
      · change starAdj none (some ⟨i', ⟨j', hj'⟩⟩) at ha
        simp only [starAdj] at ha
        subst ha
        refine ⟨w, ?_, ?_⟩
        · have e1 : (wordP w).comp (geod (some ⟨i', ⟨0, hj'⟩⟩)) =
              ((wordP w).comp (geod (o L))).comp e.toPath := by
            rw [Subsingleton.elim e (out0 (L := L) i')]; rfl
          rw [e1]; exact h
        · simp only [Quiver.Path.length_cons, hl, starDepth]
      · change starAdj (some ⟨i, ⟨j, hj⟩⟩) none at ha
        simp only [starAdj] at ha
        subst ha
        refine ⟨w ++ [i], ?_, ?_⟩
        · have e1 : (wordP (w ++ [i])).comp (geod (o L)) =
              ((wordP w).comp (geod (some ⟨i, ⟨0, hj⟩⟩))).comp e.toPath := by
            rw [wordP_append, Subsingleton.elim e (in0 (L := L) i)]
            simp only [wordP, xp, Quiver.Path.comp_nil]
            rfl
          exact e1 ▸ h
        · simp only [Quiver.Path.length_cons, hl, starDepth, List.length_append,
            List.length_singleton]
          omega
      · change starAdj (some ⟨i, ⟨j, hj⟩⟩) (some ⟨i', ⟨j', hj'⟩⟩) at ha
        simp only [starAdj] at ha
        obtain ⟨rfl, hj2 | hj2⟩ := ha
        · subst hj2
          refine ⟨w, ?_, ?_⟩
          · have e1 : (wordP w).comp (geod (some ⟨i, ⟨j + 1, hj'⟩⟩)) =
                ((wordP w).comp (geod (some ⟨i, ⟨j, hj⟩⟩))).comp e.toPath := by
              rw [Subsingleton.elim e (outS (L := L) i j (by omega))]; rfl
            rw [e1]; exact h
          · simp only [Quiver.Path.length_cons, hl, starDepth]; omega
        · subst hj2
          refine ⟨w ++ [i], ?_, ?_⟩
          · have h2 := comp_sub_mem k (LinearPaths.path (wordP (L := L) w))
              (geod_yb k i j' (by omega))
            simp only [LinearPaths.path_comp_path] at h2
            have e1 : ((wordP w).comp (geod (some ⟨i, ⟨j' + 1, hj⟩⟩))).comp e.toPath =
                (wordP (L := L) w).comp ((geodA i j' (by omega)).comp (yb i j' (by omega))) := by
              rw [Subsingleton.elim e (inS (L := L) i j' (by omega))]
              rfl
            have e2 : (wordP (L := L) (w ++ [i])).comp (geod (some ⟨i, ⟨j', hj'⟩⟩)) =
                (wordP (L := L) w).comp ((xp i).comp (geodA i j' (by omega))) := by
              rw [wordP_append]
              simp only [wordP, Quiver.Path.comp_nil, Quiver.Path.comp_assoc]
              rfl
            rw [e1] at h
            have h3 := add_mem h h2
            rw [sub_add_sub_cancel] at h3
            rw [e2]; exact h3
          · simp only [Quiver.Path.length_cons, hl, starDepth, List.length_append,
              List.length_singleton]
            omega

/-! ### Powers -/

/-- Powers of a closed path. -/
def cpow {a : (starTree L).Dbl} (p : Quiver.Path a a) : ℕ → Quiver.Path a a
  | 0 => Quiver.Path.nil
  | n + 1 => p.comp (cpow p n)

theorem cpow_succ' {a : (starTree L).Dbl} (p : Quiver.Path a a) (n : ℕ) :
    cpow p (n + 1) = (cpow p n).comp p := by
  induction n with
  | zero => simp [cpow]
  | succ n ih =>
      show p.comp (cpow p (n + 1)) = (cpow p (n + 1)).comp p
      conv_lhs => rw [ih]
      rw [← Quiver.Path.comp_assoc]; rfl

theorem length_cpow {a : (starTree L).Dbl} (p : Quiver.Path a a) (n : ℕ) :
    (cpow p n).length = n * p.length := by
  induction n with
  | zero => simp [cpow]
  | succ n ih => rw [cpow, Quiver.Path.length_comp, ih]; ring

theorem wordP_replicate (i : Fin t) (n : ℕ) :
    wordP (L := L) (List.replicate n i) = cpow (xp i) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, wordP, ih]; rfl

theorem cpow_sub_mem {a : (starTree L).Dbl} {p p' : Quiver.Path a a}
    (h : LinearPaths.path p - LinearPaths.path p' ∈ I k a a) (n : ℕ) :
    LinearPaths.path (cpow p n) - LinearPaths.path (cpow p' n) ∈ I k a a := by
  induction n with
  | zero => simp [cpow]
  | succ n ih =>
      have h1 := sub_comp_mem k h (LinearPaths.path (cpow p n))
      have h2 := comp_sub_mem k (LinearPaths.path p') ih
      have := add_mem h1 h2
      rw [sub_add_sub_cancel] at this
      simpa only [cpow, LinearPaths.path_comp_path] using this

theorem cpow_xp_succ (i : Fin t) (q : ℕ) :
    cpow (xp (L := L) i) (q + 1) = (out0 i).toPath.comp ((cpow (zb i 0 (Nat.zero_le _)) q).comp
      (in0 i).toPath) := by
  induction q with
  | zero => simp [cpow, xp]
  | succ q ih =>
      rw [cpow, ih, cpow]
      simp only [xp, zb, Quiver.Path.comp_assoc]

theorem cpow_yb_succ (i : Fin t) (r : ℕ) (h : r + 1 ≤ L i) (q : ℕ) :
    cpow (yb (L := L) i r h) (q + 1) = (outS i r h).toPath.comp
      ((cpow (zb i (r + 1) h) q).comp (inS i r h).toPath) := by
  induction q with
  | zero => simp [cpow, yb]
  | succ q ih =>
      rw [cpow, ih, cpow]
      simp only [yb, zb, Quiver.Path.comp_assoc]

/-- Inward backtracks die when pushed to the leaf: `z_r^q = 0` for
`q ≥ L i + 1 - r`, `q ≥ 1`. -/
theorem cpow_zb_mem (i : Fin t) : ∀ (n r : ℕ) (hr : r ≤ L i), L i - r = n → ∀ q, 1 ≤ q →
    L i + 1 - r ≤ q → LinearPaths.path (cpow (zb (L := L) i r hr) q) ∈ I k _ _
  | 0, r, hr, hn, q, hq, _ => by
      obtain rfl : r = L i := by omega
      obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      rw [cpow, ← LinearPaths.path_comp_path]
      exact ((starTree L).preproj k).mem_ideal_comp (zb_leaf_mem k i) _
  | n + 1, r, hr, hn, q, hq, hq' => by
      have hr' : r + 1 ≤ L i := by omega
      have h1 := cpow_sub_mem k (yb_sub_zb_mem k i r hr') q
      obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have h2 := cpow_zb_mem i n (r + 1) hr' (by omega) q (by omega) (by omega)
      have h3 : LinearPaths.path (cpow (yb (L := L) i r hr') (q + 1)) ∈ I k _ _ := by
        rw [cpow_yb_succ, ← LinearPaths.path_comp_path, ← LinearPaths.path_comp_path]
        exact ((starTree L).preproj k).comp_mem_ideal _
          (((starTree L).preproj k).mem_ideal_comp h2 _)
      have := Submodule.sub_mem _ h3 h1
      rwa [sub_sub_cancel] at this

/-- **`x_i^{L_i+1} = 0`** (in the manuscript's indexing; arm `i` has `L i + 1`
vertices): moving a power down its arm. -/
theorem xp_pow_mem (i : Fin t) :
    LinearPaths.path (wordP (L := L) (List.replicate (L i + 2) i)) ∈ I k (o L) (o L) := by
  rw [wordP_replicate, cpow_xp_succ, ← LinearPaths.path_comp_path, ← LinearPaths.path_comp_path]
  exact ((starTree L).preproj k).comp_mem_ideal _
    (((starTree L).preproj k).mem_ideal_comp
      (cpow_zb_mem k i (L i) 0 (Nat.zero_le _) (by omega) (L i + 1) (by omega) (by omega)) _)

/-! ### Paths in an arm beyond a vertex -/

/-- The geodesic out along arm `i` from its vertex `r`. -/
def geodR (i : Fin t) (r : ℕ) : ∀ (n : ℕ) (h : r + n ≤ L i),
    Quiver.Path (av L i r (by omega)) (av L i (r + n) h)
  | 0, _ => Quiver.Path.nil
  | n + 1, h => (geodR i r n (by omega)).cons (outS i (r + n) h)

theorem length_geodR (i : Fin t) (r : ℕ) : ∀ (n : ℕ) (h : r + n ≤ L i),
    (geodR (L := L) i r n h).length = n
  | 0, _ => rfl
  | n + 1, h => by rw [geodR, Quiver.Path.length_cons, length_geodR i r n]

/-- `γ y_{r+n} ≡ y_r γ` along the arm beyond `r`. -/
theorem geodR_yb (i : Fin t) (r : ℕ) (hr : r + 1 ≤ L i) : ∀ (n : ℕ) (h : r + n + 1 ≤ L i),
    LinearPaths.path ((geodR i r n (by omega)).comp (yb i (r + n) h)) -
      LinearPaths.path ((yb (L := L) i r hr).comp (geodR i r n (by omega))) ∈
        I k (av L i r (by omega)) (av L i (r + n) (by omega))
  | 0, h => by simp [geodR]
  | n + 1, h => by
      have h1 := comp_sub_mem k (LinearPaths.path (geodR (L := L) i r (n + 1) (by omega)))
        (yb_sub_zb_mem k i (r + (n + 1)) h)
      have h2 := sub_comp_mem k (geodR_yb i r hr n (by omega))
        (LinearPaths.arrow (outS i (r + n) (by omega)))
      have h3 := add_mem h1 h2
      rw [sub_add_sub_comm] at h3
      simp only [LinearPaths.arrow, LinearPaths.path_comp_path] at h3
      convert h3 using 1
      have e1 : (geodR (L := L) i r (n + 1) (by omega)).comp (zb i (r + (n + 1)) (by omega)) =
          ((geodR i r n (by omega)).comp (yb i (r + n) (by omega))).comp
            (outS i (r + n) (by omega)).toPath := by
        simp only [geodR, zb, yb, Quiver.Path.comp_assoc]; rfl
      have e2 : (yb (L := L) i r hr).comp (geodR i r (n + 1) (by omega)) =
          ((yb i r hr).comp (geodR i r n (by omega))).comp (outS i (r + n) (by omega)).toPath := by
        simp only [geodR, Quiver.Path.comp_assoc]; rfl
      rw [e1, e2]
      abel

/-- **Normal form beyond an arm vertex**: a path from the vertex `r` of arm `i`
that stays in the arm beyond `r` is a power of the outward backtrack `y_r`
followed by a geodesic. -/
theorem arm_normal_form (i : Fin t) (r : ℕ) (hr : r + 1 ≤ L i) {b : (starTree L).Dbl}
    (p : Quiver.Path (av L i r (Nat.le_of_succ_le hr)) b)
    (hp : ∀ v ∈ p.vertices, ∃ (n : ℕ) (h : r + n ≤ L i), v = av L i (r + n) h) :
    ∃ (q n : ℕ) (h : r + n ≤ L i) (hb : av L i (r + n) h = b),
      LinearPaths.path p - LinearPaths.path ((cpow (yb i r hr) q).comp
        ((geodR i r n h).cast rfl hb)) ∈ I k _ b ∧ p.length = 2 * q + n := by
  induction p with
  | nil => exact ⟨0, 0, by omega, rfl, by simp [cpow, geodR], rfl⟩
  | @cons b c p e ih =>
      obtain ⟨q, n, h, hb, hmem, hl⟩ := ih fun v hv ↦ hp v (by
        rw [Quiver.Path.mem_vertices_cons]; exact Or.inl hv)
      subst hb
      obtain ⟨n', h', rfl⟩ := hp c (Quiver.Path.end_mem_vertices _)
      have hm := sub_comp_mem k hmem (LinearPaths.arrow e)
      simp only [LinearPaths.arrow, LinearPaths.path_comp_path, Quiver.Path.cast_rfl_rfl] at hm
      have ha := e.down
      change starAdj (some ⟨i, ⟨r + n, _⟩⟩) (some ⟨i, ⟨r + n', _⟩⟩) at ha
      simp only [starAdj, true_and] at ha
      rcases ha with hn | hn
      · obtain rfl : n' = n + 1 := by omega
        refine ⟨q, n + 1, h', rfl, ?_, by rw [Quiver.Path.length_cons, hl]; ring⟩
        rw [Quiver.Path.cast_rfl_rfl]
        have e1 : (cpow (yb (L := L) i r hr) q).comp (geodR i r (n + 1) h') =
            ((cpow (yb i r hr) q).comp (geodR i r n h)).comp e.toPath := by
          rw [Subsingleton.elim e (outS (L := L) i (r + n) h')]; rfl
        rw [e1]; exact hm
      · obtain rfl : n = n' + 1 := by omega
        refine ⟨q + 1, n', h', rfl, ?_, by rw [Quiver.Path.length_cons, hl]; ring⟩
        rw [Quiver.Path.cast_rfl_rfl]
        have h2 := comp_sub_mem k (LinearPaths.path (cpow (yb (L := L) i r hr) q))
          (geodR_yb k i r hr n' (by omega))
        simp only [LinearPaths.path_comp_path] at h2
        have e1 : ((cpow (yb (L := L) i r hr) q).comp (geodR i r (n' + 1) h)).comp e.toPath =
            (cpow (yb i r hr) q).comp ((geodR i r n' h').comp (yb i (r + n') (by omega))) := by
          rw [Subsingleton.elim e (inS (L := L) i (r + n') h)]
          rfl
        have e2 : (cpow (yb (L := L) i r hr) (q + 1)).comp (geodR i r n' h') =
            (cpow (yb i r hr) q).comp ((yb i r hr).comp (geodR i r n' h')) := by
          rw [cpow_succ', Quiver.Path.comp_assoc]
        rw [e1] at hm
        have h3 := add_mem hm h2
        rw [sub_add_sub_cancel] at h3
        rw [e2]; exact h3

end StarCorner

end MultiplicativeBasisDeformations
