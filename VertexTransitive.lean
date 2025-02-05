import Mathlib

structure GraphAutomorphism (G : SimpleGraph V) :=
  (bijective_map : V ≃ V)
  (preserves_adj : ∀ u v, G.Adj u v ↔ G.Adj (bijective_map u) (bijective_map v))

def iso_from_auto {G: SimpleGraph V} (f : GraphAutomorphism G) : (G ≃g G) :=
  { toFun := f.bijective_map,
    invFun := f.bijective_map.symm,
    left_inv := f.bijective_map.3,
    right_inv := f.bijective_map.4,
    map_rel_iff' :=  λ {u v} => (f.preserves_adj u v).symm
  }

def inv_graph_automorphism (f : GraphAutomorphism G) : GraphAutomorphism G :=
{ bijective_map := f.bijective_map.symm,
  preserves_adj := by
      intro u v
      nth_rewrite 1 [←f.bijective_map.apply_symm_apply u]
      nth_rewrite 1 [←f.bijective_map.apply_symm_apply v]
      apply Iff.symm
      apply f.preserves_adj (f.bijective_map.symm u) (f.bijective_map.symm v)}

def isVertexTransitive (G : SimpleGraph V) :=
  ∀ u v, ∃ f : GraphAutomorphism G, f.1 u = v

--  As an example, let's prove that cliques are vertex transitive!
def Clique (n : Nat) : SimpleGraph (ZMod n) :=
  { Adj := fun u v => u ≠ v,
    symm := by intros u v h; exact Ne.symm h,
    loopless := by intro u; simp
  }

lemma clique_vertex_transitive (n : Nat) : isVertexTransitive (Clique n) := by
  unfold isVertexTransitive
  intro u v
  let f : ZMod n → ZMod n := fun x => x + (v - u)
  let f_inv : ZMod n → ZMod n := fun x => x - (v - u)

  have left_inverse: ∀ x, f_inv (f x) = x := by intro x; unfold f f_inv; ring

  have right_inverse: ∀ x, f (f_inv x) = x := by intro x; unfold f f_inv; ring

  let g: ZMod n ≃ ZMod n := ⟨f, f_inv, left_inverse, right_inverse⟩
  let f_auto : GraphAutomorphism (Clique n) := ⟨g, by intro x y; unfold Clique; simp⟩

  have h : f u = v := by
    unfold f; ring
  exact ⟨f_auto, h⟩

lemma auto_walk_iff (G: SimpleGraph V)
                    [Fintype V] [DecidableRel G.Adj]
                    (f : GraphAutomorphism G) (u v : V)
                    {d : Nat} (wh: ∃ (w : G.Walk u v), w.length = d) :
      ∃ (w' : G.Walk (f.1 u) (f.1 v)), w'.length = d := by
      let isoF : G ≃g G := iso_from_auto f
      let homoF : G →g G := isoF

      obtain ⟨w, hw⟩ := wh
      let map : G.Walk u v -> G.Walk (isoF u) (isoF v) := SimpleGraph.Walk.map homoF
      have map_length : (map w).length = w.length := by aesop
      use map w
      linarith

theorem auto_le_distance (G : SimpleGraph V) (hconn: G.Connected) [Fintype V] [DecidableRel G.Adj] (f : GraphAutomorphism G) (u v : V) :
  G.dist (f.1 u) (f.1 v) ≤ G.dist u v:= by
    let d := G.dist u v
    have h: ∃ w : G.Walk (f.1 u) (f.1 v), w.length = d := by
      apply auto_walk_iff
      apply SimpleGraph.Connected.exists_walk_length_eq_dist hconn

    have ⟨w, hw⟩ := h
    have s := SimpleGraph.dist_le w
    rw [hw] at s
    simp_all only [d]

theorem auto_preserve_distance (G: SimpleGraph V) (hconn: G.Connected) [Fintype V] [DecidableRel G.Adj] (f : GraphAutomorphism G) (u v : V) :
  G.dist u v = G.dist (f.1 u) (f.1 v) := by
  rw [Nat.eq_iff_le_and_ge]
  apply And.intro
  . nth_rewrite 1 [←f.bijective_map.symm_apply_apply u]
    nth_rewrite 1 [←f.bijective_map.symm_apply_apply v]
    let f_inv : GraphAutomorphism G := inv_graph_automorphism f
    apply auto_le_distance G hconn f_inv
  . apply auto_le_distance G hconn f


noncomputable def sum_dist (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (v : V) : Nat :=
  ∑ u : V, (G.dist u v)

noncomputable def average_dist_graph_from_vertex (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (v : V) : ℚ :=
  sum_dist G v / (Fintype.card V - 1)

noncomputable def average_dist_graph' (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : ℚ :=
  (∑ v : V, average_dist_graph_from_vertex G v) / Fintype.card V

noncomputable def average_dist_graph (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : ℚ :=
  (∑  u : V, ∑  v : V, G.dist u v) / (Fintype.card V *(Fintype.card V-1))

lemma avg_dist_equiv (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
  average_dist_graph' G = average_dist_graph G := by
    unfold average_dist_graph' average_dist_graph
    push_cast

    have h:  (∑ x : V, ∑ x_1 : V, (G.dist x x_1)) / (@Nat.cast ℚ Rat.instNatCast (Fintype.card V) * (@Nat.cast ℚ Rat.instNatCast  (Fintype.card V) - 1))
        = ((∑ x : V, ∑ x_1 : V, ↑(G.dist x x_1)) / (@Nat.cast ℚ Rat.instNatCast (Fintype.card V) - 1)) / ↑(Fintype.card V) :=
          by
          field_simp
          ring_nf
    push_cast at h; rw [h]
    have ah: (∑ v : V, average_dist_graph_from_vertex G v) =(∑ x : V, ∑ x_1 : V, ↑(G.dist x x_1)) / (↑(Fintype.card V) - 1) := by
      unfold average_dist_graph_from_vertex sum_dist
      simp [SimpleGraph.dist_comm]
      exact Eq.symm (Finset.sum_div Finset.univ (fun i ↦ ∑ x_1 : V,  @Nat.cast ℚ Rat.instNatCast (G.dist i x_1)) (↑(Fintype.card V) - 1))
    rw [ah]

theorem vertex_transitive_average_dist_from_vertex (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (hconn: G.Connected) (h: isVertexTransitive G) (u v : V) :
  average_dist_graph_from_vertex G u = average_dist_graph_from_vertex G v := by
  unfold average_dist_graph_from_vertex
  have neq : sum_dist G u = sum_dist G v := by
    unfold sum_dist; unfold isVertexTransitive at h
    obtain ⟨f, hf⟩ := h u v
    rw [←hf]
    have lpre  : ∀ u_1 : V, SimpleGraph.dist G u_1 u = SimpleGraph.dist G (f.1 u_1) (f.1 u) := by
      intro u_1
      apply auto_preserve_distance
      exact hconn
    simp [lpre]
    let b : V → Nat := λ x => G.dist x (f.bijective_map u)
    apply Equiv.sum_comp f.bijective_map b
  rw [neq]


theorem constant_sum [Fintype V] (f: V → ℚ) (eq_h : ∀ u v : V, f u = f v) :
  ∑ v : V, f v = Fintype.card V * (f v) := by
    have E : ∃ c : ℚ, ∀ u : V, f u = c := by
      use f v; intro u; apply eq_h
    have ⟨c, hc⟩ := E
    rw [hc v]
    simp_all only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]


theorem vertex_transitive_average_dist_eq_average_dist_from_vertex (G : SimpleGraph V) [Fintype V] [ne: Nonempty V] [DecidableRel G.Adj] (hconn: G.Connected) (h: isVertexTransitive G) (u : V) :
  average_dist_graph' G  = average_dist_graph_from_vertex G u := by
  unfold average_dist_graph'
  have eq_h : ∀ u v : V, average_dist_graph_from_vertex G u = average_dist_graph_from_vertex G v := by
    exact fun u v ↦ vertex_transitive_average_dist_from_vertex G hconn h u v
  have p : ∑ v : V, average_dist_graph_from_vertex G v = Fintype.card V * average_dist_graph_from_vertex G u := by
    apply constant_sum (λ x : V => average_dist_graph_from_vertex G x) eq_h
  have pcard : 0 < Fintype.card V := by apply Fintype.card_pos_iff.mpr ne
  simp_all [pcard]

theorem vertex_transitive_diam_at_most_2avg (G : SimpleGraph V) [Fintype V] [ne: Nonempty V] (v_gt_1 : Fintype.card V > 1) [DecidableRel G.Adj] (hconn: G.Connected) (h: isVertexTransitive G) :
  G.diam ≤ 2*average_dist_graph' G := by
  have e := G.exists_dist_eq_diam
  have ⟨u, v, d⟩ := e
  have hg : ∀w : V, average_dist_graph' G = (∑ x : V, (G.dist x w)) / (Fintype.card V - 1) := by
    intro w
    rw [vertex_transitive_average_dist_eq_average_dist_from_vertex _ _ _ w]
    unfold average_dist_graph_from_vertex; unfold sum_dist
    simp
    exact hconn; exact h

  have hv: average_dist_graph' G = (∑ x : V, (G.dist x v)) / (Fintype.card V - 1) := hg v
  have hu: average_dist_graph' G = (∑ x : V, (G.dist x u)) / (Fintype.card V - 1) := hg u

  have d_avg : 2 * average_dist_graph' G = (∑ x : V, (G.dist x v)) / (Fintype.card V - 1) + (∑ x : V, (G.dist x u)) / (Fintype.card V - 1) := by linarith
  rw [d_avg]
  simp
  have dsum : (∑ x : V, (G.dist x v)) / (@Nat.cast ℚ Rat.instNatCast (Fintype.card V) - 1) + (∑ x : V, (G.dist x u)) / (@Nat.cast ℚ Rat.instNatCast (Fintype.card V) - 1) = (∑ x : V, (G.dist x u + G.dist x v)) / (Fintype.card V - 1) := by
    field_simp
    have ee : (∑ x : V, @Nat.cast ℚ Rat.instNatCast (G.dist x v) + ∑ x : V, @Nat.cast ℚ Rat.instNatCast (G.dist x u)) =  (∑ x : V, (@Nat.cast ℚ Rat.instNatCast (G.dist x u) + @Nat.cast ℚ Rat.instNatCast (G.dist x v)))  := by
      rw [add_comm]
      apply Eq.symm Finset.sum_add_distrib
    rw [ee]

  simp at dsum
  rw [dsum]
  have s_diam : ∀ x : V, G.diam ≤ (↑(G.dist x u) + ↑(G.dist x v)) := by
    intro x
    rw [SimpleGraph.dist_comm]
    rw [←d]
    apply SimpleGraph.Connected.dist_triangle hconn

  have sum_s_diam :  ∑ _ : V, G.diam ≤ (∑ x : V, (↑(G.dist x u) + ↑(G.dist x v))) := by
    apply Finset.sum_le_sum
    have fset_s_diam :  ∀ x ∈ Finset.univ, G.diam ≤ G.dist x u + G.dist x v := by
      intro x _
      apply s_diam x
    apply fset_s_diam

  have sum_diam : ∑ _ : V, G.diam = Fintype.card V * G.diam := by
    apply Finset.sum_const
  rw [sum_diam] at sum_s_diam

  have almost_last : @Nat.cast ℚ Rat.instNatCast G.diam * (↑(Fintype.card V) - 1) ≤ ∑ x : V, (G.dist x u + G.dist x v) := by
    have f_trans : @Nat.cast ℚ Rat.instNatCast G.diam * (↑(Fintype.card V) - 1) ≤ Fintype.card V * G.diam := by
      rw [mul_comm]
      ring_nf
      field_simp
    push_cast
    apply LE.le.trans
    exact f_trans
    norm_cast

  field_simp [almost_last]
  rw [le_div_iff₀]
  push_cast at almost_last
  exact almost_last
  field_simp [v_gt_1]
