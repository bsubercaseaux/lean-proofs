import Mathlib
import LeanProofs.DiamBasics

abbrev GraphAutomorphism (G : SimpleGraph α) := G ≃g G
def VertexTransitive (G : SimpleGraph α) := ∀ u v, ∃ f : GraphAutomorphism G, f u = v

/-
This file proves that for every connected vertex-transitive graph G,
  its diameter is at most twice the average vertex distance.

  That is, if μ(G) = ∑ u,v dist(u,v) / (|V|*(|V|-1)),
  then diam(G) < 2μ(G).

  Based on https://arxiv.org/abs/2501.00144.
-/

-- Step 1: prove that SimpleGraph.dist is preserved by automorphisms
variable {V : Type*} (G : SimpleGraph α) (f : GraphAutomorphism G) {u v : α}

lemma auto_walk_iff {d : Nat} (wh: ∃ (w : G.Walk u v), w.length = d) :
      ∃ (w' : G.Walk (f u) (f v)), w'.length = d := by
      let map : G.Walk u v -> G.Walk (f u) (f v) := SimpleGraph.Walk.map (f: G →g G)
      obtain ⟨w, hw⟩ := wh
      have map_length : (map w).length = w.length := by aesop
      use map w
      linarith

lemma auto_le_dist (hconn: G.Connected) (f : GraphAutomorphism G) :
  G.dist (f u) (f v) ≤ G.dist u v:= by
    have ⟨w, hw⟩: ∃ w' : G.Walk (f u) (f v), w'.length = G.dist u v := by
      apply auto_walk_iff
      apply SimpleGraph.Connected.exists_walk_length_eq_dist hconn
    rw [←hw]
    apply SimpleGraph.dist_le w

lemma auto_preserve_dist (hconn: G.Connected) (f : GraphAutomorphism G) :
  G.dist u v = G.dist (f u) (f v) := by
  rw [Nat.eq_iff_le_and_ge]
  apply And.intro
  . nth_rewrite 1 [←f.symm_apply_apply u]
    nth_rewrite 1 [←f.symm_apply_apply v]
    apply auto_le_dist G hconn f.symm
  . apply auto_le_dist G hconn f


-- Definition and basic facts of average distance
notation "|" V "|" => Fintype.card V

noncomputable def avg_dist (G : SimpleGraph α) [Fintype α] [DecidableRel G.Adj] : ℚ :=
  (∑ u : α, ∑ v : α, G.dist u v) / (|α| *(|α|-1))

noncomputable def avg_dist_from_vertex (G : SimpleGraph α) [Fintype α] [DecidableRel G.Adj] (v : α) : ℚ :=
  (∑ u : α, (G.dist u v)) / (|α| - 1)

noncomputable def avg_dist' (G : SimpleGraph α) [Fintype α] [DecidableRel G.Adj] : ℚ :=
  (∑ v : α, avg_dist_from_vertex G v) / |α|


variable {α : Type*} (G : SimpleGraph α) [Fintype α] [DecidableRel G.Adj]

noncomputable abbrev μ := avg_dist G
noncomputable abbrev μ' := avg_dist' G
noncomputable abbrev μ_v (v: α) := avg_dist_from_vertex G v


lemma avg_dist_eq_avg_dist' : μ' G = μ G := by
  unfold μ μ' avg_dist avg_dist' avg_dist_from_vertex
  field_simp [SimpleGraph.dist_comm, Finset.sum_add_distrib, Finset.sum_div]
  ring_nf; rfl

lemma vt_avg_dist_from_vertex_eq (hconn: G.Connected) (h: VertexTransitive G) (u v : α):
  μ_v G u = μ_v G v := by
  unfold μ_v avg_dist_from_vertex; unfold VertexTransitive at h
  obtain ⟨f, hf⟩ := h u v
  have sum_dist_eq : (∑ u_1 : α, G.dist u_1 u) = (∑ u : α, G.dist u v) := by
    rw [←hf]
    have lpre  : ∀ w : α, G.dist w u = G.dist (f w) (f u) := by
      exact fun w ↦ auto_preserve_dist G hconn f
    simp [lpre]
    apply Equiv.sum_comp f.1 (fun x ↦ G.dist x (f u))
  rw [sum_dist_eq]

lemma vt_avg_dist_eq_avg_dist_from_vertex  [ne: Nonempty α] (hconn: G.Connected) (h: VertexTransitive G) (u : α) :
  μ' G  = μ_v G u := by
  unfold μ' avg_dist'

  have p' : ∑ v : α, μ_v G v = |α| * μ_v G u := by
    simp [← (fun u v ↦ vt_avg_dist_from_vertex_eq G hconn h u v) u]
  simp_all

/-
The main theorem ; proof can perhaps be simplified
Paper proof is basically just the following

Let u, v be "antipodal" vertices in G, meaning that d(u, v) = diam(G).
Then, if we denote by μ(u) the average distance from u to all other vertices,
we have

2μ = μ(u) + μ(v)
   = (∑ x, dist(x, u) + dist(x, v)) / (|V| - 1)
   >= ∑ x, dist(u, v) / (|V| - 1) by the triangle inequality
   = |V| * diam(G) / (|V| - 1) > diam(G)

-/
theorem vertex_transitive_diam_at_most_2avg (nt : Nontrivial α) (hconn: G.Connected) (h: VertexTransitive G) :
  G.diam < 2*(μ' G) := by
  have ⟨u, v, d⟩ :=  G.exists_dist_eq_diam
  have hg : ∀ w : α, μ' G = (∑ x : α, (G.dist x w)) / (|α| - 1) := by
    intro w
    rw [vt_avg_dist_eq_avg_dist_from_vertex _ hconn h w]
    unfold μ_v avg_dist_from_vertex; simp

  have: μ' G = (∑ x : α, (G.dist x v)) / (|α| - 1) := hg v
  have: μ' G = (∑ x : α, (G.dist x u)) / (|α| - 1) := hg u

  have d_avg : 2 * μ' G = (∑ x : α, (G.dist x v)) / (|α| - 1) + (∑ x : α, (G.dist x u)) / (|α| - 1) := by linarith
  rw [d_avg]
  have α_gt_1 : |α| > 1 := by
    rw [←Finite.one_lt_card_iff_nontrivial] at nt
    simp at nt
    exact nt

  suffices : (G.diam : ℚ) * (|α| - 1) < ∑ x : α, (G.dist x v + G.dist x u)
  . field_simp [α_gt_1, lt_div_iff₀, this]
    rw [←Finset.sum_add_distrib]
    exact_mod_cast this

  . have sum_s_diam :  ∑ _ : α, G.diam ≤ (∑ x : α, (G.dist x v + G.dist x u)) := by
      apply Finset.sum_le_sum; intro  i _;
      rw [add_comm, G.dist_comm, ←d]
      apply SimpleGraph.Connected.dist_triangle hconn

    rw [Finset.sum_const, Finset.card_univ] at sum_s_diam

    have d_gt_0 : G.diam > 0 := pos_diam_of_connected_and_nt G hconn nt
    calc
      (G.diam : ℚ) * (|α| - 1) < |α| * G.diam := by simp_all only [mul_comm, Nat.cast_sum, Nat.cast_pos, mul_lt_mul_right, sub_lt_self_iff, zero_lt_one]
                             _ ≤ ∑ x : α, (G.dist x v + G.dist x u) := by exact_mod_cast sum_s_diam
