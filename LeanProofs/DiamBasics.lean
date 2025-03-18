import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Order.CompletePartialOrder

variable {α : Type*}  (G : SimpleGraph α)

lemma preconnected_of_ediam_ne_top (h_ne_top : G.ediam ≠ ⊤ ) : G.Preconnected := by
  unfold SimpleGraph.Preconnected
  intro u v
  apply SimpleGraph.reachable_of_edist_ne_top
  rw [← lt_top_iff_ne_top]
  rw [← lt_top_iff_ne_top] at h_ne_top
  calc G.edist u v ≤ G.ediam := by exact SimpleGraph.edist_le_ediam
                 _ < ⊤ := by exact h_ne_top

lemma connected_of_ediam_ne_top_and_nonempty (h_ne_top : G.ediam ≠ ⊤) (h_nonempty : Nonempty α) : G.Connected := by
  rw [SimpleGraph.connected_iff]; exact ⟨preconnected_of_ediam_ne_top G h_ne_top, h_nonempty⟩

-- Converse of SimpleGraph.ediam_ne_top_of_diam_ne_zero
lemma pos_diam_of_ne_top_and_nt (h_ne_top : G.ediam ≠ ⊤) (nt_α : Nontrivial α) : 0 < G.diam  := by
  have ⟨u, v, uv_neq⟩ := nt_α
  have h_conn : G.Connected := connected_of_ediam_ne_top_and_nonempty G h_ne_top nt_α.to_nonempty
  calc 0 < G.dist u v := by apply SimpleGraph.Connected.pos_dist_of_ne h_conn uv_neq
          _ ≤ G.diam := by apply SimpleGraph.dist_le_diam h_ne_top

lemma pos_diam_iff_ne_top_and_nt : G.diam > 0 ↔ G.ediam ≠ ⊤ ∧ Nontrivial α := by
  constructor
  . intro hdiam
    have diam_ne_zero : G.diam ≠ 0 := by linarith
    have nt_α : Nontrivial α := by apply SimpleGraph.nontrivial_of_diam_ne_zero diam_ne_zero
    have hediam : G.ediam ≠ ⊤ := by
      exact SimpleGraph.ediam_ne_top_of_diam_ne_zero diam_ne_zero
    exact ⟨hediam,  SimpleGraph.nontrivial_of_diam_ne_zero diam_ne_zero⟩
  . intro ⟨hediam, hcard⟩
    apply pos_diam_of_ne_top_and_nt G hediam hcard

lemma not_connected_of_diam_zero [Fintype α] (h : G.diam = 0) (nt_α: Nontrivial α)  : ¬ G.Connected := by
  rw [SimpleGraph.connected_iff];
  cases isEmpty_or_nonempty α
  · intro h; aesop
  · simp
    rw [SimpleGraph.diam_eq_zero] at h
    rcases h with  p | q
    . have uv_top : ∃ u v, G.edist u v = ⊤ := by
        rw [←p]
        apply SimpleGraph.exists_edist_eq_ediam_of_finite
      unfold SimpleGraph.Preconnected
      simp
      have ⟨u, v, h_uv⟩ := uv_top
      use u; use v;
      rw [←SimpleGraph.edist_ne_top_iff_reachable]
      tauto
    . have := not_subsingleton α
      contradiction

lemma pos_diam_of_connected_and_nt [Fintype α] (hconn: G.Connected) (nt_α : Nontrivial α ) :
  0 < G.diam := by
  by_contra h
  have h_diam : G.diam = 0 := by linarith
  have h_not_conn : ¬ G.Connected := not_connected_of_diam_zero G h_diam nt_α
  contradiction
