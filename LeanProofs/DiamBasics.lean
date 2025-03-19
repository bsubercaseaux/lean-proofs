import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Order.CompletePartialOrder

variable {α : Type*}  (G : SimpleGraph α)

lemma preconnected_of_ediam_ne_top (h_ne_top : G.ediam ≠ ⊤ ) : G.Preconnected := by
   apply Classical.not_not.mp (mt G.ediam_eq_top_of_not_preconnected h_ne_top)

lemma connected_of_ediam_ne_top_and_nonempty (h_ne_top : G.ediam ≠ ⊤) (h_nonempty : Nonempty α) : G.Connected := by
  rw [SimpleGraph.connected_iff]; exact ⟨preconnected_of_ediam_ne_top G h_ne_top, h_nonempty⟩

-- Converse of SimpleGraph.ediam_ne_top_of_diam_ne_zero
lemma pos_diam_of_ne_top_and_nt (h_ne_top : G.ediam ≠ ⊤) (nt_α : Nontrivial α) : 0 < G.diam  := by
  have ⟨u, v, uv_neq⟩ := nt_α
  have h_conn : G.Connected := connected_of_ediam_ne_top_and_nonempty G h_ne_top nt_α.to_nonempty
  calc 0 < G.dist u v := by apply SimpleGraph.Connected.pos_dist_of_ne h_conn uv_neq
          _ ≤ G.diam := by apply SimpleGraph.dist_le_diam h_ne_top

lemma pos_diam_iff_ne_top_and_nt : G.diam > 0 ↔ G.ediam ≠ ⊤ ∧ Nontrivial α := by
  rw [← not_iff_not, not_and, not_nontrivial_iff_subsingleton]
  simp [G.diam_eq_zero]
  tauto

lemma not_connected_of_diam_zero [Fintype α] (nt_α: Nontrivial α) (h : G.diam = 0) : ¬ G.Connected := by
  rw [SimpleGraph.connected_iff];
  cases isEmpty_or_nonempty α
  · intro h; aesop
  · simp
    rw [SimpleGraph.diam_eq_zero] at h
    rcases h with  p | q
    . have uv_top : ∃ u v, G.edist u v = ⊤ := by
        rw [← p]
        apply SimpleGraph.exists_edist_eq_ediam_of_finite
      unfold SimpleGraph.Preconnected
      simp
      have ⟨u, v, h_uv⟩ := uv_top
      use u; use v;
      rw [← SimpleGraph.edist_ne_top_iff_reachable]
      tauto
    . have := not_subsingleton α
      contradiction


lemma not_connected_iff_diam_zero [Fintype α] (nt_α : Nontrivial α) : ¬ G.Connected ↔ G.diam = 0 := by
  constructor
  . exact SimpleGraph.diam_eq_zero_of_not_connected
  . exact not_connected_of_diam_zero G nt_α

lemma pos_diam_of_connected_and_nt [Fintype α] (hconn: G.Connected) (nt_α : Nontrivial α ) :
  0 < G.diam := by
  by_contra h
  have h_diam : G.diam = 0 := by linarith
  have h_not_conn : ¬ G.Connected := not_connected_of_diam_zero G nt_α h_diam
  contradiction
