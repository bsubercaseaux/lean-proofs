import Mathlib

namespace DiamBasics
variable {α : Type*}  (G : SimpleGraph α)

lemma preconnected_of_ediam_ne_top (h_ne_top : G.ediam ≠ ⊤ ) : G.Preconnected := by
  unfold SimpleGraph.Preconnected
  intro u v
  apply SimpleGraph.reachable_of_edist_ne_top
  rw [←lt_top_iff_ne_top]
  rw [←lt_top_iff_ne_top] at h_ne_top
  calc G.edist u v ≤ G.ediam := by exact SimpleGraph.edist_le_ediam
                 _ < ⊤ := by exact h_ne_top

lemma connected_of_ediam_ne_top_and_nonempty (h_ne_top : G.ediam ≠ ⊤) (h_nonempty : Nonempty α) : G.Connected := by
  rw [SimpleGraph.connected_iff]; exact ⟨preconnected_of_ediam_ne_top G h_ne_top, h_nonempty⟩

notation "|" V "|" => Fintype.card V

lemma pos_diam_of_ne_top_and_card [Fintype α] (h_ne_top : G.ediam ≠ ⊤) (α_gt_1 : 1 < |α|) : 0 < G.diam  := by
  have ⟨u, v, uv_neq⟩ :=  Fintype.one_lt_card_iff.mp α_gt_1
  have h_conn : G.Connected := connected_of_ediam_ne_top_and_nonempty G h_ne_top (by rw [←Fintype.card_pos_iff]; linarith)
  have d_uv : G.dist u v > 0 := SimpleGraph.Connected.pos_dist_of_ne h_conn uv_neq
  calc 0 < G.dist u v := by apply d_uv
          _ ≤ G.diam := by apply SimpleGraph.dist_le_diam h_ne_top


lemma pos_diam_iff_ne_top_and_card [Fintype α]:
  G.diam > 0 ↔ G.ediam ≠ ⊤ ∧ 1 < |α| := by
  constructor
  . intro hdiam
    have diam_ne_zero : G.diam ≠ 0 := by linarith
    have nt_α : Nontrivial α := by apply SimpleGraph.nontrivial_of_diam_ne_zero diam_ne_zero
    have card : 1 < |α| := by
      rw [←Finite.one_lt_card_iff_nontrivial, Nat.card_eq_fintype_card] at nt_α; assumption
    have hediam : G.ediam ≠ ⊤ := by
      exact SimpleGraph.ediam_ne_top_of_diam_ne_zero diam_ne_zero
    exact ⟨hediam, card⟩
  . intro ⟨hediam, hcard⟩
    apply pos_diam_of_ne_top_and_card G hediam hcard


lemma diam_eq_zero_of_not_connected [Fintype α] (h : G.diam = 0) (h_gt_1: 1 < |α|)  : ¬ G.Connected := by
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
    . rw [←Fintype.card_le_one_iff_subsingleton] at q
      linarith


lemma pos_diam_of_connected_and_card [Fintype α] (hconn: G.Connected) (α_gt_1 : 1 < |α| ) :
  0 < G.diam := by
  by_contra h
  have h_diam : G.diam = 0 := by linarith
  have h_not_conn : ¬ G.Connected := diam_eq_zero_of_not_connected G h_diam α_gt_1
  contradiction

end DiamBasics
