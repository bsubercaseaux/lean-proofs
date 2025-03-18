import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Ring.RingNF

namespace SimpleGraph
variable {G : SimpleGraph α} {H : SimpleGraph β}


lemma boxProd_reach (x y : α × β) :
  (G □ H).Reachable x y ↔ G.Reachable x.1 y.1 ∧ H.Reachable x.2 y.2 := by
  classical
  constructor
  . intro r
    obtain ⟨w⟩ := r
    exact ⟨⟨ w.ofBoxProdLeft⟩, ⟨w.ofBoxProdRight⟩⟩
  . intro ⟨r₁, r₂⟩
    obtain ⟨w₁⟩ := r₁
    obtain ⟨w₂⟩ := r₂
    exact ⟨(w₁.boxProdLeft _ _).append (w₂.boxProdRight _ _)⟩


lemma boxProd_edist_top (x y : α × β) :
    (G □ H).edist x y = ⊤ ↔ G.edist x.1 y.1 = ⊤ ∨ H.edist x.2 y.2 = ⊤ := by
  constructor
  . intro _
    have nh : ¬( (G □ H).edist x y ≠ ⊤) := by simp_all
    rw [edist_ne_top_iff_reachable, boxProd_reach] at nh
    repeat rw [← edist_ne_top_iff_reachable] at nh
    tauto
  . intro _
    have nh : ¬ (G.edist x.1 y.1 ≠ ⊤ ∧ H.edist x.2 y.2 ≠ ⊤) := by aesop
    repeat rw [edist_ne_top_iff_reachable] at nh
    rw [←boxProd_reach] at nh
    exact edist_eq_top_of_not_reachable nh


lemma len_sum_projections {a₁ a₂ : α} {b₁ b₂ : β} [DecidableEq α] [DecidableEq β] [DecidableRel G.Adj] [DecidableRel H.Adj] (w : (G □ H).Walk (a₁, b₁) (a₂, b₂)) :
    w.ofBoxProdLeft.length + w.ofBoxProdRight.length = w.length := by
  match w with
  | Walk.nil => simp [Walk.length, Walk.ofBoxProdLeft, Walk.ofBoxProdRight]
  | Walk.cons x w' =>
    next c =>
      simp
      unfold Walk.ofBoxProdLeft Walk.ofBoxProdRight Or.by_cases
      by_cases h₁ : G.Adj a₁ c.1 ∧ b₁ = c.2
      . simp [h₁]
        rw [← len_sum_projections w']
        ring_nf
        congr
        . exact h₁.2
        . simp
      . simp [h₁]
        have h₂ : H.Adj b₁ c.2 ∧ a₁ = c.1 := by aesop
        simp [h₂]
        rw [← len_sum_projections w']
        ring_nf
        simp [add_assoc, add_left_cancel_iff]
        rw [add_comm, add_left_cancel_iff]
        congr
        . exact h₂.2
        . simp

lemma boxProd_edist (x y : α × β) :
    (G □ H).edist x y = G.edist x.1 y.1 + H.edist x.2 y.2  := by
  classical
  by_cases h : (G □ H).edist x y = ⊤
  . rw [h]
    rw [boxProd_edist_top] at h
    aesop

  . have ⟨w, hw⟩ :=  exists_walk_of_edist_ne_top h
    rw [boxProd_edist_top] at h
    have rG : G.edist x.1 y.1 ≠ ⊤ := by tauto
    have rH : H.edist x.2 y.2 ≠ ⊤ := by tauto
    have ⟨wG, hwG⟩ := exists_walk_of_edist_ne_top rG
    have ⟨wH, hwH⟩ := exists_walk_of_edist_ne_top rH

    let h_walk : (G □ H).Walk x y := (wG.boxProdLeft _ _).append (wH.boxProdRight _ _)

    have h_walk_length : h_walk.length =  wG.length + wH.length := by
      rw [Walk.length_append]
      unfold Walk.boxProdLeft Walk.boxProdRight
      simp

    have edist_le_h_walk : (G □ H).edist x y ≤ h_walk.length := edist_le h_walk
    have le : (G □ H).edist x y ≤ G.edist x.1 y.1 + H.edist x.2 y.2 := by
      calc (G □ H).edist x y ≤ h_walk.length := by exact edist_le_h_walk
            _ = wG.length + wH.length := by exact_mod_cast h_walk_length
            _ = G.edist x.1 y.1 + H.edist x.2 y.2 := by simp [hwG, hwH]

    have ge : (G □ H).edist x y ≥ G.edist x.1 y.1 + H.edist x.2 y.2 := by
      let projG := Walk.ofBoxProdLeft w
      let projH := Walk.ofBoxProdRight w
      have proj_sum : projG.length + projH.length = w.length := by rw [len_sum_projections]

      rw [← hw, ← proj_sum]
      have proj_G_edist : G.edist x.1 y.1 ≤ projG.length := by apply edist_le
      have proj_H_edist : H.edist x.2 y.2 ≤ projH.length := by apply edist_le

      simp
      apply add_le_add proj_G_edist proj_H_edist

    apply le_antisymm le ge

end SimpleGraph
