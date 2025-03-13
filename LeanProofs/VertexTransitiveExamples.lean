import Mathlib
import LeanProofs.VertexTransitive

--  As an example, let's prove that cliques are vertex transitive!
section clique
def Clique (n : Nat) : SimpleGraph (ZMod n) :=
  { Adj := fun u v => u ≠ v,
    symm := by intros u v h; exact Ne.symm h,
    loopless := by intro u; simp}

lemma clique_vertex_transitive (n : Nat) : VertexTransitive (Clique n) := by
  unfold VertexTransitive
  intro u v
  let f : ZMod n → ZMod n := fun x ↦ x + (v - u)
  let f_inv : ZMod n → ZMod n := fun x ↦ x - (v - u)

  have left_inverse: ∀ x, f_inv (f x) = x := by intro x; unfold f f_inv; ring
  have right_inverse: ∀ x, f (f_inv x) = x := by intro x; unfold f f_inv; ring

  let g: ZMod n ≃ ZMod n := ⟨f, f_inv, left_inverse, right_inverse⟩
  let f_auto : GraphAutomorphism (Clique n) :=  ⟨g, by intro x y; unfold Clique; simp⟩
  exact ⟨f_auto, by aesop⟩

end clique
