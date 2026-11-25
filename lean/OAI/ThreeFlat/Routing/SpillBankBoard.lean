import OAI.ThreeFlat.Routing.SpillLinks
import OAI.ThreeFlat.Routing.SpillReserveSelectorNetwork
import OAI.ThreeFlat.Concentrator.TwoPassBank
import OAI.ThreeFlat.Concentrator.PublicGraph

namespace OAI
/-! # The public edges joining both sparse-packing banks -/

noncomputable section
open scoped Classical
namespace ThreeFlat.Routing.Spill
open Concentrator

variable {C q D R : ℕ} (B : TwoPassBank C q D R)
abbrev primaryBoard := fun e => (B.N e).toFinset
abbrev fullBoard := publicNeighbors B.address.toEmbedding B.N B.G
abbrev BankSignal := Candidate (primaryBoard B) ⊕ ReserveChoice (Fin (C*R)) B.slots

/-- One selector wire per actual public edge. For a reserve loop its source
end supplies the unique selector for the advertised output register. -/
def boardSignal (c : Candidate (fullBoard B)) : BankSignal B :=
  match hz : B.address.symm c.2.val with
  | .inl r => .inl ⟨c.1, r, by
      apply List.mem_toFinset.mpr
      apply (mem_publicNeighbors_iff B.address.toEmbedding B.N B.G c.1 (.inl r)).mp
      change B.address (.inl r) ∈ fullBoard B c.1
      simp [← hz,c.2.property]⟩
  | .inr (v,j) => .inr (c.1,decide (v ≠ B.G.src c.1),j)

def boardPick (primary : Candidate (primaryBoard B) → Bool) (reserve : ReserveChoice (Fin (C*R)) B.slots → Bool) :
    Candidate (fullBoard B) → Bool := (Sum.elim primary reserve) ∘ boardSignal B

theorem fullBoard_left (e : Fin (C*R)) : (fullBoard B e).card ≤ 3*D := by
  have hh := publicNeighbors_left_degree B.address.toEmbedding B.N B.G B.primaryDegree e
  exact hh.trans (by have := B.slotBound; omega)

theorem fullBoard_right (r : Fin R) : Fintype.card (Contenders (fullBoard B) r) ≤ D := by
  have hh := publicNeighbors_right_degree B.address.toEmbedding B.N B.G B.reverseDegree
    B.incidentDegree r
  simpa [Contenders,fullBoard,Fintype.card_subtype] using hh

end ThreeFlat.Routing.Spill

end
end OAI
