import OAI.Computability.BorderVNP.PackedReportCableTransport

/-! # Word readback of the private views on a report with no trailing outputs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open Crossing CellAddressCircuit GeometryFrameEncoding VPVNP.BurstRAM VPVNP.VerifierNetwork
open RoutingISA DiagonalResidueRAM ParseBatchSort

variable {s m n C d k w J A W : ℕ} {σ : Type*} [Fintype σ] {F : Fields s m n C d k w σ}
    {old : Fin J → Fin s} {x : σ → Bool} {origin : ℕ} {mem : Memory W}

/-- When all the appended words are private fields, the original native
readback gives the full word array used by the report continuation. -/
theorem privateWords_without_tail (rest : Frame σ (Outputs 0 w))
    (saved : ∀ i : Fin (C+(J+C)), readings mem (origin+m*3+count m C J A+i.val) =
      value (fun j => (privateViews F old).eval x (i,j))) :
    ∀ i : Fin ((C+(J+C))+0), mem (origin+m*3+count m C J A+i.val) =
      word W (value fun j => (withPrivateViews F old rest).eval x (.inl (i,j))) := by
  intro i
  let j : Fin (C+(J+C)) := i
  change mem (origin+m*3+count m C J A+(j.castAdd 0).val) =
    word W (value fun z => (withPrivateViews F old rest).eval x (.inl (j.castAdd 0,z)))
  simp only [withPrivateViews,GeometryOutput.prepend_first,Fin.val_castAdd]
  rw [←saved j]
  apply Fin.ext
  exact (Nat.mod_eq_of_lt (mem _).isLt).symm

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
