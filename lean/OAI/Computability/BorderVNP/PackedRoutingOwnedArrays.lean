import OAI.Computability.BorderVNP.PackedRoutingPrivateViews

/-! # Native original-box and owned-cell operands following the live placement rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open Crossing CellAddressCircuit CellAddressPhysical CellAddresses GeometryFrameEncoding
open VPVNP.BurstRAM VPVNP.VerifierNetwork RoutingISA DiagonalResidueRAM ParseBatchSort

variable {D s m n C d k w J A o W : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
variable (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ) {x : σ → Bool}
variable (net : Represents N cell aux siteID edgeID portID F x)
variable (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)

include net fit

/-- Every appended field occupies the address read by the original-box and owned-cell
native row producers. The output hypothesis is the remaining word array from export_runs. -/
theorem owned_words (old : Fin J → N.Site) (rest : Frame σ (Outputs o w)) (origin : ℕ) (mz : Memory W)
    (width : w ≤ W) (out : ∀ i : Fin ((C+(J+C))+o), mz (origin+m*3+count m C J A+i.val) =
      word W (value fun j => (withPrivateViews F (siteID ∘ old) rest).eval x (.inl (i,j)))) :
    let first := (bases origin m C J).livePairs+2*A
    (∀ c : Fin C, readings mz (first+c.val) = guessedSize N cell c+siteSize N cell c aux) ∧
    (∀ i : Fin J, readings mz (first+C+i.val) = siteBase N cell (cell (old i)) siteID aux ⟨old i,rfl⟩) ∧
      ∀ c : Fin C, readings mz (first+C+J+c.val) = guessedSize N cell c := by
  intro first
  have val (i : Fin (C+(J+C))) : readings mz (first+i.val) =
      value (fun j => (privateViews F (siteID ∘ old)).eval x (i,j)) := by
    have raw := out (i.castAdd o)
    simp only [withPrivateViews,GeometryOutput.prepend_first,Fin.val_castAdd] at raw
    have exactWord := (congrArg Fin.val raw).trans
      (word_val _ _ ((value_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0<2) width)))
    change (mz (first+i.val)).val = _
    have start : first = origin+m*3+count m C J A := by dsimp [first,bases,count]; omega
    rwa [start]
  refine ⟨fun c => ?_,fun i => ?_,fun c => ?_⟩
  · exact (val (c.castAdd (J+C))).trans (privateViews_wires F N cell aux siteID edgeID portID net fit _ c)
  · simpa only [Fin.val_natAdd,Fin.val_castAdd,Nat.add_assoc] using
      (val (Fin.natAdd C (i.castAdd C))).trans (privateViews_site F N cell aux siteID edgeID portID net fit old i)
  · simpa only [Fin.val_natAdd,Nat.add_assoc] using
      (val (Fin.natAdd C (Fin.natAdd J c))).trans (privateViews_internal F N cell aux siteID edgeID portID net fit _ c)

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
