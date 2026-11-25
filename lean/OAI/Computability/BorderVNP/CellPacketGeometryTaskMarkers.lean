import OAI.Computability.BorderVNP.CellPacketGeometryDescriptorInverse
import OAI.Computability.BorderVNP.CellPacketGeometryRate

/-! # The actual two physical task-marker indices in a site-major packet sort -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.LiveWords

open ParseBatchSort VPVNP.VerifierNetwork

variable {σ E I Orig : Type} [Fintype σ] [Fintype E] [Fintype I] {s C q k w : ℕ}

/-- The ordered template's second sort contains one start and one stop
marker for every cell, separated by the three physical words per chunk.
Both original indices and their returned positions fit the descriptor bank. -/
theorem Template.descriptorMarkerRanks (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (anchors : Frame σ (Fin s × Fin q)) (baseOwner : Fin s → Fin C) (pin : Orig → T.Fields)
    (pad : s < 2^q) (dest H : ℕ) (x : σ → Bool) (wide : 2^T.chunkDepth ≤ 2^w) (mem : ℕ → ℕ)
    (output : ∀ i : Fin (Total T.publicDepth T.chunkDepth), mem (dest+i.val) =
      value (fun j => (T.orderedFrame up anchors baseOwner pin pad dest H).eval x (.inl (i,j)))) :
    let padded := 2^T.chunkDepth
    let rank := descriptorBank dest T.publicDepth+padded
    let stops := C+3*T.chunkLabels.length
    (C ≤ stops ∧ stops+C ≤ padded) ∧
      ∀ c < C, mem (rank+c) < padded ∧ mem (rank+(stops+c)) < padded := by
  intro padded rank stops
  obtain ⟨π,inverse⟩ := descriptorInverse_of_output _ _ x dest mem wide output
  have cap := T.sort_rooms.2.1
  rw [Schema.coords_length] at cap
  refine ⟨⟨Nat.le_add_right ..,cap⟩,fun i hi => ?_⟩
  let c : Fin C := ⟨i,hi⟩
  let start := Markers.start T.sort_rooms.2.1 c
  let stop := Markers.stop T.sort_rooms.2.1 c
  have atStart := (inverse start).trans_lt (π.symm start).isLt
  have atStop := (inverse stop).trans_lt (π.symm stop).isLt
  exact ⟨atStart,by simpa only [stop,Markers.stop,Schema.coords_length] using atStop⟩

end CellPacketGeometry.LiveWords

end BorderVNP
end Computability
end OAI
