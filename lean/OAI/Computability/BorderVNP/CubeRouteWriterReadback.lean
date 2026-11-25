import OAI.Computability.BorderVNP.CubeRouteNativePlacement
import OAI.Computability.BorderVNP.CubeRoutePinnedFrame
import OAI.Computability.BorderVNP.CubeRouteProfileInputs
import OAI.Computability.BorderVNP.CubeScatterSharedArenaLayout
import OAI.Computability.BorderVNP.RoutingISACubeArenaPreserveGroups

/-! # True physical inputs and scheduler fields at the native writer return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube RoutingISA.Transmission PackedHistoryCircuit

variable {w n bits : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
variable {r t : Bank w} {m mt : Memory w} {es : List (TeamRAM.Event w)}

/-- The secondary header and all earlier allocations are before the first emitted transmission record. -/
theorem secondary_le_records (ar : CubeArena.Layout) : ar.header.header ≤ ar.records := by
  obtain ⟨start,_,_,_,_,_,power,gap,groups,totals,owners,pairs,host⟩ := ar.group_order
  exact start.trans (power.trans ((Nat.le_add_right ..).trans (gap.trans (groups.trans (totals.trans
    (owners.trans (pairs.trans host)))))))

/-- The public writer return preserves the processor tape, substituted input, and seven transfer
parameters. Its final count comes from the shared appender, while the five scheduler pointers
come from the pinned ordinary boot frame. -/
theorem WriterHistory.routeSources (H : WriterHistory n bits pub mac r m es t mt) (ar : CubeArena.Layout)
    (frame axis num : ℕ) (ok : DataReady pub H.dataInput) (base : (pub 0).val = frame)
    (output : (DataWriter.layout (readings pub) (readings H.dataInput)).output = ar.records)
    (emit : (ar.sharedRows frame axis num).Emitted (readings H.sharedInput) (readings mt))
    (low : frame+112 ≤ ar.header.header) (prior : ∀ x < ar.header.header, H.dataInput x = m x)
    (pins : Pins.Layout) (f : BroadcastFrame) (F : Pins.ProcessorFields pins) (guess : ℕ → Bool)
    (teams : f.teams = ar.teams) (inputRoom : F.header.length ≤ frame)
    (pinRoom : frame+13 < pins.ibase ∧ pins.ibase+pins.count ≤ ar.header.header)
    (sources : ProfileRouteInputs F f pub guess m)
    (pointers : TablePointers (ar.table frame (num+ar.header.d.choose 2)) (readings m)) :
    (ar.table frame (num+ar.header.d.choose 2)).frameFields (readings mt) ∧ ProfileRouteInputs F f pub guess mt := by
  let g := ar.sharedRows frame axis num
  let tab := ar.table frame (num+ar.header.d.choose 2)
  have image := H.dataImage ok
  rw [image] at emit
  have keep (x : ℕ) (hx : x < ar.header.header) (field : x ≠ frame+13) : mt x = m x := by
    have h₁ := CubeArena.emitted_before_records _ pub H.dataInput emit base.symm output.symm x
      (output.symm ▸ hx.trans_le (secondary_le_records ar)) (base.symm ▸ field)
    exact (Fin.ext h₁).trans (prior x hx)
  have fixed (k : ℕ) (hk : k < 112) (hne : k ≠ 13) : mt (frame+k) = m (frame+k) :=
    keep _ ((Nat.add_lt_add_left hk _).trans_le low) (by omega)
  have final := sources.congr (fun x hx => keep x (by omega) (by omega))
    (fun j hj => keep _ (by omega) (by omega)) (fun j hj => by rw [base]; apply fixed <;> simp at hj <;> omega)
  have ptr := pointers.transfer (fun j hj => by
    change readings mt (frame+j) = readings m (frame+j)
    apply congrArg Fin.val
    apply fixed <;> simp at hj <;> omega)
  have teamAt : readings mt (frame+1) = ar.teams := base ▸ final.broadcast.2.1.trans teams
  have countAt : readings mt (frame+13) = num+ar.header.d.choose 2 := emit.count
  exact ⟨⟨teamAt,ptr.records,countAt,ptr.widths,ptr.offsets,ptr.used,ptr.ordinals⟩,final⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
