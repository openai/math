import OAI.Computability.BorderVNP.TransmissionAssignedPayload
import OAI.Computability.BorderVNP.TransmissionRouteFactory
import OAI.Computability.BorderVNP.DiagonalNativeSenderAssignments

/-! # The genuine exterior coordinate compared by a native data sender -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}

/-- The native sender's team word is the team at its populated scheduling bank. -/
theorem TransferBank.teamWord {u : Fin (R+1)} (A : TransferBank G pin ext L.width w L.header u) :
    (directoryFrame A.pub A.mem 0).val = u.val := by
  simpa [directoryFrame,frameField,Wiring.transferFrame,readings] using A.schedule.frame.1

/-- A source leg lies inside the original physical input tape on the sending
team, with no assumption about local choices or sender equality. -/
theorem TransferBank.source_address_lt {u v : Fin (R+1)} (A : TransferBank G pin ext L.width w L.header u)
    (p : Hop L.three L.width u v) :
    routedAddress (readings A.pub) (readings A.mem) u v p.1 (p.2.val/(R+1-2)) <
      (G.processorFields u pin ext A.ibase A.hbase A.starbase).header.length := by
  have ne := hop_ne_relay p
  have neq : v.val ≠ u.val := fun h => ne (Fin.ext h.symm)
  obtain ⟨f0,f1,_,f3,f4,f5,_⟩ := A.schedule.frame
  let pos := (legEquiv L.three L.width u v p).val + L.header + (if v < u then legLoad L.three L.width v u else 0)
  have addr : legPosition (readings A.pub) (readings A.mem) u v p.1 (p.2.val/(R+1-2)) = pos :=
    (A.schedule.table.legPosition_eq p).trans (show
    (legEquiv L.three L.width u v p).val + frameField (readings A.pub) (readings A.mem) 5 +
      (if v < u then legLoad L.three L.width v u else 0) = pos from by rw [f5]; rfl)
  have cap := A.schedule.capacity v neq
  change L.header+legLoad L.three L.width u v+legLoad L.three L.width v u ≤ link*r at cap
  have room : pos < r*link := by
    have lim := (legEquiv L.three L.width u v p).isLt
    dsimp only [pos]
    rw [Nat.mul_comm r link]
    split <;> omega
  simp only [routedAddress,f0,f1,f3,f4,addr,Wiring.transferFrame,ite_true]
  exact (G.processorFields u pin ext A.ibase A.hbase A.starbase).exterior_address_lt_header
    v.val pos u.isLt v.isLt neq room

/-- The source comparison's addressed word is precisely the exterior value on the
scheduled hop of this row. Its physical address precedes the end of the processor
input segment. Both the remote endpoint and relay ordinal are fixed by the row. -/
theorem TransferBank.sender_hop (hw : 0 < w) {u : Fin (R+1)}
    (A : TransferBank G pin ext L.width w L.header u) (row : Range w)
    (span : ScheduledRange (G.transferFrame u L.header A.dst) L.width row)
    (sel : row.selected (directoryFrame A.pub A.mem 0) = some (some .sendData))
    {j : ℕ} (hj : j < row.width.val) :
    ∃ z : Fin (R+1), ∃ different : u ≠ z,
      let k := row.ordinal.val+j
      let v := Routing.relay L.three different k
      ∃ p : Hop L.three L.width u v, row.teamB.val = z.val ∧ p.1=z ∧ p.2.val=k ∧
        row.senderAddress A.pub A.mem j < (G.processorFields u pin ext A.ibase A.hbase A.starbase).header.length ∧
        (A.mem (row.senderAddress A.pub A.mem j)).val = ((L.exteriorEquiv ext).hop u v p).toNat := by
  obtain ⟨own,remote⟩ := row.sender_endpoints sel
  let z : Fin (R+1) := ⟨row.teamB.val,span.second⟩
  have first : row.teamA.val = u.val := (congrArg Fin.val own.symm).trans A.teamWord
  have diff : u ≠ z := fun e => remote (Fin.ext (first.trans (congrArg Fin.val e)))
  let k := row.ordinal.val+j
  let v := Routing.relay L.three diff k
  have bounds := span.demand remote
  have sa : (⟨row.teamA.val,span.first⟩ : Fin (R+1)) = u := Fin.ext first
  change row.ordinal.val+row.width.val ≤ demand L.width ⟨row.teamA.val,_⟩ z at bounds
  rw [sa] at bounds
  have valid : k < demand L.width u z := (Nat.add_lt_add_left hj _).trans_le bounds
  let p : Hop L.three L.width u v := ⟨z,⟨k,by simp [v,pairBits,diff,valid]⟩⟩
  have own0 : frameField (readings A.pub) (readings A.mem) 0 = u.val := A.schedule.frame.1
  have teams1 : frameField (readings A.pub) (readings A.mem) 1 = R+1 := A.schedule.frame.2.1
  have addr : row.senderAddress A.pub A.mem j =
      routedAddress (readings A.pub) (readings A.mem) u v z (k/(R+1-2)) := by
    change routedAddress _ _ _ (endpointRelay _ _ z.val k) z.val (k/(_-2)) = _
    rw [own0,teams1,endpointRelay_eq L.three diff]
  refine ⟨z,diff,p,rfl,rfl,rfl,?_,?_⟩
  · rw [addr]; exact A.source_address_lt p
  · rw [addr]; exact A.read_source_hop hw p

end TeamContraction

end BorderVNP
end Computability
end OAI
