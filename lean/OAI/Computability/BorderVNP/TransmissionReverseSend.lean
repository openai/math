import OAI.Computability.BorderVNP.TransmissionPairViews
import OAI.Computability.BorderVNP.TransmissionAssignedProgram

/-! # Every actual hop of a returned nonlocal data row carries the forced input bit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open private sendingData from OAI.Computability.BorderVNP.TransmissionDataReceipt
open private hop_relay from OAI.Computability.BorderVNP.TransmissionAcross

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {ib hb sb : Fin (R+1) → ℕ}
local notation "PL" => fun u => G.pinLayout u (ib u) (hb u) (sb u)
local notation "Delivery" => ReturnedDelivery G pin ext L D pp lp owner origin stride H PL

/-- A returning sender's actual comparison forces the originally programmed literal
or prepared substitute on the precisely identified exterior hop. The argument is
an arbitrary hop with the scheduled endpoints and ordinal, as needed to invert
`TableLayout.recordBitsEquiv` on all exterior positions. -/
theorem ReturnedDelivery.remote_data_hop (f : Delivery) (guess : Fin (R+1) → ℕ → Bool)
    {u v : Fin (R+1)} (p : Hop L.three L.width u v) (sub : Pins.SubstitutionAt (PL u) (guess u) (H u).initial)
    (i : Fin (D.directory pp lp).length) (j : Fin (D.directory pp lp)[i.val].width)
    (first : (f.row i).first = u.val) (second : (f.row i).second = p.1.val)
    (ord : p.2.val = f.table.ordinal f.row i+j.val) :
    (L.exteriorEquiv ext).hop u v p = G.dataBit guess (D.directory pp lp)[i.val] j.val := by
  let raw := (D.directory pp lp)[i.val]
  let a := (H u).rows i
  have reach := i.isLt.trans_le (f.placed u).count
  obtain ⟨_,ha,hpeer,_,ho⟩ := tableRange_fields (f.image u) f.allocated (f.records u) (i.isLt.trans_le f.prefixCount)
  rw [← f.ranges u] at ha hpeer ho
  have srcTeam : a.teamA.val = u.val := ha.trans first
  have dstTeam : a.teamB.val = p.1.val := hpeer.trans second
  have own : (H u).team = a.teamA := Fin.ext ((f.bank u).team.trans srcTeam.symm)
  obtain ⟨ne,relay⟩ := hop_relay p
  have remote : a.teamA ≠ a.teamB := fun h => ne (Fin.ext (srcTeam.symm.trans ((congrArg Fin.val h).trans dstTeam)))
  have sel : a.selected (H u).team = some (some .sendData) :=
    own ▸ sendingData f.word ((f.placed u).columns.kind i) remote
  have hj : j.val < a.width.val := ((f.placed u).columns.width i).symm ▸ j.isLt
  have checked := (H u).word.property i reach sel j hj
  let A := (f.bank u).before (f.placed u) reach.le
  have args : A.pub = (H u).pub := (f.bank u).args
  have offset : a.ordinal.val+j.val = p.2.val := (congrArg (·+j.val) ho).trans ord.symm
  have own0 : frameField (readings A.pub) (readings A.mem) 0 = u.val := A.schedule.frame.1
  have num : frameField (readings A.pub) (readings A.mem) 1 = R+1 := A.schedule.frame.2.1
  have addr : a.senderAddress (H u).pub A.mem j = routedAddress (readings A.pub) (readings A.mem) u v p.1
      (p.2.val/(R+1-2)) := by
    calc _ = a.senderAddress A.pub A.mem j := congrArg (fun x => a.senderAddress x A.mem j) args.symm
         _ = _ := by simp only [Range.senderAddress,own0,num,dstTeam,offset,endpointRelay_eq L.three ne,relay]
  change A.mem (a.source.val+j.val) = A.mem (a.senderAddress (H u).pub A.mem j.val) at checked
  rw [addr] at checked
  have physical := A.read_source_hop f.word p
  have source : a.source.val = raw.sourceBase (PL u) := (f.placed u).sources.source i
  have hteam : raw.team = u.val := ((f.placed u).sources.team i).symm.trans srcTeam
  have low := D.source_below pp lp (List.getElem_mem i.isLt) f.positive j.isLt (PL u) (f.dimensions u).1 (f.dimensions u).2
    (f.table.readExtent (PL u)) (f.table.readExtent_bounds _).2.1 (f.table.readExtent_bounds _).2.2
  obtain ⟨hp,hbit⟩ := D.populated_source_bounds pp lp (List.getElem_mem i.isLt) f.positive j.isLt
  have pc : D.processors = r := (f.dimensions u).1
  have lc : D.literal = G.program.length+t := (f.dimensions u).2
  have bit := G.read_dataBit guess u pin ext (ib u) (hb u) (sb u) (H u).initial (f.loaded u) sub raw hteam
    (pc ▸ hp) j (lc ▸ hbit)
  have initial : A.mem (a.source.val+j.val) = (H u).initial (raw.sourceBase (PL u)+j.val) := by
    rw [source]; exact (f.placed u).before_low reach.le low
  have compare := (congrArg Fin.val checked).symm.trans (congrArg Fin.val (initial.trans bit))
  rw [Fin.val_ofNat,Nat.mod_eq_of_lt ((Bool.toNat_lt _).trans_le (Nat.one_lt_pow f.word.ne' (by decide : 1<2)))] at compare
  exact (show Function.Injective Bool.toNat by decide) (physical.symm.trans compare)

/-- Either endpoint of any data descriptor forces the same concrete input bit.
The reversed leg follows from the successful native relay comparison. -/
theorem ReturnedDelivery.data_pair_value (f : Delivery) (guess : Fin (R+1) → ℕ → Bool)
    (sub : ∀ u, Pins.SubstitutionAt (PL u) (guess u) (H u).initial)
    {u v : Fin (R+1)} (p : Hop L.three L.width u v)
    (i : Fin (D.directory pp lp).length) (j : Fin (D.directory pp lp)[i.val].width)
    (ends : (f.row i).first = u.val ∧ (f.row i).second = p.1.val ∨
      (f.row i).first = p.1.val ∧ (f.row i).second = u.val)
    (ord : p.2.val = f.table.ordinal f.row i+j.val) :
    (L.exteriorEquiv ext).hop u v p = G.dataBit guess (D.directory pp lp)[i.val] j.val := by
  rcases ends with ⟨first,second⟩ | ⟨first,second⟩
  · exact f.remote_data_hop guess p (sub u) i j first second ord
  · exact (((f.relay v).relay_hop_iff f.word p).mp (f.checked u v p)).trans
      (f.remote_data_hop guess (otherHop L.three L.width p) (sub p.1) i j first second ord)

end TeamContraction

end BorderVNP
end Computability
end OAI
