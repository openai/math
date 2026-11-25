import OAI.Computability.BorderVNP.TransmissionPlacedBanks
import OAI.Computability.BorderVNP.CellPacketDelivered
import OAI.Computability.BorderVNP.RoutingWireNative

/-! # Actual receipts from local copies and checked remote data transfers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open CellSparse.Packet.Source (Receipt)
open Packing.Directory (Row)

variable {R r t d link inner n w : ℕ} {Edge : Type}
variable {G : Wiring R r t d link inner n Edge} {pin : Fin d → Bool}
variable {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}

open private sender_regs receiver_regs from OAI.Computability.BorderVNP.TransmissionAcrossHistory

/-- An actual returning native relay test implies all its physical comparisons at
their addressed positions in the initialized processor tapes. -/
theorem TransferBank.checked_of_return {v : Fin (R+1)} (V : TransferBank G pin ext L.width w L.header v)
    (hw : 0 < w) (macros : TeamOpcode.Macros w 8) (s : Bank w)
    (l : TableLayout) (row : ℕ → TableRow) (teams : l.teams = R+1)
    (widths : L.width = fun a b => l.widthMatrix row (a.cast teams.symm) (b.cast teams.symm))
    (al : l.Allocated w) (fit : l.RowsFit w row) (base : (V.pub 0).val = l.frame)
    (fields : l.frameFields (readings V.mem))
    (sizes : ∀ i < l.teams^2, readings V.mem (l.widths+i) = l.pairWidth row l.count i)
    (space : RelayRooms w l.teams (fun x y => l.partnerLength row x v.val y)
      (readings V.pub) (readings V.mem) v.val)
    {es final mt} (returning : Runs V.pub macros checkRelays s V.mem es final mt)
    (u : Fin (R+1)) (p : Hop L.three L.width u v) :
    RelayWordAgrees (readings V.pub) (readings V.mem) u v p.1 (p.2.val / (R+1-2)) :=
  (V.relay_hop_iff hw p).mpr (((V.native_relays hw macros s l row teams widths al fit base fields sizes space).sound
    returning).1 u p)

/-- On distinct endpoints the data sender selects the comparison handler. -/
private theorem sendingData {r : Range w} (hw : 0 < w) (tag : r.kind = 1) (hd : r.teamA ≠ r.teamB) :
    r.selected r.teamA = some (some .sendData) := by
  have one : (1 : Word w) ≠ 0 := fun h => by
    have v := congrArg Fin.val h
    simp only [Fin.val_one',Fin.val_zero,Nat.mod_eq_of_lt (Nat.one_lt_pow hw.ne' (by decide : 1 < 2))] at v
    omega
  simp [Range.selected,Range.bank,decision,Decision.role,tag,one,hd]

variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → ℕ} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}

/-- Every populated data bit has a real receipt at its allocated consumer address.
The local case copies the protected literal or substitution. The remote case
reconstructs the two native RAM snapshots and uses the checked physical relay.
No equality of the two endpoint values or final destination value is required. -/
theorem receipt_of_placed {cutoff : Fin (R+1) → ℕ} (hw : 0 < w)
    (bank : ∀ u, HistoryBank G pin ext L.width L.header u (H u) (cutoff u))
    (placed : ∀ u, PlacedImage (H u) D pp lp owner origin stride (pins u) (cutoff u))
    (relay : ∀ v, TransferBank G pin ext L.width w L.header v)
    (checked : ∀ u v, ∀ p : Hop L.three L.width u v, RelayWordAgrees (readings (relay v).pub)
      (readings (relay v).mem) u v p.1 (p.2.val/(R+1-2)))
    (ordinal : ℕ → ℕ)
    (ord : ∀ u, ∀ i : Fin (D.directory pp lp).length, ((H u).rows i).ordinal.val = ordinal i.val)
    (span : ∀ u, ∀ i : Fin (D.directory pp lp).length,
      ScheduledRange (G.transferFrame u L.header (bank u).initial.dst) L.width ((H u).rows i))
    (i : Fin (D.directory pp lp).length) (j : Fin (D.directory pp lp)[i.val].width) (u z : Fin (R+1))
    (srcTeam : (D.directory pp lp)[i.val].team = u.val)
    (dstTeam : owner (D.directory pp lp)[i.val].cell = z.val)
    (sourceLow : (D.directory pp lp)[i.val].sourceBase (pins u)+j.val < cutoff u) :
    Receipt (H u) (H z) ((D.directory pp lp)[i.val].sourceBase (pins u)+j.val)
      (D.deliveredAt pp lp origin stride ⟨i,j⟩) := by
  let su := (H u).rows i
  let rz := (H z).rows i
  have sa : su.teamA.val = u.val := ((placed u).sources.team i).trans srcTeam
  have sb : su.teamB.val = z.val := ((placed u).columns.team i).trans dstTeam
  have ra : rz.teamA.val = u.val := ((placed z).sources.team i).trans srcTeam
  have rb : rz.teamB.val = z.val := ((placed z).columns.team i).trans dstTeam
  have own : (H u).team = su.teamA := Fin.ext ((bank u).team.trans sa.symm)
  have dest : (H z).team = rz.teamB := Fin.ext ((bank z).team.trans rb.symm)
  have rowU := i.isLt.trans_le (placed u).count
  have slotU : j.val < su.width.val := ((placed u).columns.width i).symm ▸ j.isLt
  have source : su.source.val = (D.directory pp lp)[i.val].sourceBase (pins u) := (placed u).sources.source i
  have protect : ∀ k ≤ i.val, ((H u).rows k).protectsCell (H u).team (su.source.val+j.val) :=
    fun k hk => (placed u).low k (hk.trans_lt rowU) _ (by rwa [source])
  rw [← source]
  have writing := (placed z).write i j
  change LastWrite _ rz.teamB _ _ (if rz.teamA = rz.teamB then .dataHere else .receiveB) _ _ at writing
  by_cases same : u = z
  · subst z
    have eq : rz.teamA = rz.teamB := Fin.ext (ra.trans rb.symm)
    rw [ite_eq_left eq,← dest] at writing
    exact Receipt.localCopy _ _ _ _ writing (by rw [source]; exact sourceLow.trans_le (placed u).fits) protect
  · have unequal : su.teamA ≠ su.teamB := fun e => same (Fin.ext (sa.symm.trans ((congrArg Fin.val e).trans sb)))
    have different : rz.teamA ≠ rz.teamB := fun e => same (Fin.ext (ra.symm.trans ((congrArg Fin.val e).trans rb)))
    rw [ite_eq_right different,← dest] at writing
    have selected : su.selected (H u).team = some (some .sendData) :=
      own ▸ sendingData hw ((placed u).columns.kind i) unequal
    refine Receipt.relay _ _ _ _ _ rowU slotU selected writing ?_ (fun k hk => protect k hk.le)
    let A := (bank u).before (placed u) rowU.le
    let B := (bank z).bit (placed z) writing.row_lt writing.selected writing.slot_lt.le
    let v := Routing.relay L.three same (su.ordinal.val+j.val)
    have bound := (span u i).demand unequal
    have tA : (⟨su.teamA.val,(span u i).first⟩ : Fin (R+1)) = u := Fin.ext sa
    have tB : (⟨su.teamB.val,(span u i).second⟩ : Fin (R+1)) = z := Fin.ext sb
    change su.ordinal.val+su.width.val ≤ Routing.demand L.width ⟨su.teamA.val,_⟩ ⟨su.teamB.val,_⟩ at bound
    rw [tA,tB] at bound
    have hb : su.ordinal.val+j.val < Routing.demand L.width u z := (Nat.add_lt_add_left slotU _).trans_le bound
    let p : Hop L.three L.width u v := ⟨z,⟨su.ordinal.val+j.val,by simp [v,pairBits,same,hb]⟩⟩
    have fit := slotU.trans su.width.isLt
    have sreg := sender_regs su (H u).team j.val fit
    have rreg := receiver_regs rz (H z).team j.val fit
    have ordEq : su.ordinal.val = rz.ordinal.val := (ord u i).trans (ord z i).symm
    have wire := A.endpoint_eq same B hb (relay v) (checked u v p) 10 9 _ _
      (sreg.1.trans sb) (rreg.1.trans ra) sreg.2 (rreg.2.trans (congrArg (·+j.val) ordEq.symm))
    change (H u).before i.val (endpointNat 10 (bank u).initial.pub (su.bitBank (H u).team j.val) ((H u).before i.val)) =
      bitMemory _ _ _ _ _ _ _ _ (endpointNat 9 (bank z).initial.pub (rz.bitBank (H z).team j.val)
        (bitMemory _ _ _ _ _ _ _ _)) at wire
    rw [(bank u).args,(bank z).args] at wire
    unfold TeamHistory.linkWord
    convert wire using 2
    rw [endpointNat_eq]
    simp only [Range.senderAddress, sreg.1, sreg.2, su]

end TeamContraction

end BorderVNP
end Computability
end OAI
