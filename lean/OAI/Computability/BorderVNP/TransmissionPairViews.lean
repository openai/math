import OAI.Computability.BorderVNP.TransmissionNativeDelivery

/-! # Both physical views of a shared pair in the native cell banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open private sender_regs from OAI.Computability.BorderVNP.TransmissionAcrossHistory

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
local notation "Delivery" => ReturnedDelivery G pin ext L D pp lp owner origin stride H pins

private theorem shared_info (f : Delivery) (g : Cube.SharedRows.Layout) (u : Fin (R+1))
    {src : ℕ → ℕ} (em : g.Emitted src (f.before u)) (fit : g.Fits w src) (recBase : f.table.records = g.records)
    (ct : f.table.count = g.dataCount+g.groups.choose 2) {s t : ℕ} (hs : s < t) (ht : t < g.groups) :
    let i := g.rowIndex s t
    let row := (H u).rows i
    row.kind = 0 ∧ row.teamA.val = (f.row i).first ∧ row.teamB.val = (f.row i).second ∧
      row.width.val = (f.row i).width ∧ row.ordinal.val = f.table.ordinal f.row i ∧ g.LastWriteFields (H u).rows := by
  rw [f.ranges]
  let p := g.shared_range_fields (f.image u) f.allocated recBase ct em.rows hs ht
  let cols := tableRange_fields (f.image u) f.allocated (f.records u) (ct ▸ g.index_lt hs ht)
  exact ⟨Fin.ext p.1,cols.2.1,cols.2.2.1,cols.2.2.2.1,cols.2.2.2.2,
    Cube.SharedRows.Layout.LastWriteFields.of_scheduled (f.image u) f.allocated fit recBase ct em.rows⟩

/-- A co-located symbol pair gets the same single chronological guess in its
forward and reverse views. The width and the two addresses are the emitted ones. -/
theorem ReturnedDelivery.local_pair (f : Delivery) (g : Cube.SharedRows.Layout) (u : Fin (R+1))
    {src : ℕ → ℕ} (em : g.Emitted src (f.before u)) (fit : g.Fits w src)
    (recBase : f.table.records = g.records) (ct : f.table.count = g.dataCount+g.groups.choose 2)
    (room : g.banks+g.stride*g.groups^2 ≤ 2^w) {s t j : ℕ} (hs : s < t) (ht : t < g.groups)
    (first : (f.row (g.rowIndex s t)).first = u.val) (second : (f.row (g.rowIndex s t)).second = u.val)
    (inside : j < (f.row (g.rowIndex s t)).width) :
    let b := if (H u).bits (g.rowIndex s t) j then (1 : Word w) else 0
    (H u).history.val.2.2 (g.view s t+j) = b ∧ (H u).history.val.2.2 (g.view t s+j) = b := by
  let i := g.rowIndex s t
  let a := (H u).rows i
  obtain ⟨tag,ha,hb,hw,_,fields⟩ := shared_info f g u em fit recBase ct hs ht
  have self : (H u).team = a.teamA := Fin.ext ((f.bank u).team.trans (ha.trans first).symm)
  have same : a.teamA = a.teamB := Fin.ext ((ha.trans first).trans (hb.trans second).symm)
  have sel : a.selected (H u).team = some (some .sharedHere) := by
    change a.kind = 0 at tag
    rw [self]
    simp [Range.selected,Range.bank,decision,Decision.role,tag,same]
  have count := (f.fullCount u).trans ct
  apply (H u).local_shared
  · rw [count]; exact Cube.SharedRows.Layout.shared_lastWrite_A fields room _ hs ht sel (hw ▸ inside) (by decide)
  · rw [count]; exact Cube.SharedRows.Layout.shared_lastWrite_B fields room _ hs ht sel (hw ▸ inside) (by decide)

/-- Both ends of a remote pair read the *specified* shared exterior coordinate.
The relay and hop ordinal are computed from the public scheduler's prefix, and
both values are read from the returned RAM at their distinct ordered views. -/
theorem ReturnedDelivery.remote_pair (f : Delivery) (g : Cube.SharedRows.Layout) (u z : Fin (R+1))
    (different : u ≠ z) (src : Fin (R+1) → ℕ → ℕ) (em : ∀ v, g.Emitted (src v) (f.before v))
    (fit : ∀ v, g.Fits w (src v)) (recBase : f.table.records = g.records)
    (ct : f.table.count = g.dataCount+g.groups.choose 2) (room : g.banks+g.stride*g.groups^2 ≤ 2^w)
    {s t j : ℕ} (hs : s < t) (ht : t < g.groups) (first : (f.row (g.rowIndex s t)).first = u.val)
    (second : (f.row (g.rowIndex s t)).second = z.val) (inside : j < (f.row (g.rowIndex s t)).width) :
    let i := g.rowIndex s t
    let k := f.table.ordinal f.row i+j
    let v := Routing.relay L.three different k
    ∃ p : Hop L.three L.width u v, p.1 = z ∧ p.2.val = k ∧
      let val := Fin.ofNat (2^w) ((L.exteriorEquiv ext).hop u v p).toNat
      (H u).history.val.2.2 (g.view s t+j) = val ∧ (H z).history.val.2.2 (g.view t s+j) = val := by
  let i := g.rowIndex s t
  let a := (H u).rows i
  let b := (H z).rows i
  obtain ⟨tagA,ua,ub,uw,uo,uFields⟩ := shared_info f g u (em u) (fit u) recBase ct hs ht
  obtain ⟨tagB,za,zb,zw,zo,zFields⟩ := shared_info f g z (em z) (fit z) recBase ct hs ht
  have selfA : (H u).team = a.teamA := Fin.ext ((f.bank u).team.trans (ua.trans first).symm)
  have selfB : (H z).team = b.teamB := Fin.ext ((f.bank z).team.trans (zb.trans second).symm)
  have neA : a.teamA ≠ a.teamB := fun eq => different (Fin.ext ((ua.trans first).symm.trans ((congrArg Fin.val eq).trans (ub.trans second))))
  have neB : b.teamA ≠ b.teamB := fun eq => different (Fin.ext ((za.trans first).symm.trans ((congrArg Fin.val eq).trans (zb.trans second))))
  have selA : a.selected (H u).team = some (some .receiveA) := by
    change a.kind = 0 at tagA
    rw [selfA]; simp [Range.selected,Range.bank,decision,Decision.role,tagA,neA]
  have selB : b.selected (H z).team = some (some .receiveB) := by
    change b.kind = 0 at tagB
    rw [selfB]; simp [Range.selected,Range.bank,decision,Decision.role,tagB,neB.symm]
  have lw := Cube.SharedRows.Layout.shared_lastWrite_A uFields room _ hs ht selA (uw ▸ inside) (by decide)
  have rw' := Cube.SharedRows.Layout.shared_lastWrite_B zFields room _ hs ht selB (zw ▸ inside) (by decide)
  rw [← ct,← f.fullCount u] at lw
  rw [← ct,← f.fullCount z] at rw'
  let A := (f.bank u).bit (f.placed u) lw.row_lt selA lw.slot_lt.le
  let B := (f.bank z).bit (f.placed z) rw'.row_lt selB rw'.slot_lt.le
  let k := f.table.ordinal f.row i+j
  let v := Routing.relay L.three different k
  have lim : k < demand L.width u z := by
    let frame := G.transferFrame u L.header (f.bank u).initial.dst
    have span : ScheduledRange frame L.width a := by
      change ScheduledRange frame L.width ((H u).rows i)
      rw [f.ranges]
      exact f.widths.symm ▸ ScheduledRange.of_table (f.image u) f.allocated f.rowsFit (f.records u) frame f.teams
        (ct ▸ g.index_lt hs ht)
    have bound := span.demand neA
    have sa : (⟨a.teamA.val,span.first⟩ : Fin (R+1)) = u := Fin.ext (ua.trans first)
    have sb : (⟨a.teamB.val,span.second⟩ : Fin (R+1)) = z := Fin.ext (ub.trans second)
    change a.ordinal.val+a.width.val ≤ demand L.width ⟨a.teamA.val,_⟩ ⟨a.teamB.val,_⟩ at bound
    rw [sa,sb] at bound
    change a.ordinal.val = f.table.ordinal f.row i at uo
    change a.width.val = (f.row i).width at uw
    dsimp only [k]; rw [← uo]
    exact (Nat.add_lt_add_left (uw ▸ inside) _).trans_le bound
  let p : Hop L.three L.width u v := ⟨z,⟨k,by simp [v,pairBits,different,lim]⟩⟩
  let vv := Routing.relay L.three different (a.ordinal.val+j)
  have ordA : a.ordinal.val+j=k := congrArg (·+j) uo
  have rel : RelayWordAgrees (readings (f.relay vv).pub) (readings (f.relay vv).mem)
      u vv z ((a.ordinal.val+j)/(R+1-2)) := by
    dsimp only [vv]; rw [ordA]; exact f.checked u v p
  have wireEq := TransferBank.remote_shared different (H u) (H z) lw rw' A B (f.bank u).args rfl (f.bank z).args rfl
    (ub.trans second) (za.trans first) (uo.trans zo.symm) (ordA ▸ lim) (f.relay vv) rel
  have peek := A.read_source_hop f.word p
  have regs := sender_regs a (H u).team j (lw.slot_lt.trans a.width.isLt)
  have actual := (H u).readback lw
  change (H u).history.val.2.2 (g.view s t+j) = A.mem (endpointNat 10 (H u).pub (a.bitBank (H u).team j) A.mem) at actual
  have args : A.pub = (H u).pub := (f.bank u).args
  have own := A.schedule.frame.1
  have teams := A.schedule.frame.2.1
  change frameField (readings A.pub) (readings A.mem) 0 = u.val at own
  change frameField (readings A.pub) (readings A.mem) 1 = R+1 at teams
  have peerA : a.teamB.val = z.val := ub.trans second
  have addr : endpointNat 10 (H u).pub (a.bitBank (H u).team j) A.mem =
      routedAddress (readings A.pub) (readings A.mem) u v z (k/(R+1-2)) := by
    calc _ = endpointNat 10 A.pub (a.bitBank (H u).team j) A.mem :=
            congrArg (fun p => endpointNat 10 p (a.bitBank (H u).team j) A.mem) args.symm
         _ = _ := by simp only [endpointNat_eq,own,teams,regs.1,peerA,regs.2,ordA,endpointRelay_eq L.three different,v]
  rw [addr] at actual
  have value : (H u).history.val.2.2 (g.view s t+j) =
      Fin.ofNat (2^w) ((L.exteriorEquiv ext).hop u v p).toNat := by
    rw [actual]; apply Fin.ext
    exact peek.trans (Nat.mod_eq_of_lt ((Bool.toNat_lt _).trans_le (Nat.one_lt_pow f.word.ne' (by decide : 1<2)))).symm
  exact ⟨p,rfl,rfl,value,wireEq.symm.trans value⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
