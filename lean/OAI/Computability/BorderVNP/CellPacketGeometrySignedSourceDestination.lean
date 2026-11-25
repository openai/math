import OAI.Computability.BorderVNP.CellPacketGeometrySignedPlacements
import OAI.Computability.BorderVNP.PackedReportPrivateSlotBound

/-! # The numerical slot of a signed template reference at its native receiving cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing CellAddresses Directory Directory.PrivateBank RoutingISA
open scoped Classical

/-- Every native private destination consists of the supplied prefix, the report gap,
and the earlier original rows in this cell, even for an empty description. -/
theorem private_displacement {D C ne np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (edge : N.Edge ↪ Fin ne) (port : P ↪ Fin np)
    (dir : Directory.Layout) (host : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (gap : ℕ) (old : ℕ → ℕ) (names : ∀ i : Fin dir.entries, old i.val=(cell (host i)).val) (j : Fin dir.entries) :
    (destination N cell edge port dir host live gap (.inl j)).2 =
      suppliedSize N cell (cell (host j))+gap+PrivatePlacement.prefixCounts old dir.description j.val (cell (host j)).val := by
  let sc := Sum.elim (fun x : SuppliedWord N cell => x.1) (id : Fin C → Fin C)
  let sizes := Sum.elim (supplyWidth N cell) (fun _ : Fin C => gap)
  let key := reserveID (C:=C) (suppliedID N cell edge port)
  have placed := base_private sc (cell ∘ host) key sizes dir.description old names j
  have volume : DataSlabs.size sc sizes (cell (host j))=suppliedSize N cell (cell (host j))+gap := by
    rw [show DataSlabs.size sc sizes _=_ from reservedSize (fun x : SuppliedWord N cell => x.1)
      (supplyWidth N cell) gap (cell (host j)),dataSlabs_size]
  exact placed.trans (congrArg (· + _) volume)

end Packing.RoutingOutputs.NativeDemands

namespace CellPacketGeometry.History.Native.SignedFields

open Crossing Shortening.PublicCapacity Packing Packing.Inherited FrozenTape CellSparse CellSparse.Packet
open CellSparse.Packet.Source FinalReports SiteWords RoutingISA CellPacket
open Packing.CellAddresses Packing.CellAddressPhysical Packing.CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

/-- Reading an original reference through the genuine signed template gives the
absolute bank address computed from the named terminal network's native destination.
The address is independent of the saved history bus and scalar-reader payload. -/
theorem template_native_destination {s : Shape} {n C d k w t D a : ℕ} {Z H R B I P : Type}
    [Fintype Z] [Fintype H] [Fintype R] [Fintype B] [Fintype P] {bits : P → ℕ}
    (dir : Directory.Layout) (F : Fields s.sites s.edges n C d k w Z) (occupied : Fin s.edges → Z)
    (portUsed : Fin n → Bool) (boxes : Fin s.sites → List (Source.Box (Fin dir.entries)))
    (bus : Frame (Z ⊕ H) (FrozenTape.Pins R B t)) (entry : Fin dir.entries → Fin s.sites)
    (arena stride gap g digits : ℕ) (valid : Z) (z : Z → Bool) (saved : H → Bool)
    (T : LiveWords.Template (Spare.Field C g digits (Fin dir.entries)) I (Fin dir.entries) a (C+1))
    (read : Fin a → I → ℕ) (N : Network D P bits) (cell : N.Site → Fin C) (state : N.Site → Site)
    (sid : N.Site ↪ Fin s.sites) (eid : N.Edge ↪ Fin s.edges) (pid : P ↪ Fin n)
    (phys : Represents N cell (fun v => (state v).size) sid eid pid F z)
    (sizes : ∀ c, guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c<2^w)
    (host : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (names : ∀ j, entry j=sid (host j)) (fits : arena+C*stride<2^w)
    (extents : ∀ c : Fin C, Nat.le (suppliedSize N cell c+gap+dir.entries*dir.description) stride) (j : Fin dir.entries) :
    let packet := liveFrame F boxes entry arena stride gap dir.description g digits
    let args := (Terminal.feeds (s:=s) F occupied portUsed boxes bus packet valid).arguments (Sum.elim z saved)
    T.arguments args read (.inl (.inr j)) =
      arena+(cell (host j)).val*stride+(RoutingOutputs.NativeDemands.destination N cell eid pid dir host live gap (.inl j)).2 := by
  intro packet args
  let c := cell (host j)
  let old := fun i : ℕ => if h : i<dir.entries then (cell (host ⟨i,h⟩)).val else 0
  have owners (i : Fin dir.entries) : old i.val=(cell (host i)).val := dite_eq_left i.isLt
  have displacement := RoutingOutputs.NativeDemands.private_displacement N cell eid pid dir host live gap old owners j
  have interval := RoutingOutputs.NativeDemands.private_description_interval N cell eid pid dir host live gap j
  have offset : (RoutingOutputs.NativeDemands.destination N cell eid pid dir host live gap (.inl j)).2 ≤ stride :=
    (Nat.le_add_right ..).trans (interval.2.trans (extents c))
  have endWord := Nat.mul_le_mul_right stride (show c.val+1≤C from c.isLt)
  rw [Nat.succ_mul] at endWord
  have limit : arena+stride*c.val+suppliedSize N cell c+gap+PrivatePlacement.prefixCounts old dir.description j.val c.val<2^w := by
    rw [Nat.mul_comm stride c.val]
    change (RoutingOutputs.NativeDemands.destination N cell eid pid dir host live gap (.inl j)).2 =
      suppliedSize N cell c+gap+PrivatePlacement.prefixCounts old dir.description j.val c.val at displacement
    omega
  have strideBound : stride < 2^w := (Nat.le_mul_of_pos_left stride (Nat.zero_lt_of_lt c.isLt)).trans_lt
    ((Nat.le_add_left ..).trans_lt fits)
  have volume : dir.entries*dir.description<2^w :=
    ((Nat.le_add_left ..).trans (extents c)).trans_lt strideBound
  have len : dir.description≤dir.entries*dir.description := Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt j.isLt)
  have mask (u : Fin C) : (∑ i : Fin dir.entries, if cell (host i)=u then dir.description else 0)<2^w := by
    have bound : (∑ i : Fin dir.entries, if cell (host i)=u then dir.description else 0) ≤ dir.entries*dir.description := by
      calc
        _ ≤ ∑ _ : Fin dir.entries, dir.description := Finset.sum_le_sum fun i _ => by split <;> simp
        _ = _ := by simp
    exact bound.trans_lt volume
  have atSlot := pointer_read F boxes entry arena stride gap dir.description g digits N cell state sid eid pid z phys
    sizes host names old owners (len.trans_lt volume) mask j limit
  refine (sourcePointer F occupied portUsed boxes bus entry arena stride gap dir.description g digits valid z saved T read j).trans
    (atSlot.trans ?_)
  rw [displacement]
  simp only [Nat.mul_comm stride (cell (host j)).val,Nat.add_assoc]

end CellPacketGeometry.History.Native.SignedFields

end BorderVNP
end Computability
end OAI
