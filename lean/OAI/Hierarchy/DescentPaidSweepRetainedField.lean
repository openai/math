import OAI.Hierarchy.DescentPaidSweepTargetPadding
import OAI.Hierarchy.DescentScalarVenueRaster
import OAI.Hierarchy.DescentNativeBankLookup

namespace OAI
/-! # Reading the original four-hop target names from the retained native ingress field -/
namespace Hierarchy.DescentScalarVenueMask.Raster
open DescentSIMDLookup DescentPackedZip DescentPackedActorMask DescentPackedColony
open DescentHaloWalkRAM DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames DescentOrdinaryRasterReturn
open DescentIssuedTerminalId ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section
variable {V : Type} [Fintype V] {H H' G M d r cap w raw : ℕ}
    (wide : H≤H') (host : V↪Fin H) (near : V→Fin d→Option V) (S : Shape (breadth d) r cap)
    (base k gain slots low : ℕ) (original : Fin r→Fin (1+cap*6)→Fin H→Fin G→Ticket (breadth d) raw)
    (t : Fin r→Fin (1+cap*6)→Fin H'→Fin G→Ticket (breadth d) raw) (hub : Fin H→Fin G→ Cell 1)
    (hub' : Fin H'→Fin G→ Cell 1)
local notation "up" => Fin.castLEEmb wide
local notation "actual" => Gather.reaching (hostRotor host near)
local notation "current" => Gather.reaching (hostRotor (host.trans up) near)
local notation "n₀" => H'*chunks G M
local notation "out" => output (breadth d) r cap raw low H' G M base
local notation "dest" => (Bank.mk out (Nat.clog 2 n₀))
local notation "state" => result S k gain slots raw low H' G M base

/-- A clipped entrance publishes these original bank reads before the signed stage. -/
theorem held_field_reads (field : Bank) (input now : Memory w)
    (printed : Reads field (fun h g=>encode (Packed.bits low) (actors (breadth d*r) cap)
      (fields current t hub' k gain slots low h g)) M input)
    (real : ∀x j h g,t x j (up h) g=original x j h g) (blank : ∀x j (h : Fin H') g,H≤h.val→t x j h g=none)
    (hubs : ∀h g,hub' (up h) g=hub h g) (fits : field.size<2^w) (capacity : n₀≤field.size)
    (preserved : ∀q<field.base+n₀,now q=input q) :
    Source (H:=H') (.lookup field .row) (fun h g=>encode (Packed.bits low) (actors (breadth d*r) cap)
      (fun j=>extend (fun v g=>fields actual original hub k gain slots low v g j) h g)) M now :=by
  intro s
  have pos:=(row H' G M s).isLt
  apply (lookup_nat field now _ .row (row H' G M s).val rfl (pos.trans_le capacity) fits).trans
  apply (preserved _ (Nat.add_lt_add_left pos field.base)).trans
  apply (printed s).trans
  apply congrArg (fun x : Fin H'→Fin G→ Cell ((Packed.bits low)*actors (breadth d*r) cap)=>((data x s).val:Word w))
  funext h g
  apply congrArg (encode (Packed.bits low) (actors (breadth d*r) cap))
  funext j
  exact padded_targets wide hub hub' k gain slots low host near original t real blank hubs h g j

theorem held_fields (old now : Memory w) (typed : Receiver.Raw S.ports S.route S.key S.hub S.ends base current t hub' M old)
    (real : ∀x j h g,t x j (up h) g=original x j h g) (blank : ∀x j (h : Fin H') g,H≤h.val→t x j h g=none)
    (hubs : ∀h g,hub' (up h) g=hub h g) (room : out+(dest).size<2^w)
    (preserved : ∀q<out+n₀,now q=state old q) :
    Source (H:=H') (.lookup dest .row) (fun h g=>encode (Packed.bits low) (actors (breadth d*r) cap)
      (fun j=>extend (fun v g=>fields actual original hub k gain slots low v g j) h g)) M now :=by
  have capRows : n₀≤(dest).size:=Nat.le_pow_clog (by decide) _
  have exactRows:=(run S k gain slots raw low H' G M base current t hub' old typed
    ((Nat.add_le_add_left capRows _).trans_lt room)).2.1
  intro s
  have pos:=(row H' G M s).isLt
  have read:=lookup_nat dest now ((row H' G M s).val:Word w) .row (row H' G M s).val rfl
    (pos.trans_le capRows) ((Nat.le_add_left ..).trans_lt room)
  apply read.trans
  apply (preserved _ (Nat.add_lt_add_left pos out)).trans
  apply (exactRows s).trans
  apply congrArg (fun x : Fin H'→Fin G→ Cell ((Packed.bits low)*actors (breadth d*r) cap)=>((data x s).val:Word w))
  funext h g
  apply congrArg (encode (Packed.bits low) (actors (breadth d*r) cap))
  funext j
  exact padded_targets wide hub hub' k gain slots low host near original t real blank hubs h g j

end
end Hierarchy.DescentScalarVenueMask.Raster

end OAI
