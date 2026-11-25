import OAI.Hierarchy.DescentRetainedSevenTariff
import OAI.Hierarchy.DescentRetainedMovementBits
import OAI.Hierarchy.DescentPrimitiveVolumeTariff

namespace OAI
/-! # End-to-end packed-row cost of issuing the seven retained operand fields -/
namespace Hierarchy.DescentRetainedSeven.Chart
open DescentPlacedInvoiceVolume DescentResetRetainedSetup DescentSIMDLookup
open DescentStaticWordColumn (names)
noncomputable section
variable (c : DescentRetainedSeven.Chart)
local notation "L" => c.retained
local notation "S" => c.control
local notation "P" => c.placement

def units (readWork : ℕ) := (L).movementUnits+controlFactor (S).targets readWork+
  Layout.mountFee ((L).channels+1)+Layout.mountFee (L).outputs+
  (stemFactor (c.batch.fields*(P).shapes) (P).blocks c.queryBudget+
   suffixFactor (P).shapes c.batch.fields (P).blocks)

def packedMass (h : ℕ) :=
  (L).movementMass h+((S).hosts*chunks (S).groups (S).oldLanes+(S).hosts*chunks (S).groups (S).lanes)+
  ((P).oldHosts*chunks ((P).groups*(P).blocks) c.batch.inputLanes+
    (P).oldHosts*chunks (P).groups (P).lanes+(P).oldHosts+(P).rows)+(h+1)^3*2^(h/2)

/-- The clock runs with these same numerical aperture conditions on all values. -/
structure Apertures (h : ℕ) : Prop where
  movement : (L).MovementAperture h
  packet : 0<(S).oldLanes
  oldPitch : (S).oldLanes≤h
  packetBits : (S).rootWidth*(S).oldLanes≤h/2
  selector : (S).aperture*(S).lanes≤h/2
  oldSelector : (S).selectorBits*(S).oldLanes≤h/2
  joined : ((L).siteWord+(L).stripWord)*(L).decodedLanes≤h/2
  before : 0<c.batch.inputLanes
  after_ : 0<(P).lanes
  blocks : 0<(P).blocks
  newPitch : (P).lanes*(P).blocks≤h
  oldWord : c.batch.bits*c.batch.inputLanes≤h/2
  newWord : c.batch.bits*(P).blocks*(P).lanes≤h/2

private theorem mountedLookupPrice {q n h T : ℕ} (bits : n≤h/2) (table : (h+1)^3*2^(h/2)≤T) :
    Layout.mountFee (q*2^n)≤Layout.mountFee q*(T+1):=by
  have page:=half_table bits table
  calc _ ≤ 4+10*(q*T)+7*(15*(q*T+1)):=by unfold Layout.mountFee;gcongr
       _ ≤ _ :=by unfold Layout.mountFee;ring_nf;omega

theorem invoice_volume (floor w h U : ℕ) (ap : c.Apertures h) :
    c.invoice floor w U≤c.units U*(c.packedMass h+1):=by
  let T:=c.packedMass h
  have t:(h+1)^3*2^(h/2)≤T:=by dsimp [T,packedMass];omega
  have source : (L).movementMass h≤T+1:=by dsimp [T,packedMass];omega
  have move:=((L).movement_volume floor w h ap.movement).trans (Nat.mul_le_mul_left _ source)
  have share:=DescentPlacedInvoiceVolume.control (S) h T U ap.packet ap.oldPitch ap.movement.newPitch ap.packetBits ap.selector
    ap.oldSelector (by dsimp [T,packedMass];omega) (by dsimp [T,packedMass];omega) t
  have scan : ScanRoom (P) c.batch h T:=
    ⟨ap.before,ap.after_,ap.blocks,ap.movement.newPitch,ap.newPitch,ap.oldWord,ap.newWord,
      by dsimp [T,packedMass];omega,by dsimp [T,packedMass];omega,
      by dsimp [T,packedMass];omega,by dsimp [T,packedMass];omega,t⟩
  have place:=DescentPlacedInvoiceVolume.target (P) c.batch h T c.queryBudget scan
  have first:=mountedLookupPrice (q:=(L).channels+1) ap.joined t
  have less : (L).siteWord*(L).decodedLanes≤h/2:=
    (Nat.mul_le_mul_right _ (Nat.le_add_right (L).siteWord (L).stripWord)).trans ap.joined
  have last:=mountedLookupPrice (q:=(L).outputs) less t
  change c.invoice floor w U≤c.units U*(T+1)
  have total := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add move share) first) last) place
  apply total.trans_eq
  unfold units
  ring

/-- The actual conditional program and its data-independent clock, with the
source, permutation, comparator packet, and compact-directory operands supplied. -/
theorem native_volume (floor w h U : ℕ) (which : c.control.Targets) (keep : Fin c.placement.shapes→Bool)
    (old : Fin (L).sources→ProtocolRAM.Bank) (saved : ProtocolRAM.Bank) (packet : ProtocolRAM.Expr)
    (cnt inv : ProtocolRAM.Bank) (work : packet.work≤U) (ap : c.Apertures h)
    (prior : 0<(L).previousLanes) (gather : 0<(L).gatherLanes) (matrix : 0<(L).matrixLanes) :
    c.ticks floor w which old saved packet cnt inv+7*names (c.program floor w which keep old saved packet cnt inv)≤
      c.units U*(c.packedMass h+1) :=
  (c.price floor w which keep old saved packet cnt inv U work prior gather matrix ap.before ap.packet ap.blocks ap.after_).trans
    (c.invoice_volume floor w h U ap)

end
end Hierarchy.DescentRetainedSeven.Chart

end OAI
