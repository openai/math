import OAI.Hierarchy.DescentRetainedSevenLedger
import OAI.Hierarchy.DescentRetainedHomeMoverTariff

namespace OAI
/-! # Bit price of the measured chronological primitive mover -/

namespace Hierarchy.DescentRetainedHomeMover.Layout
open DescentCompiler DescentCompiler.TerminalScale DescentPlacedInvoiceVolume DescentDatedAddressBook DescentSIMDLookup
open DescentResetRetainedSetup DescentRetainedSeven Filter
noncomputable section
variable (z : DescentRetainedHomeMover.Layout)
local notation "V" => z.transfer
local notation "P" => z.placement

def pitches : Chart := ⟨z.transfer,z.placement,z.degree,z.cap,z.rootField,z.rootLanes⟩

def invoiceUnits :=
  (V).movementUnits+controlFactor z.shapes 7+printed ((V).channels+(V).nodes)+
    (stemFactor ((V).nodes*z.shapes) z.blocks z.queryBudget+suffixFactor z.shapes (V).nodes z.blocks)

/-- The receiver-dependent terms occur at the three separate genuine pitches.
The role lookup deck has exactly two pages for each input channel or new node. -/
theorem invoice_volume (floor w h : ℕ) (ap : z.pitches.Apertures h) :
    z.invoice floor w≤z.invoiceUnits*(z.pitches.packedMass h+1):=by
  let T:=z.pitches.packedMass h
  have lit:(h+1)^3*2^(h/2)≤T:=by dsimp [T,Chart.packedMass];omega
  have move:(V).movementFee floor w≤(V).movementUnits*(T+1):=
    ((V).movement_volume floor w h ap.movement).trans (Nat.mul_le_mul_left _ (by dsimp [T,Chart.packedMass,pitches];omega))
  have share:=DescentPlacedInvoiceVolume.control z.control h T 7 ap.packet ap.oldPitch ap.movement.newPitch
    ap.packetBits ap.selector ap.oldSelector (by dsimp [T,Chart.packedMass,pitches,Chart.control,control];omega)
    (by dsimp [T,Chart.packedMass,pitches,Chart.control,control];omega) lit
  have scan:ScanRoom z.placement z.batch h T:=
    ⟨ap.before,ap.after_,ap.blocks,ap.movement.newPitch,ap.newPitch,ap.oldWord,ap.newWord,
      by
        change z.placement.oldHosts*chunks (z.placement.groups*z.placement.blocks) z.transfer.decodedLanes ≤ T
        dsimp [T,Chart.packedMass,Chart.batch,pitches];omega,
      by dsimp [T,Chart.packedMass,pitches];omega,by dsimp [T,Chart.packedMass,pitches];omega,
      by dsimp [T,Chart.packedMass,pitches];omega,lit⟩
  have tar:=DescentPlacedInvoiceVolume.target z.placement z.batch h T z.queryBudget scan
  have page:2^(((V).stripWord*(V).channels+(V).stripWord)*(V).decodedLanes)≤T:=half_table ap.joined lit
  have table:DescentResetRetainedSetup.Layout.mountFee z.toLayout.bookWords≤printed ((V).channels+(V).nodes)*(T+1):=by
    dsimp only [DescentRetainedPrimitive.Layout.bookWords, DescentResetRetainedSetup.Layout.mountFee]
    calc _≤4+10*(((V).channels+(V).nodes)*(2*T))+7*(15*(((V).channels+(V).nodes)*(2*T)+1)):=by gcongr
         _≤_:=by unfold printed;ring_nf;omega
  change _≤((V).movementUnits+controlFactor z.shapes 7+printed ((V).channels+(V).nodes)+
    (stemFactor ((V).nodes*z.shapes) z.blocks z.queryBudget+suffixFactor z.shapes (V).nodes z.blocks))*(T+1)
  rw [Nat.add_mul,Nat.add_mul,Nat.add_mul]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add move share) table) tar

theorem native_invoice (floor w h cut k u oldUnit pkt successor ratio : ℕ)
    (ap : z.pitches.Apertures h) (g : (V).CalendarPitch cut k h u) (groups : (V).groups=2^cut)
    (host : 0<(V).hosts) (pos : 0<u) (old : 0<(V).previousLanes)
    (earlier : (V).groups≤(V).previousLanes ∨ h≤(V).previousLanes*oldUnit)
    (same : (P).oldHosts=(V).hosts) (split : (P).groups*(P).blocks=(V).groups)
    (before : (V).groups≤z.rootLanes*(P).blocks ∨ h≤z.rootLanes*pkt)
    (after_ : (P).groups≤(P).lanes ∨ h≤(P).lanes*successor) (word : w≤ratio*h) :
    z.invoice floor w*w≤z.invoiceUnits*ratio*z.pitches.rowBits h oldUnit u pkt successor:=by
  calc
    _≤(z.invoiceUnits*(z.pitches.packedMass h+1))*(ratio*h):=Nat.mul_le_mul (z.invoice_volume floor w h ap) word
    _=z.invoiceUnits*ratio*((z.pitches.packedMass h+1)*h):=by ring
    _≤_:=Nat.mul_le_mul_left _ (z.pitches.packed_bits g groups host pos old earlier same split ap.packet before
      ap.blocks ap.after_ after_)

theorem shared_invoice (rate saving : ℕ) :
    ∀ᶠ h:ℕ in atTop,∀ (z : DescentRetainedHomeMover.Layout) (J copies growth floor w cut k u oldUnit pkt successor ratio : ℕ),
      J≤Nat.log 2 h→2^h≤copies→z.invoiceUnits*ratio≤ scale J rate→z.placement.newHosts≤z.transfer.hosts*growth→z.placement.groups≤z.transfer.groups→
      z.pitches.Apertures h→z.transfer.CalendarPitch cut k h u→z.transfer.groups=2^cut→0<z.transfer.hosts→0<u→0<z.transfer.previousLanes→
      (z.transfer.groups≤z.transfer.previousLanes ∨ h≤z.transfer.previousLanes*oldUnit)→z.placement.oldHosts=z.transfer.hosts→z.placement.groups*z.placement.blocks=z.transfer.groups→
      (z.transfer.groups≤z.rootLanes*z.placement.blocks ∨ h≤z.rootLanes*pkt)→(z.placement.groups≤z.placement.lanes ∨ h≤z.placement.lanes*successor)→w≤ratio*h→
      z.invoice floor w*w≤z.transfer.hosts*h*(z.invoiceUnits*ratio*z.pitches.hostRate growth)+
        z.transfer.hosts*z.transfer.groups*(z.invoiceUnits*ratio*Chart.fieldRate growth oldUnit u pkt successor)+copies/(2^J)^saving:=by
  filter_upwards [global_control_shared 5 4 rate 1 saving] with h paid
  intro z J copies growth floor w cut k u oldUnit pkt successor ratio late ambient price hostRoom groupRoom ap pitch groups host
    positive old earlier same split before after_ word
  let K:=z.invoiceUnits*ratio
  have width:=z.native_invoice floor w h cut k u oldUnit pkt successor ratio ap pitch groups host positive old earlier
    same split before after_ word
  have raw:=z.pitches.row_invoice h growth oldUnit u pkt successor hostRoom groupRoom
  have literal:K*(5*(h+1)^4*2^(h/2))≤copies/(2^J)^saving:=calc
    _≤ scale J rate*(5*(h+1)^4*2^(h/2)):=Nat.mul_le_mul_right _ price
    _=(5*(h+1)^4*2^(rate*(J+1)))*2^(h/2):=by unfold scale;ring
    _≤_:=paid J (rate*(J+1)) copies late (by simp) ambient
  apply width.trans ((Nat.mul_le_mul_left K raw).trans ?_)
  calc
    _=z.transfer.hosts*h*(K*z.pitches.hostRate growth)+z.transfer.hosts*z.transfer.groups*
        (K*Chart.fieldRate growth oldUnit u pkt successor)+K*(5*(h+1)^4*2^(h/2)):=by
          dsimp only [pitches]
          ring
    _≤_:=Nat.add_le_add_left literal _

theorem scaled_invoice {ι : ℕ→Type*} {J : ℕ→ℕ} (z : ∀h,ι h→DescentRetainedHomeMover.Layout)
    (dimension : SmallAt J fun h i=>(z h i).transfer.high+(z h i).transfer.low)
    (prior : SmallAt J fun h i=>(z h i).transfer.previousNodes) (priorArgs : SmallAt J fun h i=>(z h i).transfer.previousArgs)
    (current : SmallAt J fun h i=>(z h i).transfer.nodes) (blocks : SmallAt J fun h i=>(z h i).transfer.blocks)
    (sheets : SmallAt J fun h i=>(z h i).blocks) (shapes : SmallAt J fun h i=>(z h i).shapes) :
    SmallAt J fun h i=>(z h i).invoiceUnits:=by
  let num (n : ℕ) := SmallAt.const (ι := ι) J n
  have motion := DescentRetainedSeven.scaled_movement (fun h i=>(z h i).transfer) dimension prior priorArgs blocks
  have channels := ((num 2).add ((num 7).mul priorArgs)).mul prior
  have query := (num 14).add (channels.mul (num 36))
  have factors := DescentRetainedSeven.scaled_tariff current sheets query shapes (num 7)
  have deck := (channels.add current).mul (num 2)
  have printed := ((num 4).add ((num 10).mul deck)).add ((num 7).mul ((num 15).mul (deck.add (num 1))))
  exact (((motion.add factors.1).add printed).add factors.2)

end
end Hierarchy.DescentRetainedHomeMover.Layout

end OAI
