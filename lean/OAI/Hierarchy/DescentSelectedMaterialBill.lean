import OAI.Hierarchy.DescentMaterialDateBill
import OAI.Hierarchy.DescentMaterialPopulation
import OAI.Hierarchy.DescentSelectedSignedRates
import OAI.Hierarchy.DescentSelectedMaterialRates

namespace OAI
/-! # Word cost of the actual previous header and full fifteen-field signed-material emitter -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook DescentHostDegree DescentRawCablePanel
open DescentSIMDLookup ProtocolRAM DescentStaticWordColumn
noncomputable section
variable {F : Type} [Field F]

private theorem selected_material_rate {P : Type} {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
    {S : AtomSchedule} {price u ε : ℝ} {k i z z' D D' wire hist : ℕ}
    {W : MarkedWorld F d P bits} {prior : Reached W G price ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {p : (T.result he).Choice}
    {n : Normalize ((T.result he).state p)} {next : Reached n.result G price ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink prior he T p n next) {t f gain reset J M tail : ℕ}
    (calendar : S=stageNumbers G t J f gain reset M tail)
    (radix : k=groupBits t J (hostRate t reset) (capRate G t gain) (cutRate t f gain)) :
    let D₀:=prior.placement.degree
    let cap:=prior.placement.cap
    let U:=donorAmount k D₀ cap G.b G.C G.k
    MaterialProgram.materialFactor D₀ (2^k) (15*(2^k*cap*11)) U≤ scale J (materialRate G t f gain reset) := by
  subst S
  have degree:=ticket.degree_limit
  have age:i≤(t+1)*J:=ticket.hubRows.choose.le
  have cap:=prior.valid.capacity.trans (Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
    (Nat.add_le_add_left (Nat.mul_le_mul_left (capRate G t gain) age) 8))
  have cut:=(material_rates G t f gain reset).choose_spec J _ _ degree cap
  rw [←radix] at cut
  exact cut

namespace PhysicalOrdinary
variable {P : Type} (v : PhysicalOrdinary F P)

theorem selected_material_bill {t f g reset J M tail : ℕ}
    (calendar : v.schedule=stageNumbers v.gadget t J f g reset M tail)
    (radix : v.k=groupBits t J (hostRate t reset) (capRate v.gadget t g) (cutRate t f g))
    (short : v.short=max (v.k+3) (Nat.clog 2 (v.prior.placement.degree+1)))
    (profile : v.profile=DescentTerminalEpochBits.width v.gadget.C)
    (capacity : 256≤v.prior.placement.cap) (floor w ratio : ℕ) (parts adj : Bank)
    (oldRoom : 2*scale J (donorRates v.gadget t f g reset).amount≤v.payload)
    (newRoom : 2*scale J (signedRates v.gadget t f g reset).amount≤v.payload)
    (machine : w≤ratio*v.payload) :
    let h:=v.payload
    let H:=v.area.H
    let K:=v.venue.hosts
    let G:=v.schedule.groupCount v.age
    let G':=v.schedule.groupCount (v.age+1)
    let u:=scale J (donorRates v.gadget t f g reset).amount
    let u':=scale J (signedRates v.gadget t f g reset).amount
    let phase:=v.withIssuedSigned.beforeSignedMaterial floor parts adj w
    (phase.ticks+7*names phase.program)*w≤
      11*ratio*scale J (materialRate v.gadget t f g reset)*MaterialProgram.population H K G G' h u u' := by
  let U:=v.ticket.installedDonorWidth v.short v.profile
  let U':=v.signedLayout.unit
  let D:=v.prior.placement.degree
  let caps:=v.prior.placement.cap
  let fieldCount:=15*(2^v.k*caps*11)
  let coeff:=MaterialProgram.materialFactor D (2^v.k) fieldCount U
  let r:=materialRate v.gadget t f g reset
  let oldPay:=scale J (donorRates v.gadget t f g reset).amount
  let newPay:=scale J (signedRates v.gadget t f g reset).amount
  have eqU : U=donorAmount v.k D caps v.gadget.b v.gadget.C v.gadget.k:=by
    dsimp only [U]
    rw [short,profile]
    exact selected_amount v.ticket
  have fee : coeff ≤ scale J r:=by
    dsimp only [coeff];rw [eqU]
    exact selected_material_rate v.ticket calendar radix
  have oldPrice : U≤oldPay:=eqU.le.trans (selected_input_bounds v.ticket calendar radix
    (donorRates v.gadget t f g reset).bounds).2
  have newPrice : U'≤newPay:=(v.ticket.selected_signed_rates calendar radix v.area.H v.venue.hosts
    (v.schedule.groupCount (v.age+1)) v.payload).1
  have oldWide : 2*U≤v.payload:=(Nat.mul_le_mul_left 2 oldPrice).trans oldRoom
  have newWide : 2*U'≤v.payload:=(Nat.mul_le_mul_left 2 newPrice).trans newRoom
  have pos : 0<U:=by
    have bound:2*DepotRAM.totalBits (v.ticket.depotShape v.short)+1≤U:=
      (v.ticket.installed_donor_widths v.short v.profile).2.2
    omega
  let H:=v.area.H
  let K:=v.venue.hosts
  let G:=v.schedule.groupCount v.age
  let G':=v.schedule.groupCount (v.age+1)
  let h:=v.payload
  let R:=MaterialProgram.scanVolume H K G G' (lanes h U) (lanes h U') (2^v.k) h
  have paid:=v.material_date_bill floor w ratio parts adj capacity oldWide newWide machine
  have slots : R*h≤11*MaterialProgram.population H K G G' h U U':=
    MaterialProgram.scan_volume_paid H K G G' h U U' (2^v.k) pos v.signedLayout.positive oldWide newWide (Nat.two_pow_pos _)
  have cells : MaterialProgram.population H K G G' h U U'≤ MaterialProgram.population H K G G' h oldPay newPay:=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add oldPrice newPrice)) _
  refine paid.trans ?_
  change coeff*R*(ratio*h)≤11*ratio*scale J r*MaterialProgram.population H K G G' h oldPay newPay
  calc
    _ = ratio*coeff*(R*h) :=by ring
    _ ≤ (ratio*scale J r)*(11*MaterialProgram.population H K G G' h oldPay newPay) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left ratio fee) (slots.trans (Nat.mul_le_mul_left 11 cells))
    _ = _ :=by ring

end PhysicalOrdinary
end
end Hierarchy.DescentSixParty.Chronology

end OAI
