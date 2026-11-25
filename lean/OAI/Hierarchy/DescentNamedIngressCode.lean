import OAI.Hierarchy.DescentFixedResetDate
import OAI.Hierarchy.DescentNamedResetOutput

namespace OAI
/-! # The published reset reuses precisely the signed banks written by ingress -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentPacking.PackedMatch.Local.Stage DescentSixParty DescentCompiler DescentSIMDLookup DescentPackedWalsh ProtocolRAM
open DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {w : ℕ} (L : DescentResetCanvasIngress.Layout) (floor : ℕ)

/-- The actual ingress instructions followed by the original, dated reset body. -/
def enterCode {a : PhysicalReset} (u : a.DateInputs (L.endAddress floor) w) (z : u.FinalInputs)
    (io : Dated.Operands) : DateCode w :=
  let initial:= L.phase floor w io.hubs (fun x=>io.atoms x.val) (fun j=>io.wire j.1.val j.2.val)
  .reset (initial.program.seq (u.throughOperands.seq z.tailCode))
    (initial.ticks+(u.throughOperandTicks+z.tailTime))

theorem enterCode_any {a : PhysicalReset} (u : a.DateInputs (L.endAddress floor) w) (z : u.FinalInputs)
    (io : Dated.Operands) (hubs : io.hubs.Fits w floor)
    (atoms : ∀x : Fin (2^L.k),(io.atoms x.val).Fits w floor)
    (wires : ∀j : L.signed.Slot,(io.wire j.1.val j.2.val).Fits w floor)
    (fits : L.endAddress floor<2^w) (ready : u.Ready) (room : z.Room) (m : Memory w) :
    ∃out : Memory w,(enterCode L floor u z io).Runs m out ∧ (enterCode L floor u z io).cheap ∧
      ∀i,i<floor ∨ a.endAddress (L.endAddress floor)≤ i→ out i=m i :=by
  let e:=L.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)
  obtain ⟨first,preserve⟩:=L.any floor io.hubs _ _ m hubs atoms wires fits
  obtain ⟨out,second,cheap,last⟩:=date_any z ready room (e.image m)
  have low : floor≤L.endAddress floor:=by obtain ⟨a,b,c⟩:=L.order floor;exact a.trans (b.trans c)
  have high : L.endAddress floor≤a.endAddress (L.endAddress floor):=by
    obtain ⟨one,two,three⟩:=a.occupied (L.endAddress floor);exact one.trans (two.trans three)
  exact ⟨out, @Procedure.Exec.then w e.program (u.throughOperands.seq z.tailCode) m (e.image m) out
    e.ticks (u.throughOperandTicks + z.tailTime) @first @second,
    @cheap_seq w e.program (u.throughOperands.seq z.tailCode) e.cheap @cheap, fun i hi =>
    (last i (hi.imp_left (·.trans_le low))).trans (preserve i (hi.imp_right (high.trans ·)))⟩

theorem enterCode_price {a : PhysicalReset} (u : a.DateInputs (L.endAddress floor) w) (z : u.FinalInputs)
    (io : Dated.Operands) :
    let e:=L.phase floor w io.hubs (fun x=>io.atoms x.val) (fun j=>io.wire j.1.val j.2.val)
    (enterCode L floor u z io).tariff=(e.ticks+7*DescentStaticWordColumn.names e.program)*w+(date z).tariff :=by
  simp only [enterCode,date,DateCode.tariff,DateCode.ticks,DateCode.names,DescentStaticWordColumn.names_seq]
  ring

theorem enterCode_issued {original a : PhysicalReset} (hk : original.k=L.k)
    (hc : original.c=2*L.cap) (installed : a=atIngress L floor original hk hc)
    (u : a.DateInputs (L.endAddress floor) w) (z : u.FinalInputs) (io : Dated.Operands) :
    ∃ (inputs : (atIngress L floor original hk hc).DateInputs (L.endAddress floor) w) (finish : inputs.FinalInputs),
      HEq u inputs ∧ HEq z finish ∧ enterCode L floor u z io=entered L floor hk hc inputs finish
        io.hubs (fun x=>io.atoms x.val) (fun j=>io.wire j.1.val j.2.val) := by
  subst a
  exact ⟨u,z,HEq.rfl,HEq.rfl,rfl⟩

private theorem bind_existing (a : PhysicalReset) (hk : a.k=L.k) (hc : a.c=2*L.cap)
    (bound : ∀j,a.previousToken j=L.tokens floor (j.1.cast (congrArg (2^·) hk),j.2.cast hc)) :
    a=atIngress L floor a hk hc :=by
  have same:=funext bound
  unfold atIngress
  conv_rhs => rw [←same]

variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
    (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
    (io : Dated.Operands)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "cap" => ((capCalendar G.b S.rounds g S.height).take age).prod*256

theorem named_ingress_token (j : Fin (2^(a).k)×Fin (a).c) :
    (a).previousToken j=(a).ingress.tokens floor (j.1.cast (by rfl),j.2.cast (by rfl)) := by
  have hx : j.1.val<2^k :=j.1.isLt
  have hp : j.2.val<2*cap :=j.2.isLt
  change (if h₁ : j.1.val<2^k then if h₂ : j.2.val<2*cap then
    (a).ingress.tokens floor (⟨j.1.val,h₁⟩,⟨j.2.val,h₂⟩) else _ else _)=_
  rw [dite_eq_left hx, dite_eq_left hp]
  rfl

theorem named_ingress_bound : (a)=atIngress (a).ingress floor (a) rfl rfl :=
  bind_existing (a).ingress floor (a) rfl rfl (named_ingress_token floor G S board k tail age p f g drift degree
    payload e previous M nextM C packet oldLanes primitiveLanes printedBits venue io)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
