import OAI.Hierarchy.DescentPhysicalResetDate
import OAI.Hierarchy.DescentResetCanvasIngress
import OAI.Hierarchy.DescentStageVenueTail

namespace OAI
/-! The public reset starts on the preceding stage's measured atom and signed-incidence banks. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

variable (L : DescentResetCanvasIngress.Layout) (base : ℕ)

/-- Bind the real incoming signed banks to the actual Canvas header before issuing any instruction. -/
def atIngress (a : PhysicalReset) (blocks : a.k=L.k) (ports : a.c=2*L.cap) : PhysicalReset :=
  {a with previousToken:=fun j=>L.tokens base (j.1.cast (congrArg (2^·) blocks),j.2.cast ports)}

variable {w : ℕ} {a : PhysicalReset} (blocks : a.k=L.k) (ports : a.c=2*L.cap)
local notation "prepared" => atIngress L base a blocks ports
local notation "at₀" => L.endAddress base
variable (u : (atIngress L base a blocks ports).DateInputs (L.endAddress base) w) (z : u.FinalInputs)
variable (hubs : Bank) (atom : Fin (2^L.k)→Expr) (wire : L.signed.Slot→Bank)
local notation "enter" => L.phase base w hubs atom wire

def entered : DateCode w :=.reset
  ((enter).program.seq (u.throughOperands.seq z.tailCode))
  ((enter).ticks+(u.throughOperandTicks+z.tailTime))

/-- On every incoming tape this is one execution from the old graph up to the new role and arity banks. -/
theorem entered_any (_source : u.src=L.source base) (_sameHubs : u.hub=hubs)
    (safeHub : hubs.Fits w base) (safeAtom : ∀x,(atom x).Fits w base)
    (safeWire : ∀j,(wire j).Fits w base) (ingressFits : at₀<2^w)
    (ready : u.Ready) (room : z.Room) (m : Memory w) :
    ∃out : Memory w,(entered L base blocks ports u z hubs atom wire).Runs m out ∧
      (entered L base blocks ports u z hubs atom wire).cheap ∧
      ∀x,x<base ∨ (prepared).endAddress at₀≤x→ out x=m x := by
  obtain ⟨first,lower⟩:=L.any base hubs atom wire m safeHub safeAtom safeWire ingressFits
  obtain ⟨out,next,cheap,h⟩:=date_any z ready room ((enter).image m)
  have low : base≤at₀:=by obtain ⟨one,two,three⟩:=L.order base;exact one.trans (two.trans three)
  have high : at₀≤(prepared).endAddress at₀:=by
    obtain ⟨one,two,three⟩:=(prepared).occupied at₀;exact one.trans (two.trans three)
  exact ⟨out, @Procedure.Exec.then w (enter).program (u.throughOperands.seq z.tailCode) m ((enter).image m) out
    (enter).ticks (u.throughOperandTicks + z.tailTime) @first @next,
    @cheap_seq w (enter).program (u.throughOperands.seq z.tailCode) (enter).cheap @cheap, fun x side =>
    (h x (side.imp_left (·.trans_le low))).trans (lower x (side.imp_right (high.trans ·)))⟩

theorem entered_tariff :
    (entered L base blocks ports u z hubs atom wire).tariff=
      ((enter).ticks+7*DescentStaticWordColumn.names (enter).program)*w+(date z).tariff := by
  simp only [entered,date,DateCode.tariff,DateCode.ticks,DateCode.names,DescentStaticWordColumn.names_seq]
  ring

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
