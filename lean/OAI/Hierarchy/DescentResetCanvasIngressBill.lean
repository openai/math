import OAI.Hierarchy.DescentResetSignedTokenFees
import OAI.Hierarchy.DescentVenueExprTariff
import OAI.Hierarchy.DescentResetCanvasIngress

namespace OAI
namespace Hierarchy
open DescentSIMDLookup DescentPackedColony DescentSixParty.Chronology ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentStaticWordColumn (names names_seq names_mount names_scan)
noncomputable section
namespace DescentResetCanvasAmount.Layout
variable (s : DescentResetCanvasAmount.Layout)

/-- Two immutable mounts and the one pass forming the weighted group words. -/
def bill :=
  let lut:=s.number*2^(s.unitBits*s.lanes)
  let body:=1+s.number*28
  (4+10*s.rows+7*(15*(s.rows+1))) + (4+10*lut+7*(15*(lut+1))) +
  (4+s.rows*(2*body+4)+7*(11+4*body))

theorem price (base w : ℕ) (hubs : Bank) (atom : Fin s.blocks→Bank) (wire : s.Slot→Bank) :
    (s.phase base w hubs atom wire).ticks+7*names (s.phase base w hubs atom wire).program≤ s.bill := by
  let u := s.unitBits
  let src := s.input base hubs atom wire ∘ s.order.symm
  let bits := s.field ∘ s.order.symm
  let f := fun j=>s.contribution (s.order.symm j)
  let body := DescentPackedColumnSum.reads (s.table base) u s.lanes bits src
  have bound (j:s.Key) : (s.input base hubs atom wire j).work≤22 := by
    cases j with
    | inl x=>exact (by decide : 7 ≤ 22)
    | inr pair=>
      rcases pair with ⟨p,i⟩
      by_cases zero:i=0 <;> simp [input,recorded,zero,Expr.work]
  have work : body.work≤1+s.number*28:=DescentPackedColumnSum.work_le _ _ _ bits src 22 (fun _=>bound _)
  have loop:=Nat.mul_le_mul_left s.rows (Nat.add_le_add_right (Nat.mul_le_mul_left 2 work) 4)
  change ((4+10*s.rows)+DescentPackedColumnSum.ticks (s.table base) u s.lanes s.hosts s.groups bits src)+
    7*names ((DescentStaticWordColumn.program w base s.hostId s.rows).seq
      (DescentPackedColumnSum.program w (s.table base) (s.amount base).base u s.lanes
        (s.bits*s.blocks) s.hosts s.groups bits f src))≤_
  rw [DescentPackedColumnSum.program,names_seq,names_seq,names_mount,names_mount,names_scan]
  change ((4+10*s.rows)+((4+10*(s.number*2^(u*s.lanes)))+(4+s.rows*(2*body.work+4))))+
    7*(15*(s.rows+1)+(15*(s.number*2^(u*s.lanes)+1)+(11+4*body.work)))≤_
  unfold bill
  change _≤(4+10*s.rows+7*(15*(s.rows+1)))+(4+10*(s.number*2^(u*s.lanes))+7*(15*(s.number*2^(u*s.lanes)+1)))+
    (4+s.rows*(2*(1+s.number*28)+4)+7*(11+4*(1+s.number*28)))
  omega
end DescentResetCanvasAmount.Layout

namespace DescentResetCanvasIngress.Layout
variable (s : DescentResetCanvasIngress.Layout)
def bill (atomWork : ℕ) := s.signed.fees + DescentVenueSlabs.ExprInputs.tariff s.amounts atomWork + s.collector.bill

theorem price (base w atomWork : ℕ) (hubs : Bank) (atom : Fin (2^s.k)→Expr) (ports : s.signed.Slot→Bank)
    (cost : ∀x,(atom x).work≤atomWork) (old : 0<s.sourceLanes) (next : 0<s.targetLanes) :
    (s.phase base w hubs atom ports).ticks+7*names (s.phase base w hubs atom ports).program≤ s.bill atomWork := by
  have signed:=s.signed.price base w ports old next
  have atoms:=DescentVenueSlabs.ExprInputs.price s.amounts atom (s.signedEnd base) w atomWork cost old next
  have amount:=s.collector.price (s.atomEnd base) w hubs (s.atomBank base) (s.signed.raw base)
  change ((s.signed.phase base w ports).ticks+DescentVenueSlabs.ExprInputs.ticks s.amounts atom (s.signedEnd base)+
    (s.collector.phase (s.atomEnd base) w hubs (s.atomBank base) (s.signed.raw base)).ticks)+7*names
    ((((s.signed.phase base w ports).program).seq (DescentVenueSlabs.ExprInputs.program s.amounts atom (s.signedEnd base) w)).seq
      (s.collector.phase (s.atomEnd base) w hubs (s.atomBank base) (s.signed.raw base)).program)≤_
  rw [names_seq,names_seq,bill]
  omega
end DescentResetCanvasIngress.Layout
end
end Hierarchy

end OAI
