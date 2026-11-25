import OAI.Hierarchy.DescentOrdinaryFinal
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Reading the committed ordinary operand books at their physical addresses -/
namespace Hierarchy.DescentOrdinaryFinal.Chart
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOperandStateBanks ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (B : DescentOrdinaryFinal.Chart)
def Values := ∀_p : Fin B.outputs,Fin B.layout.blocks→(i : Fin B.inputs)→
  Fin B.layout.hosts→Fin B.layout.groups→Cell (B.widths (B.kind i))
def dataAt (V : B.Values) (p : Fin B.outputs) (x : Fin B.layout.blocks) (h : Fin B.layout.hosts)
    (g : Fin B.layout.groups) : B.Input:=fun i=>(V p x i h g).val

theorem issued {w} (s : B.Sources) (floor : ℕ) (m : Memory w) (early : B.Early s floor w)
    (room : B.endAddress floor<2^w) (v : B.Values)
    (source : ∀p x i,Reads (B.sourceBank s p x i) (v p x i) B.layout.lanes m)
    (x : Fin B.layout.blocks) (p : Fin B.outputs) :
    Reads (B.bank floor x p) (fun h g=>B.law p (B.dataAt v p x h g)) B.layout.lanes (B.image s floor m) :=by
  obtain ⟨one,two,three⟩:=B.order floor
  have cap:=(Nat.le_add_right (B.out floor) (B.passes*B.rows)).trans three
  have convert (i : Fin B.inputs) :=DescentOperandInputCast.issued B.widths B.scalarWidth B.scalarWidth
    B.layout.lanes floor (B.kind i) (B.raw s p x i) m (v p x i) B.widths_le
    (show (B.raw s p x i).Fits w floor from ⟨(early p x i).1,trivial⟩)
    (source_column _ floor (early p x i).1 m _ (early p x i).2 (source p x i))
    ((two.trans cap).trans_lt room)
  have built:=DescentOperandFamilyBook.issued B.law B.zero B.layout.lanes (B.castEnd floor) p
    (B.castArg s floor p x) (B.castImage floor m) (B.dataAt v p x)
    (fun i=>(convert i).1) (fun i=>(convert i).2) (cap.trans_lt room)
  have scan:=DescentPackedFlowBatch.execute (B.out floor) B.rows B.rows B.passes (B.expr s floor)
    (B.mounted floor m) (B.expr_fits s floor m early room) (three.trans_lt room) le_rfl
  let z:=B.address (p,x)
  have loc : z.val=p.val*B.layout.blocks+x.val:=by
    simp [z,address,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  intro r
  have actual:=scan.2.1 z (row B.layout.hosts B.layout.groups B.layout.lanes r)
  have term : B.expr s floor z.val=
      DescentOperandFamilyBook.expr B.law B.layout.lanes (B.castEnd floor) p (B.castArg s floor p x):=by
    rw [expr, dite_eq_left (show z.val < B.passes from z.isLt)]
    change DescentOperandFamilyBook.expr B.law B.layout.lanes (B.castEnd floor)
      (B.address.symm (B.address (p,x))).1
      (B.castArg s floor (B.address.symm (B.address (p,x))).1 (B.address.symm (B.address (p,x))).2) = _
    rw [B.address.symm_apply_apply]
  rw [term] at actual
  have written:=actual.trans (built.2 r)
  simpa only [image,scans,bank,DescentDatedPriorOperand.previousBank,loc,rows,Nat.add_mul,Nat.mul_assoc,Nat.add_assoc]
    using written

theorem placed {w} (floor : ℕ) (x : Fin B.layout.blocks) (p : Fin B.outputs)
    (room : B.endAddress floor<2^w) : (B.bank floor x p).Fits w (B.endAddress floor) ∧
    B.rows≤(B.bank floor x p).size:=by
  let z:=B.address (p,x)
  have h:=z.isLt
  have loc : z.val=p.val*B.layout.blocks+x.val:=by
    simp [z,address,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  have position : z.val*B.rows≤B.passes*B.rows :=
    Nat.mul_le_mul_right B.rows (Nat.le_of_lt h)
  rw [loc,Nat.add_mul,Nat.mul_assoc] at position
  have bound : (B.bank floor x p).base+(B.bank floor x p).size≤B.endAddress floor:=by
    change B.out floor+p.val*(B.layout.blocks*B.rows)+x.val*B.rows+2^Nat.clog 2 (B.rows+1) ≤
      B.out floor+B.passes*B.rows+2^Nat.clog 2 (B.rows+1)
    apply Nat.add_le_add_right
    simpa only [Nat.add_assoc] using Nat.add_le_add_left position (B.out floor)
  have positive : 0<(B.bank floor x p).size:=Nat.two_pow_pos _
  exact ⟨⟨positive,(Nat.le_add_left ..).trans_lt (bound.trans_lt room),bound⟩,
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)⟩

end
end Hierarchy.DescentOrdinaryFinal.Chart

end OAI
