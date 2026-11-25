import OAI.Hierarchy.DescentResetPrimitiveCheckpoint
import OAI.Hierarchy.DescentResetNodeTariff

namespace OAI
/-! # Instruction and clock bills for the global reset primitive strip -/
namespace Hierarchy.DescentResetPrimitiveCheckpoint.Shape
open DescentSIMDLookup DescentPackedZip DescentSixParty DescentPrimitivePalette DescentStaticWordColumn ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (s Z : ℕ) (op : RotorSpec)
variable (v : DescentResetPrimitiveCheckpoint.Shape) {w : ℕ}
local notation "c" => v.chart
def operandWork (B : ℕ) :=3*B+26
def clockBound (B : ℕ) :=DescentResetPrimitivePage.clock v.rawBits (c).lanes+
  (4+((c).blocks*(c).nodes)*(4+(c).rows*(2*operandWork B+4)))+
  (4+10*(c).dictionary+(4+(c).blocks*(4+(c).rows*(2*(1+18*(c).nodes)+4))))
def nameBound (B : ℕ) :=DescentResetPrimitivePage.size v.rawBits (c).lanes+
  (15+((c).blocks*(c).nodes)*(11+4*operandWork B))+
  (15*((c).dictionary+1)+(15+(c).blocks*(11+4*(1+18*(c).nodes))))

theorem price (floor : ℕ) (src : v.Inputs) (B : ℕ) (m : Memory w)
    (small : ∀x n,(src.retained x n).work≤B ∧ (src.fresh x n).work≤B ∧ (src.relay x n).work≤B)
    (room : v.endAddress floor<2^w) :
    v.clock G s Z op floor src≤v.clockBound B ∧ names (v.program G s Z op floor src w)≤v.nameBound B:=by
  let es:=List.ofFn (v.operation G s Z op floor src)
  have len : es.length=(c).blocks*(c).nodes:=List.length_ofFn
  have costs : ∀e∈es,e.work≤operandWork B:=by
    intro e hi
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hi
    let p : Fin (c).blocks×Fin (c).nodes:=finProdFinEquiv.symm i
    obtain ⟨l,r,h⟩:=small p.1 p.2
    change (DescentResetPrimitivePage.expr G s Z op floor v.rawBits (c).lanes
      (src.retained p.1 p.2) (src.fresh p.1 p.2) (src.relay p.1 p.2)).work≤_
    simp only [DescentResetPrimitivePage.expr,DescentStaticUnary.query,Tables.read,Expr.work,operandWork];omega
  have costs₁:=ProbeStage.Native.columns_clock (c).rows (v.gateEnd floor) (operandWork B) es costs
  have costs₂:=ProbeStage.Native.columns_text w (c).rows (v.gateEnd floor) (operandWork B) es costs
  rw [len] at costs₁ costs₂
  obtain ⟨t,a⟩:=DescentResetNodeBooks.charged (v.scalarEnd floor) (v.gateEnd floor) (c).blocks (c).nodes (c).hosts (c).groups (c).bits (c).lanes w
  have high : v.gateEnd floor≤v.endAddress floor:=by
    exact (((Nat.le_add_right _ (((c).blocks*(c).nodes)*(c).rows)).trans (Nat.le_add_right _ (max (c).dictionary (c).rounded))).trans
      (Nat.le_add_right _ ((c).blocks*(c).rows))).trans (Nat.le_add_right ..)
  have charge:=DescentResetPrimitivePage.tariff G s Z op floor v.rawBits (c).lanes m (high.trans_lt room)
  constructor
  · exact Nat.add_le_add (Nat.add_le_add_left costs₁ _) t
  · unfold program
    rw [names_seq,names_seq]
    exact Nat.add_le_add (Nat.add_le_add charge.le costs₂) a
end
end Hierarchy.DescentResetPrimitiveCheckpoint.Shape

end OAI
