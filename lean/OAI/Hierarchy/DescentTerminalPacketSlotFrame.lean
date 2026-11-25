import OAI.Hierarchy.DescentTerminalStableSortRAM
import OAI.Hierarchy.ProtocolRAMBinarySpan

namespace OAI
/-! # The retained RAM frame and output range of the native relative-slot scan -/
namespace Hierarchy.DescentTerminalPacketSlotRAM
open DescentTerminalExteriorPackets ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure Computability.BorderVNP.FragmentBucket
open scoped Classical Fin.CommRing
noncomputable section
variable {w n H : ℕ}

def bank (base slots : ℕ) : Bank:=⟨base,Nat.clog 2 slots⟩

def out (L : ProtocolRAMEndpointSort.Layout) (n H : ℕ) :=
  L.sorted+(bank 0 n).size+(bank 0 H).size

theorem workspace (L : ProtocolRAMEndpointSort.Layout) (n H : ℕ) :
    out L n H+n ≤ L.sorted+3*n+2*H+4 := by
  have bound (k : ℕ) : (bank 0 k).size ≤ 2*(k+1) := by
    apply Nat.le_trans _ (ProtocolRAMPurchaseSampler.span_le k)
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.clog_le_of_le_pow (ProtocolRAMPurchaseSampler.lt_span k).le
  have rows:=bound n;have sites:=bound H
  unfold out
  omega

def expr (L : ProtocolRAMEndpointSort.Layout) (n H : ℕ) : Expr :=
  let id_:=Expr.lookup (bank L.sorted n) .row
  let site:=Expr.lookup (bank L.src n) id_
  .op .sub .row (.op .sub (.lookup (bank L.starts H) site) (.lookup (bank L.counts H) site))

def after (L : ProtocolRAMEndpointSort.Layout) (n H : ℕ) (m : Memory w) :=
  image (out L n H) n (expr L n H) m

theorem retained (L : ProtocolRAMEndpointSort.Layout) (n H : ℕ) (m : Memory w) (a : ℕ)
    (away : a < out L n H ∨ out L n H+n ≤ a) : after L n H m a=m a := by
  simp [after,image,fillSegment,show ¬(out L n H ≤ a ∧ a < out L n H+n) by omega]

end
end Hierarchy.DescentTerminalPacketSlotRAM

end OAI
