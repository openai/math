import OAI.Hierarchy.DescentFallbackPeriodSchedule

namespace OAI
/-! # Cost of the reached scalar census and the packed fallback private bank -/
namespace Hierarchy.DescentFallbackPeriod
open DescentSIMDLookup DescentPackedZip DescentPackedPrivateMenu DescentPackedFallbackTree.Image
open DescentSharedBookScan DescentSharedLeafLookup DescentFallbackRankRAM DescentPackedColony
open DescentPacking.PackedMatch.Local.Gather ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical
variable {D L cap n r : ℕ}

theorem reads_work (H : ℕ) (ports : Ports D) (books : Header) (here : Fin L→Expr) (tagged : Fin L→Bank)
    (sign : Fin L→Fin (2*cap)→Expr) (work : ℕ) (old : ∀i,(here i).work≤work)
    (signed : ∀i z,(sign i z).work≤work) (p : Input D L cap n r) :
    (operand (H:=H) ports books here tagged sign p).work≤ max work 80 := by
  rcases p with (i|⟨k,i⟩)|(⟨i,z⟩|i)
  · exact (old i).trans (Nat.le_max_left ..)
  · simp [operand,peerExpr,neighborID,Expr.work]
  · exact (signed i z).trans (Nat.le_max_left ..)
  · simp [operand,source,address,Expr.work]

theorem clock (chart : Chart) (tables : Fin (inputCount D L cap n r)→Tables)
    (reads : Fin (inputCount D L cap n r)→Expr) (work H G W a scale bytes Ht : ℕ)
    (operands : ∀i,(reads i).work≤work) (pos : 0<bytes) (wide : 2*bytes≤a) (word : W≤ scale*a) :
    let rows:=H*chunks G (lanes a bytes)
    let N:=DescentSharedBookScan.width r (2^n) D
    let shared:=record chart H D (2^Ht) (Ht+2)
    let gathered:=assembly tables reads
    ((4+H*N*(2*shared.work+4))+((4+rows*(2*gathered.work+4))+(4+44*rows)))*W ≤
      scale*((12+H*N*(2*(10000*(D+1)^2*(2^Ht+1))+4))*a +
        (2*(1+(inputCount D L cap n r)*(work+20))+48)*(H*a+4*H*G*bytes)) := by
  dsimp
  let N:=DescentSharedBookScan.width r (2^n) D
  let rows:=H*chunks G (lanes a bytes)
  let factor:=2*(1+(inputCount D L cap n r)*(work+20))+48
  have scalar:=shared_work chart D (2^Ht) H (Ht+2)
  have block:=(clock_le (H:=H) (G:=G) (M:=lanes a bytes) tables reads work operands)
  have short:=(volume H G a bytes pos wide)
  apply DescentPackedPayloadBudget.clock word
  calc
    _ ≤ ((4+H*N*(2*(10000*(D+1)^2*(2^Ht+1))+4))+(8+rows*factor))*a := by
      apply Nat.mul_le_mul_right
      apply Nat.add_le_add _ block
      gcongr
    _ = (12+H*N*(2*(10000*(D+1)^2*(2^Ht+1))+4))*a +factor*(rows*a) := by ring
    _ ≤ _ := by gcongr

theorem cheap (chart : Chart) (tabs : Fin (inputCount D L cap n r)→Tables)
    (field : Fin (inputCount D L cap n r)→Expr) (bank : Banks) (w H G M Ht at₀ mid out : ℕ) :
    CheapCode ((body chart H D (2^Ht) w (Ht+2) at₀ (H*DescentSharedBookScan.width r (2^n) D)).seq
      ((scan w mid (H*chunks G M) (assembly tabs field)).seq (DescentSIMDLookup.program bank out H G M w))) :=
  cheap_seq (@scan_cheap _ _ _ _) (cheap_seq (@scan_cheap _ _ _ _) (@scan_cheap _ _ _ _))

end Hierarchy.DescentFallbackPeriod

end OAI
