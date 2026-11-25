import OAI.Hierarchy.DescentPackedFlowPublication
import OAI.Hierarchy.DescentPackedRectanglePublication
import OAI.Hierarchy.DescentPackedCanvasMasks

namespace OAI
/-! # Fixed clocks for arbitrary old cell contents in a measured reset -/
namespace Hierarchy
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
namespace DescentPackedFlowPublication
open DescentPackedFlowBatch
variable {D r c H J M d b w : ℕ}

theorem execute_any_framed (A : Layout D r c) (S : Room A H J M d b w) (m : Memory w) :
    ∃dst,(procedure A H J M w).Exec m dst (duration A H J M) ∧
      ∀i,i<A.first ∨ A.middle+D*A.pitch≤ i→dst i=m i := by
  let n:=H*chunks J M
  let qs:=passes A.first n A.pitch A.front 0 D
  let mid:=result qs m
  have stop : A.middle<2^w:=(Nat.le_add_right _ _).trans_lt S.small
  have start : A.first≤A.middle:=Nat.le_add_right ..
  have front : ∀j<D,(A.front j).Fits w A.first:=fun j h=>(A.front j).fits_of_inputEnd (S.front j h) (start.trans_lt stop)
  have back : ∀j<D,(A.both H j).Fits w A.middle:=fun j h=>(A.both H j).fits_of_inputEnd (S.back j h) stop
  have one:=execute A.first n A.pitch D A.front m front stop S.pitch
  have two:=execute A.middle n A.pitch D (A.both H) mid back S.small S.pitch
  refine ⟨_,Procedure.Exec.then one.1 two.1,?_⟩
  intro i hi
  rcases hi with h|h
  · exact (two.2.2 _ (h.trans_le start)).trans (one.2.2 _ h)
  · have second:=above A.middle n A.pitch (A.both H) mid 0 D i S.pitch (by simpa using h)
    have prior:A.first+D*A.pitch=A.middle:=rfl
    exact second.trans (above A.first n A.pitch A.front m 0 D i S.pitch (by simpa only [Nat.zero_add,prior] using (show A.middle≤ i by omega)))

theorem execute_any (A : Layout D r c) (S : Room A H J M d b w) (m : Memory w) :
    ∃dst,(procedure A H J M w).Exec m dst (duration A H J M) := by
  obtain ⟨dst,run,_⟩:=execute_any_framed A S m
  exact ⟨dst,run⟩
end DescentPackedFlowPublication

namespace DescentPackedRectangle
open DescentMeasuredHeader
variable {w pitch H u l D start out : ℕ}

private theorem header_then_gather (L : Tape) (A : Gather) (mem : Memory w)
    (safe : Fits L w H (u+l) D start) (S : Room A pitch H u l D w out)
    (top : start+3*(H*((u+l)+1)+H*D)<2^w) :
    (code L A w start out H u l D).Exec mem
      (image out ((H*((u+l)+1)+H*D)*2^u) (expression A) (headerMem L start H (u+l) D mem))
      (headerTime L H (u+l) D+(4+100*((H*((u+l)+1)+H*D)*2^u))) := by
  obtain ⟨head,_⟩ := header_exec L mem safe top
  have fits : (expression A).Fits w out := by
    simp only [expression,Expr.Fits]
    repeat' first | exact S.banks _ (by simp [Gather.banks]) | trivial | constructor
  rw [Nat.mul_comm 100 ((H*((u+l)+1)+H*D)*2^u)]
  intro labels regs slots machine
  exact Procedure.Exec.then head
    (scan_exec out ((H*((u+l)+1)+H*D)*2^u) (expression A) (headerMem L start H (u+l) D mem) fits S.output) machine

theorem execute_any_framed (L : Tape) (A : Gather) (mem : Memory w) (safe : Fits L w H (u+l) D start)
    (between : start+3*(H*((u+l)+1)+H*D)≤out) (S : Room A pitch H u l D w out) (top : start+3*(H*((u+l)+1)+H*D)<2^w) :
    ∃dst,(code L A w start out H u l D).Exec mem dst
      (headerTime L H (u+l) D+(4+100*((H*((u+l)+1)+H*D)*2^u))) ∧
      ∀i,i<start ∨ out+(H*((u+l)+1)+H*D)*2^u≤ i→dst i=mem i := by
  let n := H*((u+l)+1)+H*D
  let mid := headerMem L start H (u+l) D mem
  refine ⟨image out (n*2^u) (expression A) mid,header_then_gather L A mem safe S top,?_⟩
  intro i hi
  change i < start ∨ out+n*2^u ≤ i at hi
  change start+3*n ≤ out at between
  rw [ProtocolRAMGeneratedWrite.frame_image out (n*2^u) (expression A) mid i (by omega)]
  dsimp only [mid,headerMem]
  rw [ProtocolRAMGeneratedWrite.frame_image (start+2*n) n (column L H (u+l) .gain) _ i (by omega),
      ProtocolRAMGeneratedWrite.frame_image (start+n) n (column L H (u+l) .depth) _ i (by omega),
      ProtocolRAMGeneratedWrite.frame_image start n (column L H (u+l) .live) mem i (by omega)]

theorem execute_any (L : Tape) (A : Gather) (mem : Memory w) (safe : Fits L w H (u+l) D start)
    (S : Room A pitch H u l D w out) (top : start+3*(H*((u+l)+1)+H*D)<2^w) :
    ∃dst,(code L A w start out H u l D).Exec mem dst
      (headerTime L H (u+l) D+(4+100*((H*((u+l)+1)+H*D)*2^u))) := by
  exact ⟨_,header_then_gather L A mem safe S top⟩

namespace Canvas
theorem masks_any_framed {owners count depth gain : Bank} {head tail H k D w : ℕ} (mem : Memory w)
    (safe : ∀B∈[owners,count,depth,gain],B.Fits w head)
    (gap : head+(H*(k+1)+H*D)≤tail) (room : tail+(H*(k+1)+H*D)<2^w) :
    ∃dst,(masks owners count depth gain head tail H k D w).Exec mem dst
      ((4+48*(H*(k+1)+H*D))+(4+48*(H*(k+1)+H*D))) ∧
      ∀i,i<head ∨ tail+(H*(k+1)+H*D)≤ i→dst i=mem i := by
  let N:=H*(k+1)+H*D
  have bound : head+N<2^w:=gap.trans_lt ((Nat.le_add_right ..).trans_lt room)
  have mono:head≤tail:=by omega
  have fits : ∀B∈[owners,count,depth,gain],B.Fits w tail:=fun B h=>
    ⟨(safe _ h).1,(safe _ h).2.1,(safe _ h).2.2.trans mono⟩
  have f₀ : (masked owners count depth).Fits w head:=
    ⟨⟨safe _ (by simp),trivial⟩,⟨safe _ (by simp),trivial⟩,⟨safe _ (by simp),trivial⟩,trivial⟩
  have f₁ : (masked owners count gain).Fits w tail:=
    ⟨⟨fits _ (by simp),trivial⟩,⟨fits _ (by simp),trivial⟩,⟨fits _ (by simp),trivial⟩,trivial⟩
  let mid:=image head N (masked owners count depth) mem
  refine ⟨image tail N (masked owners count gain) mid,?_,?_⟩
  · rw [Nat.mul_comm 48 (H*(k+1)+H*D)]
    intro labels regs slots machine
    exact Procedure.Exec.then (scan_exec head N (masked owners count depth) mem f₀ bound)
      (scan_exec tail N (masked owners count gain) mid f₁ room) machine
  · intro i hi
    change i < head ∨ tail+N ≤ i at hi
    exact (ProtocolRAMGeneratedWrite.frame_image tail N (masked owners count gain) mid i (by omega)).trans
      (ProtocolRAMGeneratedWrite.frame_image head N (masked owners count depth) mem i (by omega))

theorem masks_any {owners count depth gain : Bank} {head tail H k D w : ℕ} (mem : Memory w)
    (safe : ∀B∈[owners,count,depth,gain],B.Fits w head)
    (gap : head+(H*(k+1)+H*D)≤tail) (room : tail+(H*(k+1)+H*D)<2^w) :
    ∃dst,(masks owners count depth gain head tail H k D w).Exec mem dst
      ((4+48*(H*(k+1)+H*D))+(4+48*(H*(k+1)+H*D))) := by
  obtain ⟨dst,run,_⟩:=masks_any_framed mem safe gap room
  exact ⟨dst,run⟩
end Canvas
end DescentPackedRectangle
end
end Hierarchy

end OAI
