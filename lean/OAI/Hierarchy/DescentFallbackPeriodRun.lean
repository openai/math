import OAI.Hierarchy.DescentFallbackPeriodInputs
import OAI.Hierarchy.DescentPackedPayloadBudget

namespace OAI
/-! # One physical window gather and one common fallback private-menu evaluation -/
namespace Hierarchy.DescentFallbackPeriod
open DescentSIMDLookup DescentPackedZip DescentPackedPrivateMenu DescentPackedFallbackTree.Image
open DescentResetHostSize DescentPacking.PackedMatch.Local.Gather ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D L cap n h r Ht l field H G M w : ℕ}

def law (board : NonlinearExpanders.Graph n h) (r Ht l C b width : ℕ)
    (side : Bool) (ticket : Code r×Option (Fin (2^n))) (x : Cell (field*inputCount D L cap n r)) :=
  panel board r Ht (L*(2*cap)) l C b width side
    (pack r Ht (L*(2*cap)) l (key side ticket (packet x)))

/-- For the fallback pass the physical panel never consults rotor layers. A single immutable
program can fix their digit width at zero for every possible selected history. -/
theorem layer_free (board : NonlinearExpanders.Graph n h) (C b a z slot : ℕ) (which : Bool)
    (ticket : Code r×Option (Fin (2^n))) (v : Packet D L cap n r field) (j : Fin 5) :
    values board r Ht (L*(2*cap)) a C b which slot (key which ticket v) j=
      values board r Ht (L*(2*cap)) z C b which slot (key which ticket v) j := by
  unfold key
  split
  · split <;> rfl
  · rfl

theorem run (board : NonlinearExpanders.Graph n h) (C b width : ℕ) (side : Bool)
    (ticket : Code r×Option (Fin (2^n))) (tables : Fin (inputCount D L cap n r)→Tables)
    (reads : Fin (inputCount D L cap n r)→Expr) (menu : DescentSIMDLookup.Banks) (mid out : ℕ)
    (v : Fin H→Fin G→Packet D L cap n r field) (pos : 0<M) (m : Memory w)
    (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M m)
    (sources : ∀j,Source (reads (number j)) (fun a g=>v a g j) M m)
    (room : mid+H*chunks G M<2^w)
    (fit : Fits menu (field*inputCount D L cap n r)
      (fieldBits board r Ht (L*(2*cap)) l C b*(width*5)) M H G w out)
    (rom : resident (law board r Ht l C b width side ticket (D:=D) (L:=L) (cap:=cap) (field:=field)) menu H G M m)
    (dictLow : menu.dictionary.base+2^((field*inputCount D L cap n r)*M)≤ mid)
    (maskLow : menu.mask.base+H*chunks G M≤ mid) (wire : menu.source.base=mid) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out menu (image mid rows act m)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out H G M w)).Exec m dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    (∀a g (u : Fin width) (j : Fin 5),digit (fieldBits board r Ht (L*(2*cap)) l C b)
      (finProdFinEquiv (u,j)).val
      (digit (fieldBits board r Ht (L*(2*cap)) l C b*(width*5)) (lane g pos).val
        (dst (out+(row H G M (position a g pos)).val)).val)=
       values board r Ht (L*(2*cap)) l C b side u.val (key side ticket (v a g)) j) ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out ∨ out+rows≤addr)→dst addr=m addr := by
  let act:=assembly tables reads
  let rows:=H*chunks G M
  let middle:=image mid rows act m
  let x:=fun a g=>encodePacket (v a g)
  let fn:=law board r Ht l C b width side ticket (D:=D) (L:=L) (cap:=cap) (field:=field)
  have old (a : ℕ) (below : a< mid) : middle a=m a :=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl below)
  have fixed : resident fn menu H G M middle := by
    refine ⟨fun i=>?_,fun i=>?_⟩
    · rw [old _ (by have:=i.isLt;omega)]
      exact rom.1 i
    · rw [old _ (by have:=i.isLt;omega)]
      exact rom.2 i
  have slots (j) := sources (number.symm j)
  have seen:=collected tables reads mid bounds m constants (fun a g j=>v a g (number.symm j))
    (fun j=>by simpa using slots j) (List.finRange _)
  have ready (p : Row H G M) : middle (menu.source.base+(row H G M p).val)=(data x p).val := by
    rw [wire]
    apply (ProtocolRAMGeneratedWrite.read_image _ _ _ _ _).trans
    simpa only [x,encodePacket,act,assembly,List.mem_finRange,ite_true] using seen p
  have beginRun : (scan w mid rows act).Exec m middle (4+rows*(2*act.work+4)) :=
    @ProtocolRAM.scan_exec w mid rows act m
      (DescentPacking.PackedMatch.Local.Gather.fits tables reads mid bounds (List.finRange _)) room
  obtain ⟨endRun,result,_⟩:=DescentPackedLocalLookup.compile menu out fn x pos fit middle fixed ready
  refine ⟨beginRun.then endRun,?_,?_⟩
  · intro a g u j
    rw [result]
    simpa only [fn,x,law,packet_encode] using cell_read board r Ht (L*(2*cap)) l C b width side
      (key side ticket (v a g)) u j
  · intro addr awayMid awayOut
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ awayOut).trans
      (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ awayMid)

theorem clock_le (tables : Fin (inputCount D L cap n r)→Tables)
    (reads : Fin (inputCount D L cap n r)→Expr) (bound : ℕ) (ops : ∀i,(reads i).work≤bound) :
    let rows:=H*chunks G M
    (4+rows*(2*(assembly tables reads).work+4))+(4+44*rows)≤
      8+rows*(2*(1+(inputCount D L cap n r)*(bound+20))+48) := by
  have total (is : List (Fin (inputCount D L cap n r))) :
      (collect tables reads is).work≤1+is.length*(bound+20) := by
    induction is with
    | nil=>simp [collect,Expr.work]
    | cons i is ih=>
      rw [collect,DescentPackedZip.work,List.length_cons,Nat.succ_mul]
      have:=ops i
      omega
  have size:=total (List.finRange (inputCount D L cap n r))
  simp only [List.length_finRange] at size
  dsimp
  calc
    _ = 8+(H*chunks G M)*(2*(assembly tables reads).work+48) := by ring
    _ ≤ _ := by gcongr; exact size

end
end Hierarchy.DescentFallbackPeriod

end OAI
