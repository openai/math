import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.DescentPackedLocalExecution
import OAI.Hierarchy.DescentPackedMaskedData

namespace OAI
/-! # Native packed words from a vector gather followed by a local lookup -/
namespace Hierarchy.DescentIssuedGoodHeaders
open DescentSIMDLookup DescentPackedFallbackTree.Image DescentPackedZip
open DescentPacking.PackedMatch.Local.Gather
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAMGeneratedWrite ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {field H G w M : ℕ}

/-- One finite dictionary on any fixed number of genuine preceding operand banks. -/
theorem gathered_words {N b : ℕ} (emit : (Fin N→Cell field)→Cell b)
    (tables : Fin N→Tables) (reads : Fin N→Expr) (menu : DescentSIMDLookup.Banks)
    (mid out : ℕ) (x : Fin H→Fin G→Fin N→Cell field) (positive : 0< M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (sources : ∀j,Source (reads j) (fun a g=> x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*N) b M H G w out)
    (rom : resident (emit ∘ (encode field N).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*N)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    (∀q : Row H G M,dst (out+(row H G M q).val)=((data (fun a g=> emit (x a g)) q).val:Word w)) ∧
    (∀a g,digit b (lane g positive).val (dst (out+(row H G M (position a g positive)).val)).val=(emit (x a g)).val) ∧
    ∀addr,(addr< mid ∨ mid+rows≤ addr)→(addr< out ∨ out+rows≤ addr)→dst addr=mem addr := by
  let act:=assembly tables reads
  let rows:=H*chunks G M
  let middle:=image mid rows act mem
  let fn:=emit ∘ (encode field N).symm
  have old (a : ℕ) (below : a< mid) : middle a=mem a :=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl below)
  have fixed : resident fn menu H G M middle := by
    refine ⟨fun i=>?_,fun i=>?_⟩
    · rw [old _ (by have:=i.isLt;omega)];exact rom.1 i
    · rw [old _ (by have:=i.isLt;omega)];exact rom.2 i
  have seen:=collected tables reads mid bounds mem constants x sources (List.finRange _)
  have input (p : Row H G M) : middle (menu.source.base+(row H G M p).val)=(data (fun v j=> encode field N (x v j)) p).val := by
    rw [wire]
    apply (ProtocolRAMGeneratedWrite.read_image _ _ _ _ _).trans
    simpa only [act,assembly,List.mem_finRange,ite_true] using seen p
  have gather : (scan w mid rows act).Exec mem middle (4+rows*(2*act.work+4)) :=
    scan_exec (w:=w) mid rows act mem
      (DescentPacking.PackedMatch.Local.Gather.fits tables reads mid bounds (List.finRange _)) room
  obtain ⟨run,read,_⟩:=DescentPackedLocalLookup.compile menu out fn (fun v j=> encode field N (x v j)) positive fit middle fixed input
  have pins : DescentSIMDLookup.PinFrame (M:=M) menu fn (fun v j=> encode field N (x v j)) middle := by
    refine ⟨?_,input⟩
    intro entry bit
    cases entry with
    | inl i=> exact congrArg (fun z=> Computability.VPVNP.RAMSerialization.wordBits w z bit) (fixed.1 i)
    | inr i=> exact congrArg (fun z=> Computability.VPVNP.RAMSerialization.wordBits w z bit) (fixed.2 i)
  refine ⟨gather.then run,?_,?_,?_⟩
  · intro q
    have value:=(ProtocolRAMGeneratedWrite.read_image out rows (DescentSIMDLookup.lookup menu) middle (row H G M q)).trans
      (DescentSIMDLookup.lookup_read menu out fit fn (fun v j=> encode field N (x v j)) middle pins q)
    simpa only [imageBank,rows,middle,act,masked_eq_data,fn,Function.comp_apply,Equiv.symm_apply_apply] using value
  · intro a g;simpa [fn] using read a g
  · intro addr awayMid awayOut
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ awayOut).trans
      (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ awayMid)

end
end Hierarchy.DescentIssuedGoodHeaders

end OAI
