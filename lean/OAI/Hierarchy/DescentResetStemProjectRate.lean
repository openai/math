import OAI.Hierarchy.DescentDatedAddressRate
import OAI.Hierarchy.DescentResetStemProject

namespace OAI
/-! # A single address exponent for the dated vector stem projection -/
namespace Hierarchy.DescentResetStemProject
open Filter DescentDatedAddressBook DescentSIMDLookup ProtocolRAM
open ThreeFlat.Routing
variable {ι : ℕ→Type*}
private theorem chunk_rate {g batch : ∀h,ι h→ℕ} (bg : Bounded g) (bm : Bounded batch) :
    Bounded (fun h i=>chunks (g h i) (batch h i)) := by
  apply (bg.add bm).of_le
  intro h i
  exact (Nat.div_le_self ..).trans (Nat.sub_le ..)

/-- All donor and projected populations may vary with the date. The only
exponential dictionaries serialize the existing input word or its new panel. -/
theorem rates {N H G X a A M : ∀h,ι h→ℕ}
    (n : Bounded N) (hosts : Bounded H) (group : Bounded G) (block : Bounded X)
    (oldPitch : Bounded A) (newPitch : Bounded M)
    (inBits : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,a h i*A h i≤K*h)
    (outBits : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(a h i*X h i)*M h i≤K*h) :
    Bounded (fun h i=>endAddress 0 (N h i) (H h i) (G h i) (X h i) (a h i) (A h i) (M h i)) := by
  obtain ⟨kIn,pIn⟩:=inBits
  obtain ⟨kOut,pOut⟩:=outBits
  have raw : Bounded (fun h i=>2^(a h i*A h i)) := Bounded.pow_of_linear pIn
  have words : Bounded (fun h i=>2^((a h i*X h i)*M h i)) := Bounded.pow_of_linear pOut
  have one:=Bounded.const (ι:=ι) 1
  have two:=Bounded.const (ι:=ι) 2
  have bands:=group.mul block
  have nextPitch:=newPitch.mul block
  have oldChunks:=chunk_rate bands oldPitch
  have newChunks:=chunk_rate bands nextPitch
  have pages:=chunk_rate group newPitch
  have oldSpan:=((n.mul (hosts.mul oldChunks)).add one).padded
  have gatherEnd : Bounded (fun h i=>overlapBase 0 (N h i) (H h i) (G h i) (X h i) (A h i)) := by
    simpa only [overlapBase,gathered,dense,Bank.size,Nat.zero_add] using oldSpan
  have pieces : Bounded (fun h i=>Overlap.pieces (G h i*X h i) (A h i) (M h i*X h i)) :=
    oldChunks.of_le (fun _ _=>min_le_left _ _)
  have convertedRows:=(n.mul hosts).mul newChunks
  have mapSize:=(convertedRows.add one).padded
  have dictSize:=((oldPitch.add one).padded).mul raw
  have sourceEnd : Bounded (fun h i=>reshapeBase 0 (N h i) (H h i) (G h i) (X h i)
      (a h i) (A h i) (M h i)) := by
    simpa only [reshapeBase,converted,dense,Bank.size,Overlap.dest,Overlap.dictBase,Overlap.mapBits,
      Overlap.rows,Overlap.keyBits,Nat.pow_add] using
      (((gatherEnd.add ((pieces.add one).mul mapSize)).add (pieces.mul dictSize)).add mapSize)
  have bookRows : Bounded (fun h i=>DescentVectorBookReshape.rows (H h i) 1 (G h i) (X h i) (M h i)) := by
    simpa only [DescentVectorBookReshape.rows,Nat.mul_one] using block.mul (hosts.mul pages)
  have nRows:=n.mul bookRows
  have entries:=block.mul words
  have bookCells:=entries.add (two.mul nRows)
  have projected : Bounded (fun h i=>out 0 (N h i) (H h i) (G h i) (X h i) (a h i) (A h i) (M h i)) := by
    simpa only [out,DescentVectorBookReshape.output,DescentVectorBookReshape.cells,
      DescentVectorBookReshape.dictionaryWords] using
      (((sourceEnd.add bookCells).add (entries.add one).padded).add (nRows.add one).padded)
  exact (projected.add nRows).add (((hosts.mul pages).add one).padded)

end Hierarchy.DescentResetStemProject

end OAI
