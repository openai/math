import OAI.Computability.BorderVNP.PackedDirectoryKeys

/-! # Inverting the source-bit address of a populated delivery interval -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

private theorem quotient {x i block : ℕ} (hb : 0 < block) (lo : i*block ≤ x)
    (hi : x < i*block+block) : x/block = i :=
  Nat.le_antisymm (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hb).mpr
    (by simpa only [Nat.succ_mul] using hi))) ((Nat.le_div_iff_mul_le hb).mpr lo)

private theorem inside {start len block k e : ℕ} (h : e < (slice start len block k).2) :
    let x := (slice start len block k).1+e
    start ≤ x ∧ x < start+len ∧ (start/block+k)*block ≤ x ∧ x < (start/block+k)*block+block :=
  (mem_slice_iff ..).mp ⟨Nat.le_add_right ..,Nat.add_lt_add_left h _⟩

/-- Reconstruct the originating candidate and its local bit offset from a physical
processor and a bit of its private literal tail. -/
def Layout.recoverPrivate (d : Layout) (team proc off : ℕ) : ℕ × ℕ :=
  let tail := d.literal/2
  let procNum := team*d.processors+proc
  let x := procNum*tail+off
  let j := x/d.description
  let k := procNum-(j*d.description/tail)
  (privateIndex j k,x-(slice (j*d.description) d.description tail k).1)

/-- Reconstruct the originating candidate and offset from a processor's literal or
additional pinned field. -/
def Layout.recoverLive (d : Layout) (team proc field off : ℕ) : ℕ × ℕ :=
  let start := proc*d.stride+field*(d.literal+(d.teams-1)*d.link)
  let pos := start+off
  let k := pos/d.block-start/d.block
  (d.liveIndex team proc field k,pos-(slice start d.literal d.block k).1)

/-- A private source bit is inside the reserved tail, and determines its row and
intra-row offset uniquely, even at a boundary between processors. -/
theorem Layout.recover_privateRow (d : Layout) (pp : ℕ → ℕ × ℕ) (j k e : ℕ) :
    let row := d.privateRow pp j k
    let off := row.offset+e-(d.literal-d.literal/2)
    e < row.width → off < d.literal/2 ∧
      d.recoverPrivate row.team row.processor off = (privateIndex j k,e) := by
  let start := j*d.description
  let tail := d.literal/2
  let num := start/tail+k
  let sl := slice start d.description tail k
  let off := sl.1-num*tail+e
  let pos := sl.1+e
  have hlow : num*tail ≤ sl.1 := le_max_right ..
  have ho : d.literal-tail+(sl.1-num*tail)+e-(d.literal-tail) = off := by dsimp [off]; omega
  dsimp only
  intro hd
  change e < sl.2 at hd
  obtain ⟨hstart,hend,_,hblock⟩ := inside hd
  change start ≤ pos at hstart
  change pos < start+d.description at hend
  change pos < num*tail+tail at hblock
  have hx : num*tail+off = pos := by dsimp only [off,pos]; omega
  have hdiv : pos/d.description = j := quotient (by omega) hstart hend
  change d.literal-tail+(sl.1-num*tail)+e-(d.literal-tail) < tail ∧
    d.recoverPrivate (num/d.processors) (num%d.processors)
      (d.literal-tail+(sl.1-num*tail)+e-(d.literal-tail)) = _
  rw [ho]
  refine ⟨by omega,?_⟩
  simp only [recoverPrivate,Nat.div_add_mod',show num*(d.literal/2)+off = pos from hx,hdiv]
  have hsub : num-j*d.description/(d.literal/2) = k := by dsimp only [num,start,tail]; omega
  rw [hsub]
  change (_,pos-sl.1) = _
  congr 1
  dsimp only [pos]
  omega

/-- A live delivery address lies within the processor field and determines its original
public row and local offset. -/
theorem Layout.recover_liveRow (d : Layout) (lp : ℕ → ℕ × ℕ) (t p f k e : ℕ)
    (hb : 0 < d.block) :
    let row := d.liveRow lp t p f k
    e < row.width → row.offset+e < d.literal ∧
      d.recoverLive row.team row.processor row.field (row.offset+e) = (d.liveIndex t p f k,e) := by
  let start := p*d.stride+f*(d.literal+(d.teams-1)*d.link)
  let sl := slice start d.literal d.block k
  let pos := sl.1+e
  dsimp only
  intro hd
  change e < sl.2 at hd
  obtain ⟨_,hend,hlo,hhi⟩ := inside hd
  change pos < start+d.literal at hend
  have hleft : start ≤ sl.1 := le_max_left ..
  have hx : start+(sl.1-start+e) = pos := by dsimp only [pos]; omega
  have hdiv : pos/d.block = start/d.block+k := quotient hb hlo hhi
  change sl.1-start+e < d.literal ∧ d.recoverLive t p f (sl.1-start+e) = _
  refine ⟨by omega,?_⟩
  change (d.liveIndex t p f ((start+_)/d.block-start/d.block),
    (start+_)-(slice start d.literal d.block ((start+_)/d.block-start/d.block)).1) = _
  rw [hx,hdiv,Nat.add_sub_cancel_left]
  change (_,pos-sl.1) = _
  congr 1
  dsimp only [pos]
  omega

end Packing.Directory

end BorderVNP
end Computability
end OAI
