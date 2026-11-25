import OAI.Computability.BorderVNP.CellPacketFinishPack
import OAI.Computability.BorderVNP.CellPacketFinishCount

/-! # Exact packed argument and length for a native private-cell call

The chunk loop has written the tagged packet bits up to its cursor. This final
code appends the field terminator and external input, packs the complete payload,
and returns its actual word address and count in registers 5 and 15.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket

open VPVNP.BurstRAM RationalHitting.StackLanguage CellPacketEncode Packing.Directory.ISA

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- Final native instructions for a packed private call. -/
def finish : Code := .seq writeSuffix (.seq (.seq packSetup CompactWrite.writer) countBurst)

/-- Registers above the two source and destination workspaces survive the complete
finishing pass, so the enclosing cell traversal may keep its counters there. -/
theorem finish_keeps_upper : ∀ i : Reg, 21 ≤ i.val → finish.keeps i = true := by decide

/-- Tick allowance for suffix stores, packing, and returning the word count. -/
def finishCost (p ext : List Bool) : ℕ :=
  7*ext.length+5 + ((4+(CompactWrite.setup.slots+(CompactWrite.step.slots+1)*(envelope p ext).length+2))+9)

/-- The complete finishing pass is linear in the true packet and external-bit lengths. -/
theorem finishCost_le (p ext : List Bool) : finishCost p ext ≤ 100*(p.length+ext.length+1) := by
  have s : CompactWrite.setup.slots = 7 := by decide
  have t : CompactWrite.step.slots ≤ 45 := by decide
  unfold finishCost
  simp only [s,envelope,List.length_append,codeWord_length]
  nlinarith only [Nat.mul_le_mul_left (2*p.length+1+ext.length) t]

/-- Memory and returned burst registers after completing the scratch payload. -/
theorem finish_run (s : Bank w) (m : Memory w) (p ext : List Bool) (extBase scratch burst : ℕ)
    (hw : 0 < w) (c : Constants (readings s))
    (h4 : readings s 4 = extBase) (h5 : readings s 5 = ext.length) (h6 : readings s 6 = scratch)
    (h7 : readings s 7 = burst) (h8 : readings s 8 = w)
    (h20 : readings s 20 = scratch+(pairWord p).length)
    (prefixBits : CompactWrite.Source m scratch (pairWord p))
    (extBits : CompactWrite.Source m extBase ext)
    (suffixApart : CompactWrite.Disjoint extBase ext.length (scratch+(pairWord p).length) ([true]++ext).length)
    (burstApart : CompactWrite.Disjoint scratch (envelope p ext).length burst (CompactFrame.pack w (envelope p ext)).length)
    (srcFit : extBase+ext.length < 2^w) (scratchFit : scratch+(envelope p ext).length < 2^w)
    (burstFit : burst+(CompactFrame.pack w (envelope p ext)).length ≤ 2^w)
    (countFit : (CompactFrame.pack w (envelope p ext)).length < 2^w) :
    BoundedRun pub macros finish s m (finishCost p ext) (fun z =>
      z.reg 5 = burst ∧ z.reg 15 = (CompactFrame.pack w (envelope p ext)).length ∧
      z.mem = readings (putWords (suffixMemory m (scratch+(pairWord p).length) ext)
        burst (CompactFrame.pack w (envelope p ext)))) := by
  let cursor := scratch+(pairWord p).length
  have length : cursor+([true]++ext).length = scratch+(envelope p ext).length := by
    simp only [cursor,envelope_eq,List.length_append,Nat.add_assoc]
  have suffix := writeSuffix_run (pub := pub) (macros := macros) s m ext extBase cursor c h4 h5 h20 extBits
    suffixApart srcFit (length ▸ scratchFit)
  apply suffix.seq
  rintro t mt ⟨regs,cur,hm⟩
  have filled : mt = suffixMemory m cursor ext := by
    apply funext
    intro i
    apply Fin.ext
    exact congrFun (hm.trans (putDigits_eq_putWords m cursor ([true]++ext) hw)) i
  have src : CompactWrite.Source mt scratch (envelope p ext) := by
    rw [envelope_eq]
    exact source_append_stores scratch (pairWord p) ([true]++ext) prefixBits hm
  have packed := pack_run (pub := pub) (macros := macros) t mt scratch burst (envelope p ext) hw
    ((regs 8 (by decide)).trans h8) ((regs 6 (by decide)).trans h6) ((regs 7 (by decide)).trans h7)
    (cur.trans length) src burstApart scratchFit.le burstFit
  apply packed.seq
  rintro u mu ⟨width,len,base,mem⟩
  apply (countBurst_run (pub := pub) (macros := macros) u mu (envelope p ext) hw width len countFit).mono le_rfl
  rintro z ⟨n,b,memory⟩
  exact ⟨b.trans base,n,memory.trans (filled ▸ mem)⟩

/-- A private call through the returned registers reads exactly the canonical packed payload. -/
theorem finish_burst {s : Bank w} {mt m : Memory w} (p ext : List Bool) (scratch burst : ℕ)
    (base : readings s 5 = burst) (count : readings s 15 = (CompactFrame.pack w (envelope p ext)).length)
    (mem : readings mt = readings (putWords (suffixMemory m (scratch+(pairWord p).length) ext)
      burst (CompactFrame.pack w (envelope p ext)))) :
    TeamRAM.previous mt (.burst (s 5).val (s 15).val) = CompactFrame.pack w (envelope p ext) := by
  have h : mt = _ := funext fun i => Fin.ext (congrFun mem i)
  change TeamRAM.previous mt (.burst (readings s 5) (readings s 15)) = _
  rw [base,count,h,CompactWrite.previous_putWords]

end RoutingISA.CellPacket

end BorderVNP
end Computability
end OAI
