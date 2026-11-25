import OAI.Computability.BorderVNP.CellPacketLoad
import OAI.Computability.BorderVNP.PackedDirectoryWriter

/-! # Inserting records whose count is decoded from the private site sidecars -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket.Supplement

open VPVNP.BurstRAM DiagonalResidueRAM Packing.Directory.ISA

/-- Public pointers for the post-sidecar cell prepass. The original geometry tail
and two sidecar-produced counters are fetched from team RAM. -/
structure Layout where
  /-- First of the four reserved tail descriptors. -/
  tail : ℕ
  /-- First natural word of the sidecar-derived supplemental record stream. -/
  supplement : ℕ
  /-- Consecutive record-count and word-count cells written by the sidecar reader. -/
  counters : ℕ
  /-- Scratch cell containing the merged public and private row count. -/
  merged : ℕ
  /-- Number of words of the public report section, including its count. -/
  reportWords : ℕ

/-- Concrete runtime record and word counts. These are measurements of stored
arrays, rather than public advice about the original site tables. -/
structure Data where
  /-- Geometry address of the count before its row and report arrays. -/
  geomBase : ℕ
  /-- Number of public geometry records. -/
  geomCount : ℕ
  /-- Public record words following the count, excluding report words. -/
  geomWords : ℕ
  /-- Actual private supplemental record count. -/
  suppCount : ℕ
  /-- Actual private supplemental natural word count. -/
  suppWords : ℕ

/-- The prepass reads six concrete scalar words in the two producer arrays. -/
structure Input (l : Layout) (d : Data) {w : ℕ} (s : Bank w) (m : Memory w) : Prop where
  tail : readings s 2 = l.tail
  source : readings s 3 = l.supplement
  counters : readings s 4 = l.counters
  merged : readings s 5 = l.merged
  report : readings s 6 = l.reportWords
  base : readings m (l.tail+1) = d.geomBase
  tailLen : readings m (l.tail+2) = 1+d.geomWords+l.reportWords
  geomCount : readings m d.geomBase = d.geomCount
  suppCount : readings m l.counters = d.suppCount
  suppWords : readings m (l.counters+1) = d.suppWords

/-- Four actual natural-word source triples replacing the reserved static tail. -/
def descriptors (l : Layout) (d : Data) : List ℕ :=
  [0,l.merged,1,0,d.geomBase+1,d.geomWords,0,l.supplement,d.suppWords,
    0,d.geomBase+1+d.geomWords,l.reportWords]

/-- Compute the row-count sum, the start of the public reports and both stream
lengths. All sidecar-dependent words come from the physical counter bank. -/
def prepare : Code := .block [.constant 0 0,.constant 1 1,
  .binary .add 7 2 1,.load 8 7,.binary .add 7 7 1,.load 9 7,
  .load 10 8,.load 11 4,.binary .add 7 4 1,.load 12 7,
  .binary .add 13 10 11,.binary .add 14 8 1,.binary .sub 15 9 1,
  .binary .sub 15 15 6,.binary .add 16 14 15,.store 5 13,.copy 20 2]

/-- Register sequence for the four triples written by the fixed descriptor emitter. -/
def fields : List Reg := [0,5,1,0,14,15,0,3,12,0,16,6]

/-- Fixed public machine instructions for changing the record count and the
four source intervals. No public instruction varies with the private site data. -/
def code : Code := .seq prepare (pushWords fields)

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- Actual memory effect of the record-count prepass. -/
def image (l : Layout) (d : Data) (m : Memory w) : Memory w :=
  putWords (Function.update m l.merged (word w (d.geomCount+d.suppCount))) l.tail
    ((descriptors l d).map (word w))

set_option maxRecDepth 3000 in
/-- Execute the native count merge and four descriptor writes. It reads only the
two counters and the existing geometry-tail header, so its cost is constant even
when the supplemental stream contains many sparse records. -/
theorem run (l : Layout) (d : Data) (s : Bank w) (m : Memory w) (input : Input l d s m)
    (tailFit : l.tail+12 < 2^w) (counterFit : l.counters+1 < 2^w)
    (baseFit : d.geomBase+1+d.geomWords < 2^w) (countFit : d.geomCount+d.suppCount < 2^w) :
    BoundedRun pub mac code s m 42 (fun z => z.mem = readings (image l d m)) := by
  have nonzero : w ≠ 0 := by rintro rfl; simp at tailFit
  have oneFit : 1 < 2^w := by omega
  have one : (Fin.ofNat (2^w) 1).val = 1 := Nat.mod_eq_of_lt oneFit
  have safe : prepare.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [prepare,Code.block,Code.fixedSafe,Code.safeReadOnly,Code.fixedEval,
      Code.evalNat,addressOpFits,addressOp,NatState.ofWords,input.tail,input.counters,input.report,
      input.base,input.tailLen,input.geomCount,input.suppCount]
    omega
  obtain ⟨es,t,mt,first,cost,he⟩ := prepare.runFixed pub mac s m safe
  have reg := congrArg NatState.reg he
  have memory := congrArg NatState.mem he
  have computed (j : Reg) := congrFun reg j
  have cur : readings t 20 = l.tail := by
    simpa (config := {decide := true}) [prepare,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,input.tail] using computed 20
  have unit : readings t 1 = 1 := by
    simpa (config := {decide := true}) [prepare,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,one] using computed 1
  have vs : fields.map (readings t) = descriptors l d := by
    have equal := congrArg (fun f => fields.map f) reg
    simpa (config := {decide := true}) [fields,descriptors,prepare,Code.block,Code.fixedEval,Code.evalNat,
      NatState.ofWords,addressOp,one,input.tail,input.source,input.merged,input.counters,input.report,
      input.base,input.tailLen,input.geomCount,input.suppCount,input.suppWords,Nat.add_assoc,Nat.add_comm 1] using equal
  have exactMem : mt = Function.update m l.merged (word w (d.geomCount+d.suppCount)) := by
    funext j
    have atJ := congrFun memory j
    apply Fin.ext
    by_cases eq : j=l.merged
    · subst j
      rw [Function.update_self,word_val _ _ countFit]
      change readings mt l.merged = _
      simpa (config := {decide := true}) [prepare,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,
        addressOp,one,input.tail,input.merged,input.counters,input.base,input.geomCount,input.suppCount] using atJ
    · rw [Function.update_of_ne eq]
      change readings mt j = readings m j
      simpa (config := {decide := true}) [prepare,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,
        input.merged,Function.update_of_ne eq] using atJ
  have physical : fields.map t = (descriptors l d).map (word w) := by
    rw [←vs,List.map_map]
    exact List.map_congr_left fun i _ => Fin.ext (Nat.mod_eq_of_lt (t i).isLt).symm
  obtain ⟨fs,write,budget⟩ := pushWords_runs pub mac fields t mt l.tail
    (Fin.ext (cur.trans (word_val _ _ (by omega)).symm)) (Fin.ext (unit.trans one.symm))
    (by simpa [fields] using tailFit) (by decide)
  refine ⟨_,_,_,first.seq write,?_,?_⟩
  · rw [show traceCost (es++fs) = traceCost es + traceCost fs from VPVNP.RAMBuckets.cost_append ..,budget]
    have steps : prepare.slots = 17 := by decide
    rw [steps] at cost
    change traceCost es+(2*12+1) ≤ 42
    omega
  · change readings (putWords mt l.tail (fields.map t)) = readings (image l d m)
    rw [physical,exactMem]; rfl

end RoutingISA.CellPacket.Supplement

end BorderVNP
end Computability
end OAI
