import OAI.Computability.BorderVNP.RoutingISACompactWriteBurst
import OAI.Computability.BorderVNP.RoutingISACallInversion
import OAI.Computability.BorderVNP.RoutingISARegisterFrame
import OAI.Computability.BorderVNP.RoutingISATableEvents
import OAI.Computability.BorderVNP.RoutingISAOrdinaryCost

/-! # A native second call on the checked finite-field subtotal suffix

The ordinary writer reads the subtotal bits at the true source address. Its final
cursor names the word with the terminator; the RAM subtracts the output base and
adds one to supply the actual packed count to fixed routine one.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FiniteScalarCall

open VPVNP.BurstRAM Packing.Directory.ISA CellDispatch

variable {w src dst : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- Recover the true packed length from the last store address and the retained base. -/
def count : Code := .block [.binary .sub 15 7 5, .constant 1 1, .binary .add 15 15 1]

/-- Both the packer and the arithmetic precede the field-returning private call. -/
def prepare : Code := .seq CompactWrite.writer count

/-- Execute the finite-field scalar routine on the true contiguous packed subtotal suffix. -/
def code : Code := .seq prepare (.call 1 5 15)

/-- Exact native event of the deterministic scalar routine, in chronological word order. -/
def event (dst : ℕ) (words : List (Word w)) : TeamRAM.Event w := ⟨.burst dst words.length,words,[],.plus⟩

/-- The native outer writer and cursor arithmetic supply the true output operands. -/
theorem prepare_run (s : Bank w) (m : Memory w) (bits : List Bool) (hw : 0 < w)
    (width : readings s 2 = w) (base : readings s 3 = src) (len : readings s 4 = bits.length)
    (dest : readings s 5 = dst) (source : CompactWrite.Source m src bits)
    (separate : CompactWrite.Disjoint src bits.length dst (CompactFrame.pack w bits).length)
    (srcFit : src+bits.length ≤ 2^w) (dstFit : dst+(CompactFrame.pack w bits).length ≤ 2^w)
    (countFit : (CompactFrame.pack w bits).length < 2^w) :
    let words := CompactFrame.pack w bits
    let mem := putWords m dst words
    ∃ es t, Runs pub macros prepare s m es t mem ∧
      traceCost es ≤ CompactWrite.setup.slots+(CompactWrite.step.slots+1)*bits.length+2+count.slots ∧
      (t 5).val=dst ∧ (t 15).val=words.length := by
  intro words mem
  obtain ⟨fs,u,mu,pack,cost,memEq,cur⟩ := CompactWrite.writer_run_cursor (pub:=pub) (macros:=macros)
    s m bits hw width base len dest source separate srcFit dstFit
  have hm : mu = mem := funext fun a => Fin.ext (congrFun memEq a)
  subst mu
  have dest' : readings u 5 = dst := (congrArg Fin.val (pack.keepsReg (by decide : CompactWrite.writer.keeps 5 = true))).trans dest
  have clen : words.length = (2*bits.length)/w+1 := by
    rw [show words = CompactFrame.pack w bits from rfl,CompactFrame.length_pack,←CompactFrame.wordCount,
      CompactFrame.wordCount_terminator hw]
  have bound : (2*bits.length)/w+1 < 2^w := clen ▸ countFit
  change readings u 7 = dst + (2*bits.length)/w at cur
  have safe : count.safeReadOnly w (readings pub) (readings mem) (readings u) := by
    simp (config := {decide := true}) [count,Code.block,Code.safeReadOnly,Code.evalNat,addressOp,addressOpFits,cur,dest']
    omega
  obtain ⟨ys,t,next,hc,hr⟩ := count.runReadOnly pub macros mem u safe
  refine ⟨_,t,pack.seq next,?_,?_,?_⟩
  · rw [show traceCost (fs++ys) = traceCost fs + traceCost ys from VPVNP.RAMBuckets.cost_append ..]
    omega
  · exact (congrArg Fin.val (next.keepsReg (by decide : count.keeps 5=true))).trans dest'
  · change readings t 15 = words.length
    rw [hr,clen]
    simp (config := {decide := true}) [count,Code.block,Code.evalNat,addressOp,cur,dest']

/-- The complete native scalar call has exactly one successful trace, independently of
the value of the field element. Its final event reads precisely the newly packed words. -/
theorem run (s : Bank w) (m : Memory w) (bits : List Bool) (hw : 0 < w)
    (width : readings s 2 = w) (base : readings s 3 = src) (len : readings s 4 = bits.length)
    (dest : readings s 5 = dst) (source : CompactWrite.Source m src bits)
    (separate : CompactWrite.Disjoint src bits.length dst (CompactFrame.pack w bits).length)
    (srcFit : src+bits.length ≤ 2^w) (dstFit : dst+(CompactFrame.pack w bits).length ≤ 2^w)
    (countFit : (CompactFrame.pack w bits).length < 2^w)
    (scalar : ∀ bs, macros 1 (CompactFrame.pack w bits) bs = if bs.isEmpty then some .plus else none) :
    let words := CompactFrame.pack w bits
    let mem := putWords m dst words
    ∃ pre t, Runs pub macros prepare s m pre t mem ∧ Runs pub macros code s m (pre++[event dst words]) t mem ∧
      traceCost (pre++[event dst words]) ≤ CompactWrite.setup.slots+(CompactWrite.step.slots+1)*bits.length+
        2+count.slots+1+words.length ∧
      ∀ es u mu, Runs pub macros code s m es u mu → es=pre++[event dst words] ∧ u=t ∧ mu=mem := by
  intro words mem
  obtain ⟨pre,t,prep,cost,pointer,size⟩ := prepare_run (pub:=pub) (macros:=macros)
    s m bits hw width base len dest source separate srcFit dstFit countFit
  change (t 15).val = words.length at size
  change Runs pub macros prepare s m pre t mem at prep
  have read : TeamRAM.previous mem (.burst dst words.length) = words := CompactWrite.previous_putWords ..
  have called : Runs pub macros (.call 1 5 15) t mem [event dst words] t mem := by
    rw [private_iff]
    dsimp only
    rw [pointer,size,read]
    exact ⟨dstFit,rfl,rfl,([], .plus),by simpa only [List.isEmpty_nil,ite_true] using scalar [],rfl⟩
  refine ⟨pre,t,prep,prep.seq called,?_,?_⟩
  · rw [show traceCost (pre++[event dst words]) = traceCost pre + traceCost [event dst words] from VPVNP.RAMBuckets.cost_append ..]
    change traceCost pre + (1 + words.length + 0) ≤ _
    omega
  · intro es u mu r
    obtain ⟨v,mv,gs,fs,rfl,first,last⟩ := Runs.seq_iff.mp r
    obtain ⟨rfl,rfl,rfl⟩ := prep.unique_of_deterministic (by decide) first
    obtain ⟨_,rfl,rfl,o,path,rfl⟩ := private_iff.mp last
    rw [pointer,size,read,scalar] at path
    obtain ⟨choices,sign⟩ : o.1=[] ∧ o.2=.plus := by
      cases h : o.1 <;> simp_all
    rw [pointer,size,read,choices,sign]
    exact ⟨rfl,rfl,rfl⟩

end RoutingISA.FiniteScalarCall

end BorderVNP
end Computability
end OAI
