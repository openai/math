import OAI.Computability.BorderVNP.CellPacketFinishSuffix
import OAI.Computability.BorderVNP.RoutingISARegisterFrame
import OAI.Computability.BorderVNP.RoutingISACompactWriteBurst

/-! # Packing the completed sparse envelope on the physical RAM -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket

open VPVNP.BurstRAM RationalHitting.StackLanguage CellPacketEncode Packing.Directory.ISA

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- The unframed external suffix follows the self-delimiting command packet. -/
def envelope (p ext : List Bool) := codeWord p ++ ext

/-- Splitting the scratch interval at the cursor reached by the chunk loop. -/
theorem envelope_eq (p ext : List Bool) : envelope p ext = pairWord p ++ ([true]++ext) := by
  simp only [envelope,codeWord_pair,List.append_assoc]

/-- Scratch cells occupied by the marker and external assignments after the chunk loop. -/
def suffixMemory (m : Memory w) (cursor : ℕ) (ext : List Bool) : Memory w :=
  putWords m cursor (([true]++ext).map fun b => DiagonalResidueRAM.word w b.toNat)

/-- Join an already initialized bit interval to the chronological suffix stores. -/
theorem source_append_stores {m m' : Memory w} (src : ℕ) (xs ys : List Bool)
    (left : CompactWrite.Source m src xs)
    (right : readings m' = putDigits (readings m) (src+xs.length) ys) :
    CompactWrite.Source m' src (xs++ys) := by
  intro i hi
  change readings m' (src+i) = _
  rw [right]
  by_cases h : i < xs.length
  · rw [putDigits_outside _ _ _ _ (Or.inl (by omega)),List.getElem_append_left h]
    exact left i h
  · have hi' : i-xs.length < ys.length := by simp only [List.length_append] at hi; omega
    rw [show src+i = src+xs.length+(i-xs.length) by omega, List.getElem_append_right (by omega)]
    exact putDigits_read _ _ _ ⟨i-xs.length,hi'⟩

/-- Fill the four compact-writer input registers from the enclosing packet controls. -/
def packSetup : Code := .block [.copy 2 8, .copy 3 6, .binary .sub 4 20 6, .copy 5 7]

private theorem packSetup_run (s : Bank w) (m : Memory w) (src dst n : ℕ)
    (width : readings s 8 = w) (source : readings s 6 = src) (destination : readings s 7 = dst)
    (cursor : readings s 20 = src+n) :
    BoundedRun pub macros packSetup s m 4 (fun z =>
      z.reg 2 = w ∧ z.reg 3 = src ∧ z.reg 4 = n ∧ z.reg 5 = dst ∧ z.mem = readings m) := by
  have safe : packSetup.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [packSetup, Code.block, Code.fixedSafe, Code.fixedEval,
      Code.evalNat, Code.safeReadOnly, addressOpFits, NatState.ofWords, source, cursor]
  apply (packSetup.runFixed pub macros s m safe).mono le_rfl
  rintro _ rfl
  simp (config := {decide := true}) [packSetup, Code.block, Code.fixedEval, Code.evalNat,
    addressOp, NatState.ofWords, width,source,destination,cursor]

/-- The native packed-word writer retains the width, payload size and final burst base. -/
theorem pack_run (s : Bank w) (m : Memory w) (src dst : ℕ) (bs : List Bool) (hw : 0 < w)
    (width : readings s 8 = w) (source : readings s 6 = src) (destination : readings s 7 = dst)
    (cursor : readings s 20 = src+bs.length) (digits : CompactWrite.Source m src bs)
    (apart : CompactWrite.Disjoint src bs.length dst (CompactFrame.pack w bs).length)
    (srcFit : src+bs.length ≤ 2^w) (dstFit : dst+(CompactFrame.pack w bs).length ≤ 2^w) :
    BoundedRun pub macros (.seq packSetup CompactWrite.writer) s m
      (4+(CompactWrite.setup.slots+(CompactWrite.step.slots+1)*bs.length+2)) (fun z =>
        z.reg 2 = w ∧ z.reg 4 = bs.length ∧ z.reg 5 = dst ∧
        z.mem = readings (putWords m dst (CompactFrame.pack w bs))) := by
  apply (packSetup_run (pub := pub) (macros := macros) s m src dst bs.length width source destination cursor).seq
  rintro t mt ⟨h2,h3,h4,h5,hm⟩
  have memory : mt = m := funext fun i => Fin.ext (congrFun hm i)
  subst mt
  obtain ⟨es,v,r,cost⟩ := CompactWrite.writer_runs (pub := pub) (macros := macros) t m bs hw
    h2 h3 h4 h5 digits apart srcFit dstFit
  exact ⟨es,v,_,r,cost,(congrArg Fin.val (r.keepsReg (k := 2) (by decide))).trans h2,
    (congrArg Fin.val (r.keepsReg (k := 4) (by decide))).trans h4,
    (congrArg Fin.val (r.keepsReg (k := 5) (by decide))).trans h5,rfl⟩

end RoutingISA.CellPacket

end BorderVNP
end Computability
end OAI
