import OAI.Computability.BorderVNP.CellSparseExteriorNativeSpan

/-! # The terminal zero run and the unquoted private report suffix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior.Native

open VPVNP.BurstRAM CellPacketEncode RationalHitting.StackLanguage

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- The raw report tail is read at its actual address, after encoding the
last omitted run in a number of instructions linear in its binary size. -/
theorem finish_run (s : Bank w) (m : Memory w) (width pos tailBase : ℕ) (tail : List Bool)
    (const : Constants (readings s)) (hWidth : readings s 23=width) (hPos : readings s 26=pos)
    (hBase : readings s 24=tailBase) (hLen : readings s 25=tail.length)
    (ordered : pos ≤ width) (tailFit : tailBase+tail.length<2^w)
    (input : CompactWrite.Source m tailBase tail)
    (apart : CompactWrite.Disjoint tailBase tail.length (readings s 20)
      (1+(codeWord (width-pos).bits).length+tail.length))
    (dstFit : readings s 20+1+(codeWord (width-pos).bits).length+tail.length<2^w) :
    BoundedRun pub mac finish s m (11+11*(width-pos).bits.length+7*tail.length)
      (Output (.ofWords s m) (encode width tail pos [])) := by
  have fit : loadTail.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config:={decide:=true}) [loadTail,Code.block,Code.safeReadOnly,Code.evalNat,addressOpFits,
      hBase,hLen,hWidth,hPos,tailFit,ordered]
  obtain ⟨es,t,q,hq,eq⟩ := loadTail.runReadOnly pub mac m s fit
  have regs : readings t 14=tailBase ∧ readings t 15=tailBase+tail.length ∧ readings t 16=width-pos := by
    simp (config:={decide:=true}) [eq,loadTail,Code.block,Code.evalNat,addressOp,hBase,hLen,hWidth,hPos]
  obtain ⟨src,past,num⟩ := regs
  have constants := keeps_constants q (by decide) (by decide) (by decide) const
  have dst : readings t 20=readings s 20 := congrArg Fin.val (q.keepsReg (by decide))
  have pref := prefix_then (pub:=pub) (mac:=mac) (next:=CellPacketCopy.copy false) (suffix:=tail)
    (f:=7*tail.length+1) t m 0 false (width-pos) constants (by decide) constants.1 num
    (by omega) (fun u mu fs qr eff => by
      have offset : readings u 20=readings t 20+(1+(codeWord (width-pos).bits).length) := by
        simpa [NatState.ofWords,Nat.add_comm 1] using eff.cursor
      have source : readings u 14=tailBase := (congrArg Fin.val (qr.keepsReg (by decide))).trans src
      have last : readings u 15=tailBase+tail.length := (congrArg Fin.val (qr.keepsReg (by decide))).trans past
      have disj := split_apart apart
      have bits := eff.source (by simpa [dst,Nat.add_comm 1] using disj.1) input
      apply (CellPacketCopy.copy_run (pub:=pub) (macros:=mac) false u mu tail
        (keeps_constants qr (by decide) (by decide) (by decide) constants) (by omega)
        (fun i => by rw [source]; exact bits i i.isLt) ?_ ?_).mono le_rfl
        (fun z h => ⟨h.2.2.1,h.2.2.2⟩)
      · change CompactWrite.Disjoint (readings u 14) tail.length (readings u 20) tail.length
        simpa [source,offset,dst] using disj.2
      · change readings u 20+tail.length<2^w
        omega)
  obtain ⟨fs,u,mu,g,hg,effect⟩ := pref
  refine ⟨_,u,mu,q.seq g,?_,?_⟩
  · change traceCost es ≤ 3 at hq
    rw [show traceCost (es++fs)=traceCost es+traceCost fs from VPVNP.RAMBuckets.cost_append ..]
    omega
  · exact ⟨effect.cursor.trans (congrArg (·+_) dst),effect.memory.trans (congrArg (fun d => putDigits _ d _) dst)⟩

end RoutingISA.SparseExterior.Native

end BorderVNP
end Computability
end OAI
