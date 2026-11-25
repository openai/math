import OAI.Computability.BorderVNP.CellSparseExteriorNativeFields

/-! # The native reads and writes for one live sparse exterior interval -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior.Native

open VPVNP.BurstRAM CellPacketEncode RationalHitting.StackLanguage

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- A list marker and canonical binary gap precede an arbitrary next output
field. The caller has both the real prefix execution and its bit image. -/
theorem prefix_then {next : Code} {suffix : List Bool} {f : ℕ} (s : Bank w) (m : Memory w)
    (v : Reg) (b : Bool) (a : ℕ) (const : Constants (readings s)) (distinct : v ≠ 20)
    (bit : readings s v=b.toNat) (count : readings s 16=a)
    (room : readings s 20+1+(codeWord a.bits).length<2^w)
    (more : ∀ t mt es, Runs pub mac (.seq (emit false v) gap) s m es t mt →
      Output (.ofWords s m) ([b]++codeWord a.bits) (.ofWords t mt) →
      BoundedRun pub mac next t mt f (Output (.ofWords t mt) suffix)) :
    BoundedRun pub mac (.seq (emit false v) (.seq gap next)) s m (4+(11*a.bits.length+3+f))
      (Output (.ofWords s m) (b::(codeWord a.bits++suffix))) := by
  obtain ⟨es,t,mt,r,hr,first⟩ := marker_run (pub:=pub) (mac:=mac) v b s m const distinct bit (by omega)
  have cursor : readings t 20=readings s 20+1 := first.cursor
  obtain ⟨fs,z,mz,g,hg,second⟩ := gap_run (pub:=pub) (mac:=mac) t mt a
    (keeps_constants r (by rfl) (by rfl) (by rfl) const)
    ((congrArg Fin.val (r.keepsReg (by rfl : (emit false v).keeps 16=true))).trans count) (by omega)
  obtain ⟨gs,u,mu,q,hq,third⟩ := more z mz _ (r.seq g) (first.append second)
  refine ⟨_,_,_,r.seq (g.seq q),?_,first.append (second.append third)⟩
  rw [show traceCost (es++(fs++gs))=traceCost es+traceCost (fs++gs) from VPVNP.RAMBuckets.cost_append ..,
    show traceCost (fs++gs)=traceCost fs+traceCost gs from VPVNP.RAMBuckets.cost_append ..]
  omega

/-- All three addresses and their values are the true physical descriptor. -/
structure Row {w : ℕ} (m : Memory w) (atWord : ℕ) (s : Span) : Prop where
  logical : readings m atWord=s.start
  physical : readings m (atWord+1)=s.source
  length : readings m (atWord+2)=s.bits.length

/-- Native execution for one complete span. The descriptor cursor advances
three words and the logical cursor advances directly to the end of the live
bits. The trace bound depends on the binary width of the gap. -/
theorem span_run (s : Bank w) (m : Memory w) (r : Span) (p pos : ℕ)
    (const : Constants (readings s)) (atRow : readings s 21=p) (logical : readings s 26=pos)
    (row : Row m p r) (ordered : pos ≤ r.start)
    (input : r.Reads m)
    (tableFit : p+3<2^w) (srcFit : r.source+r.bits.length<2^w) (logicalFit : r.stop<2^w)
    (apart : CompactWrite.Disjoint r.source r.bits.length (readings s 20)
      (1+(codeWord (r.start-pos).bits).length+(codeWord r.bits).length))
    (dstFit : readings s 20+1+(codeWord (r.start-pos).bits).length+(codeWord r.bits).length<2^w) :
    BoundedRun pub mac span s m (19+11*(r.start-pos).bits.length+7*r.bits.length) (fun z =>
      z.reg 21=p+3 ∧ z.reg 26=r.stop ∧
      Output (.ofWords s m) (true::(codeWord (r.start-pos).bits++codeWord r.bits)) z) := by
  have fit : loadSpan.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config:={decide:=true}) [loadSpan,Code.block,Code.safeReadOnly,Code.evalNat,addressOp,
      addressOpFits,const.2.1,atRow,logical,row.logical,row.physical,Nat.add_assoc,row.length]
    change r.start+r.bits.length<2^w at logicalFit
    omega
  obtain ⟨es,t,q,hq,eq⟩ := loadSpan.runReadOnly pub mac m s fit
  have regs : readings t 14=r.source ∧ readings t 15=r.source+r.bits.length ∧
      readings t 16=r.start-pos ∧ readings t 21=p+3 ∧ readings t 26=r.stop := by
    simp (config:={decide:=true}) [eq,loadSpan,Code.block,Code.evalNat,addressOp,const.2.1,
      atRow,logical,row.logical,row.physical,Nat.add_assoc,row.length,Span.stop]
  obtain ⟨src,past,num,ptr,logical'⟩ := regs
  have constants := keeps_constants q (by decide) (by decide) (by decide) const
  have dst : readings t 20=readings s 20 := congrArg Fin.val (q.keepsReg (by decide))
  have pref := prefix_then (pub:=pub) (mac:=mac) (next:=value) (suffix:=codeWord r.bits)
    (f:=7*r.bits.length+3) t m 1 true (r.start-pos) constants (by decide) constants.2.1 num
    (by omega) (fun u mu fs qr eff => by
      have offset : readings u 20=readings t 20+(1+(codeWord (r.start-pos).bits).length) := by
        simpa [NatState.ofWords,Nat.add_comm 1] using eff.cursor
      have source : readings u 14=r.source := (congrArg Fin.val (qr.keepsReg (by decide))).trans src
      have last : readings u 15=r.source+r.bits.length := (congrArg Fin.val (qr.keepsReg (by decide))).trans past
      have disj := split_apart apart
      apply value_run u mu r.bits (keeps_constants qr (by decide) (by decide) (by decide) constants)
        (by omega)
      · rw [source]
        apply eff.source _ input
        simpa [dst,Nat.add_comm 1] using disj.1
      · simpa [source,offset,dst] using disj.2
      · omega)
  obtain ⟨fs,u,mu,g,hg,effect⟩ := pref
  refine ⟨_,u,mu,q.seq g,?_,(congrArg Fin.val (g.keepsReg (by decide))).trans ptr,
    (congrArg Fin.val (g.keepsReg (by decide))).trans logical',?_⟩
  · change traceCost es ≤ 9 at hq
    rw [show traceCost (es++fs)=traceCost es+traceCost fs from VPVNP.RAMBuckets.cost_append ..]
    omega
  · exact ⟨effect.cursor.trans (congrArg (·+_) dst),effect.memory.trans (congrArg (fun d => putDigits _ d _) dst)⟩

end RoutingISA.SparseExterior.Native

end BorderVNP
end Computability
end OAI
