import OAI.Computability.BorderVNP.CellSparseExteriorNativeLayout
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # Complete execution of the sparse exterior writer on a real cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior.Native

open VPVNP.BurstRAM CellPacketEncode RationalHitting.StackLanguage

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- Cost for the loop and its terminal case. No term is proportional to the
logical width of an omitted interval. -/
def ticks (w : ℕ) (ss : List Span) (tail : List Bool) :=
  (20+11*w)*(ss.length+1)+7*(ss.map fun r => r.bits.length).sum+7*tail.length

private theorem scan_run (s : Bank w) (m : Memory w) (table width pos tb : ℕ) (ss : List Span) (tail : List Bool)
    (const : Constants (readings s)) (ptr : readings s 21=table) (past : readings s 22=table+3*ss.length)
    (logical : readings s 26=pos) (dense : readings s 23=width)
    (base : readings s 24=tb) (len : readings s 25=tail.length) (ordered : Ordered width pos ss)
    (stored : Stored m table tb ss tail)
    (room : Room w table tb (readings s 20) (encode width tail pos ss).length ss tail) :
    BoundedRun pub mac (.seq (.whileLt 21 22 span) finish) s m (ticks w ss tail)
      (Output (.ofWords s m) (encode width tail pos ss)) := by
  have bound : width<2^w := dense ▸ (s 23).isLt
  induction ss generalizing s m table pos with
  | nil =>
    have sep : CompactWrite.Disjoint tb tail.length (readings s 20)
        (1+(codeWord (width-pos).bits).length+tail.length) := by
      simpa [encode,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using room.reportApart
    have fit := room.outputFits
    simp only [encode,List.length_cons,List.length_append] at fit
    obtain ⟨es,t,mt,g,hg,effect⟩ := finish_run (pub:=pub) (mac:=mac) s m width pos tb tail
      const dense logical base len ordered room.reportFits stored.reports sep (by omega)
    have guard : ¬s 21 < s 22 := by change ¬readings s 21 < readings s 22; simp [ptr,past]
    refine ⟨_,t,mt,(Runs.whileDone guard).seq g,?_,effect⟩
    change 1+traceCost es ≤ ticks w [] tail
    have bits : (width-pos).bits.length ≤ w := Nat.size_eq_bits_len _ ▸
      Nat.size_le.mpr ((Nat.sub_le width pos).trans_lt bound)
    simp only [ticks,List.length_nil,Nat.zero_add,Nat.mul_one,List.map_nil,List.sum_nil,Nat.mul_zero,Nat.add_zero]
    omega
  | cons r rs ih =>
    let first := recordBits pos r
    let rest := encode width tail r.stop rs
    have split : encode width tail pos (r::rs)=first++rest := encode_cons ..
    rw [split,List.length_append] at room
    have tab := room.tableFits
    have source := stored.sources r List.mem_cons_self
    have after := ordered_bound ordered.2
    have row : Row m table r := by simpa using stored.rows ⟨0,by simp⟩
    have sep := (split_apart (room.sourcesApart r List.mem_cons_self)).1
    have fit := room.outputFits
    have hfirst : first.length=1+(codeWord (r.start-pos).bits).length+(codeWord r.bits).length := record_length ..
    rw [hfirst] at sep fit
    simp only [List.length_cons,Nat.mul_succ] at tab past
    obtain ⟨es,t,mt,g,hg,pointer,position,effect⟩ := span_run (pub:=pub) (mac:=mac) s m r table pos
      const ptr logical row ordered.1 source (by omega) (room.sourcesFit r List.mem_cons_self)
      (after.trans_lt bound) sep (by omega)
    have output : Output (.ofWords s m) first (.ofWords t mt) := effect
    have cursor : readings t 20=readings s 20+first.length := output.cursor
    have carry (j : Reg) (hj : span.keeps j=true) : readings t j=readings s j := congrArg Fin.val (g.keepsReg hj)
    have room' : Room w (table+3) tb (readings t 20) rest.length rs tail := cursor ▸ room.next
    have past' : readings t 22=table+3+3*rs.length := by rw [carry 22 (by decide),past]; omega
    obtain ⟨fs,u,mu,remaining,hr,more⟩ := ih t mt (table+3) r.stop
      (keeps_constants g (by decide) (by decide) (by decide) const) pointer past' position
      ((carry 23 (by decide)).trans dense) ((carry 24 (by decide)).trans base)
      ((carry 25 (by decide)).trans len) ordered.2 (stored.next room output) room'
    have bits : (r.start-pos).bits.length ≤ w := Nat.size_eq_bits_len _ ▸ Nat.size_le.mpr
      ((Nat.sub_le ..).trans_lt ((Nat.le_add_right r.start r.bits.length).trans_lt (after.trans_lt bound)))
    have guard : s 21<s 22 := show readings s 21<readings s 22 by omega
    cases remaining with
    | atom hc _ _ => contradiction
    | @seq _ _ _ _ vs _ _ ws _ _ before last =>
      refine ⟨_,_,_,(Runs.whileStep guard g before).seq last,?_,split ▸ output.append more⟩
      rw [show traceCost (_++ws)=traceCost _+traceCost ws from VPVNP.RAMBuckets.cost_append ..]
      change 1+traceCost (es++vs)+traceCost ws ≤ _
      rw [show traceCost (es++vs)=traceCost es+traceCost vs from VPVNP.RAMBuckets.cost_append ..]
      rw [show traceCost (vs++ws)=traceCost vs+traceCost ws from VPVNP.RAMBuckets.cost_append ..] at hr
      simp only [ticks,List.length_cons,List.map_cons,List.sum_cons,Nat.mul_succ,Nat.mul_add] at hr ⊢
      omega

/-- The full program reads the actual sorted three-word table, serializes only
its live bits, and appends the raw report suffix. The output cursor is exactly
the exclusive end of the encoded exterior. -/
theorem write_run (s : Bank w) (m : Memory w) (table width tb : ℕ) (ss : List Span) (tail : List Bool)
    (wide : 2<2^w) (ptr : readings s 21=table) (past : readings s 22=table+3*ss.length)
    (dense : readings s 23=width) (base : readings s 24=tb) (len : readings s 25=tail.length)
    (ordered : Ordered width 0 ss) (stored : Stored m table tb ss tail)
    (room : Room w table tb (readings s 20) (encode width tail 0 ss).length ss tail) :
    BoundedRun pub mac write s m (4+ticks w ss tail)
      (Output (.ofWords s m) (encode width tail 0 ss)) := by
  have safe : initRegs.safeReadOnly w (readings pub) (readings m) (readings s) := by
    change (0 < 2^w ∧ 1 < 2^w ∧ 2 < 2^w ∧ 0 < 2^w)
    omega
  obtain ⟨es,t,g,hg,regs⟩ := initRegs.runReadOnly pub mac m s safe
  have carry (j : Reg) (hj : initRegs.keeps j=true) : readings t j=readings s j := congrArg Fin.val (g.keepsReg hj)
  have state : Constants (readings t) ∧ readings t 26=0 := by
    simp (config:={decide:=true}) [Constants,regs,initRegs,Code.block,Code.evalNat]
  have dst := carry 20 (by decide)
  obtain ⟨fs,z,mz,q,hq,out⟩ := scan_run (pub:=pub) (mac:=mac) t m table width 0 tb ss tail state.1
    ((carry 21 (by decide)).trans ptr) ((carry 22 (by decide)).trans past) state.2
    ((carry 23 (by decide)).trans dense) ((carry 24 (by decide)).trans base)
    ((carry 25 (by decide)).trans len) ordered stored (dst ▸ room)
  exact ⟨_,z,mz,g.seq q,(VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add hg hq),
    ⟨out.cursor.trans (congrArg (·+_) dst),out.memory.trans (congrArg (fun d => putDigits _ d _) dst)⟩⟩

end RoutingISA.SparseExterior.Native

end BorderVNP
end Computability
end OAI
