import OAI.Hierarchy.DescentInstalledRootMenu
import OAI.Hierarchy.DescentGatheredLookupWords

namespace OAI
/-! # A physical root menu reads its packed data from the preceding shared memory -/
namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local.Gather
open DescentPackedFallbackTree.Image DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
namespace RootTable
variable {N H G M w : ℕ} (t : RootTable N)
local notation "rows" => H*chunks G M

/-- The dyadic bank footprint is paid in the allocator even if the actual number of
rows or counters is not itself a power of two. -/
theorem geometry_at (base mid out : ℕ)
    (input : Bank) (sourceAt : input.base=mid) (sourceBits : input.bits=Nat.clog 2 rows)
    (written : t.stop base H G M≤ mid) (prior : ∀j,(t.reads j).Fits w mid)
    (positioned : mid+RootArena.span rows≤ out) (complete : out+rows<2^w)
    (packed : M*max (t.field*N) t.outputBits≤ w/2) :
    let p:=t.terms base H G M input
    Bounds (w:=w) (d:=t.field) (M:=M) p.tables p.reads mid ∧
    DescentSIMDLookup.Fits p.menu (t.field*N) t.outputBits M H G w out ∧
    p.menu.dictionary.base+2^(t.field*N*M)≤ mid ∧ p.menu.mask.base+rows≤ mid := by
  let menu:=t.terms base H G M input
  have head:=t.geometry base H G M
  have wide:out<2^w:=by omega
  have midRoom:mid<2^w:=by omega
  have suffix: t.split base M+2^(t.field*N*M)+RootArena.span rows≤ mid:=written
  have cover:rows≤ RootArena.span rows:=RootArena.le_span rows
  have before {v : Bank} (bound : v.base+v.size≤ out) : v.Fits w out :=
    ⟨Nat.two_pow_pos _,by omega,bound⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    have⟨shift,gate⟩:=Book.geometry t.gate t.unit M base i (head.2.trans written) midRoom le_rfl
    exact ⟨prior i,shift,gate,rfl,rfl⟩
  · refine ⟨before ?_,before ?_,before ?_,?_,rfl,?_,complete,packed⟩
    · simpa only [terms,banks,Bank.size,sourceAt,sourceBits,RootArena.span] using positioned
    · change t.split base M+2^(t.field*N*M)≤ out
      omega
    · change t.split base M+2^(t.field*N*M)+RootArena.span rows≤ out
      omega
    · change rows≤2^input.bits
      simpa only [sourceBits,RootArena.span] using cover
    · exact cover
  · change t.split base M+2^(t.field*N*M)≤ mid
    omega
  · change t.split base M+2^(t.field*N*M)+rows≤ mid
    omega

/-- The selected lookup writes its output above its input. In particular its gathered
operand vector is physically resident after the last instruction. -/
theorem middle_words (base mid out : ℕ) (input : Bank) (mem : Memory w)
    (value : Fin H→Fin G→Fin N→Cell t.field)
    (bounds : Bounds (w:=w) (d:=t.field) (M:=M) (t.terms base H G M input).tables t.reads mid)
    (constants : ∀i,Static ((t.terms base H G M input).tables i) (setField (d:=t.field) i) M mem)
    (source : ∀i,Source (t.reads i) (fun v g=> value v g i) M mem)
    (separate : mid+rows≤ out) (q : Row H G M) :
    let menu:=t.terms base H G M input
    let midMem:=image mid rows (assembly menu.tables t.reads) mem
    imageBank H G M out menu.menu midMem (mid+(row H G M q).val)=
      ((data (fun v g=> encode t.field N (value v g)) q).val:Word w) := by
  let menu:=t.terms base H G M input
  let j:=row H G M q
  have seen:=collected menu.tables t.reads mid bounds mem constants value source (List.finRange N)
  have addr:mid+j.val< out:=lt_of_lt_of_le (Nat.add_lt_add_left j.isLt mid) separate
  apply (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl addr)).trans
  apply (ProtocolRAMGeneratedWrite.read_image _ _ _ _ j).trans
  simpa only [assembly,List.mem_finRange,ite_true] using seen q

theorem evaluated (base mid out : ℕ) (input : Bank) (sourceAt : input.base=mid)
    (sourceBits : input.bits=Nat.clog 2 rows) (written : t.stop base H G M≤ mid)
    (prior : ∀j,(t.reads j).Fits w mid) (positioned : mid+RootArena.span rows≤ out) (complete : out+rows<2^w)
    (packed : M*max (t.field*N) t.outputBits≤ w/2) (pos : 0< M) (mem : Memory w)
    (actual : (t.literals base H G M w).Resident mem) (value : Fin H→Fin G→Fin N→Cell t.field)
    (source : ∀i,Source (t.reads i) (fun v g=> value v g i) M mem) :
    let menu:=t.terms base H G M input
    let emitter:=assembly menu.tables t.reads
    let dst:=imageBank H G M out menu.menu (image mid rows emitter mem)
    ∀v g,digit t.outputBits (lane g pos).val (dst (out+(row H G M (position v g pos)).val)).val=
      (t.law (encode t.field N (value v g))).val := by
  obtain ⟨bounds,fit,dict,mask⟩:=t.geometry_at base mid out input sourceAt sourceBits written prior positioned complete packed
  have short:t.stop base H G M<2^w:=by omega
  obtain ⟨gates,lut⟩:=t.resident_at base input mem short actual
  let p:=t.terms base H G M input
  let emit:=t.law ∘ (encode t.field N)
  have twisted : (emit ∘ (encode t.field N).symm)=t.law:=by funext z;simp [emit]
  have room:mid+rows<2^w:=by have:=RootArena.le_span rows;omega
  exact (DescentIssuedGoodHeaders.gathered_words emit p.tables t.reads p.menu mid out value pos mem
    bounds gates source room fit (twisted.symm ▸ lut) dict mask sourceAt).2.2.1

end RootTable
end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
