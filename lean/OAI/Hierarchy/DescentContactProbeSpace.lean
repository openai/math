import OAI.Hierarchy.DescentContactPreROMLayout

namespace OAI
/-! # Address bounds of the installed eight-field public contact page -/
namespace Hierarchy.DescentContactPreROM.Layout
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local.Gather
open DescentContactProbeBook DescentFallbackPeriod.Projected
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
set_option quotPrecheck false

variable (A : Layout) {ports w : ℕ} (board : NonlinearExpanders.Graph A.n ports)
  (q : Fin A.sockets) (reads : Fin 8→Expr) (j : Fin A.jobs)
local notation "H" => A.hosts*A.shapes
local notation "G" => A.groups
local notation "M" => A.batch
local notation "b" => A.fieldBits
local notation "term" => A.termPage board q reads j
local notation "mid" => A.mid j.val
local notation "out" => (A.output j.val).base

structure MarkerSpace (w : ℕ) : Prop where
  bounds : Bounds (w:=w) (d:=b) («M» := M) (term).tables reads mid
  lookupFits : (DescentSIMDLookup.lookup (term).menu).Fits w out
  fit : DescentSIMDLookup.Fits (term).menu (b*8) A.outputBits M H G w out
  dictLow : (term).menu.dictionary.base+2^((b*8)*M)≤ mid
  maskLow : (term).menu.mask.base+H*chunks G M≤ mid
  wire : (term).menu.source.base=mid

/-- Every printed binary field table and its lookup dictionary and mask end before this job's
scratch bank. The gathered word and the result use the two disjoint slabs allocated to this job. -/
theorem marker_space (prior : ∀i,(reads i).Fits w A.markerBase) (room : A.endAddress<2^w)
    (packed : M*max (b*8) A.outputBits≤w/2) : MarkerSpace A board q reads j w := by
  let t:=page (A.law board) q reads
  let base:=pageBase 8 b H G M A.markerBase q
  let width:=step 8 b H G M
  have gap:=t.geometry base H G M
  have ends:=page_end (A.law board) H G M A.markerBase q reads
  have bookEnd : t.stop base H G M≤A.scratchBase := by
    calc t.stop base H G M≤t.stop base H G M+1:=Nat.le_succ _
         _=A.markerBase+(q.val+1)*width:=ends
         _≤A.scratchBase:=Nat.add_le_add_left (Nat.mul_le_mul_right width q.isLt) _
  have start : A.scratchBase≤ mid:=Nat.le_add_right ..
  have stopAt : t.stop base H G M≤ mid:=bookEnd.trans start
  have words:=A.block j
  have roomOut : out+A.rows<2^w := (words.2.1.trans words.2.2).trans_lt room
  have wideOut : out<2^w := (Nat.le_add_right out A.rows).trans_lt roomOut
  have moves : mid≤out:=Nat.le_add_right ..
  have wideMid : mid<2^w := moves.trans_lt wideOut
  have previous : A.markerBase≤ mid:=A.ordered.2.2.2.1.trans start
  have gather : Bounds (w:=w) (d:=b) («M» := M) (term).tables reads mid := by
    intro i
    have banks:=DescentPackedZip.Book.geometry t.gate t.unit M base i (gap.2.trans stopAt) wideMid le_rfl
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ previous (prior i),banks.1,banks.2,rfl,rfl⟩
  have inside (c : Bank) (bound : c.base+c.size≤out) : c.Fits w out :=
    ⟨Nat.two_pow_pos _,((Nat.le_add_left c.size c.base).trans bound).trans_lt wideOut,bound⟩
  have dict : (term).menu.dictionary.base+(term).menu.dictionary.size≤ mid :=
    (Nat.le_add_right (t.split base M+2^((b*8)*M)) A.slab).trans stopAt
  have mask : (term).menu.mask.base+(term).menu.mask.size≤ mid := stopAt
  have srcFit : (term).menu.source.Fits w out:=inside _ le_rfl
  have dictFit : (term).menu.dictionary.Fits w out:=inside _ (dict.trans moves)
  have maskFit : (term).menu.mask.Fits w out:=inside _ (mask.trans moves)
  have rowsBound : A.rows≤A.slab:=Nat.le_pow_clog (by decide) _
  exact ⟨gather,⟨⟨dictFit,srcFit,trivial⟩,maskFit,trivial⟩,
    ⟨srcFit,dictFit,maskFit,rowsBound,rfl,rowsBound,roomOut,packed⟩,
    dict,(Nat.add_le_add_left rowsBound (term).menu.mask.base).trans mask,rfl⟩

end
end Hierarchy.DescentContactPreROM.Layout

end OAI
