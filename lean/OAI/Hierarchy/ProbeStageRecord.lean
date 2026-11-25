import OAI.Hierarchy.ProbeStageRankUpdate
import OAI.Hierarchy.ProbeStageFastField
import OAI.Hierarchy.ProbeStageFallback

namespace OAI
/-! # The physical color-and-rank procedure for one chronological tile -/

namespace Hierarchy.ProbeStage.Record
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Fin.CommRing

/-- The fixed-address updates are evaluated left to right, against the actual modified memory. -/
structure Write where
  dst : ℕ
  val : Formula 1

def chain (w : ℕ) : List Write → Procedure w → Procedure w
  | [],p => p
  | a::rest,p => (WordStore.put w a.dst a.val).seq (chain w rest p)

def writes {w : ℕ} : List Write → Memory w → Memory w
  | [],m => m
  | a::rest,m => writes rest (RankUpdate.assign a.dst a.val m)

def writeCost (xs : List Write) := (xs.map (fun a => 2*a.val.work+8)).sum

theorem chain_exec {w : ℕ} (xs : List Write) (p : Procedure w) (m o : Memory w) (t : ℕ)
    (fit : ∀ x∈xs, x.dst+1<2^w) (tail : p.Exec (writes xs m) o t) :
    (chain w xs p).Exec m o (writeCost xs+t) := by
  induction xs generalizing m with
  | nil =>
    simp only [chain,writeCost,List.map_nil,List.sum_nil,Nat.zero_add]
    exact tail
  | cons x xs ih =>
    change ((WordStore.put w x.dst x.val).seq (chain w xs p)).Exec m o (writeCost (x::xs)+t)
    rw [show writeCost (x::xs)+t=(2*x.val.work+8)+(writeCost xs+t) by simp [writeCost,Nat.add_assoc]]
    apply Procedure.Exec.then (WordStore.execute x.dst x.val m (fit x (by simp)))
    exact ih (RankUpdate.assign x.dst x.val m) (fun y hy => fit y (by simp [hy])) tail

/-- The actual three row descriptor cells, and the three result cells, for this ordinal. -/
structure Row where
  leftID : ℕ
  rightID : ℕ
  stringID : ℕ
  chosen : ℕ
  enterRank : ℕ
  exitRank : ℕ

/-- Six literal directory tables translate typed block/string indices to physical offsets. -/
structure Advice where
  leftCounts : ℕ
  rightCounts : ℕ
  leftMasks : ℕ
  rightMasks : ℕ
  wordOffsets : ℕ
  stringOffsets : ℕ
  strings : ℕ
  leastTable : ℕ
  heads : ℕ
  lengths : ℕ
  offsets : ℕ
  clearing : ℕ
  degree : ℕ
  quota : ℕ
  length : ℕ
  width : ℕ
  chunks : ℕ

structure Scratch where
  leftCount : ℕ
  rightCount : ℕ
  leftMask : ℕ
  rightMask : ℕ
  wordOffset : ℕ
  stringOffset : ℕ
  bit : ℕ
  remaining : ℕ
  address : ℕ
  value : ℕ
  head : ℕ
  count : ℕ

def prepare (a : Advice) (r : Row) (s : Scratch) : List Write :=
  [⟨s.leftCount,RankUpdate.directory a.leftCounts r.leftID⟩,⟨s.rightCount,RankUpdate.directory a.rightCounts r.rightID⟩,
   ⟨s.leftMask,RankUpdate.directory a.leftMasks r.leftID⟩,⟨s.rightMask,RankUpdate.directory a.rightMasks r.rightID⟩,
   ⟨s.wordOffset,RankUpdate.directory a.wordOffsets r.stringID⟩,⟨s.stringOffset,RankUpdate.directory a.stringOffsets r.stringID⟩]

def find (a : Advice) (s : Scratch) : FastField.Layout :=
  ⟨s.leftMask,s.rightMask,s.wordOffset,a.leastTable,s.bit,a.width,a.length,a.chunks⟩

def miss (a : Advice) (s : Scratch) (yes no : Formula 1) : Formula 1 :=
  .select .eq (RankUpdate.cell s.bit) (.lit a.length) yes no

def start (a : Advice) (r : Row) (s : Scratch) : List Write :=
  [⟨r.chosen,miss a s (.lit a.degree) (.load (.op .add (.op .add (.lit a.strings)
    (RankUpdate.cell s.stringOffset)) (RankUpdate.cell s.bit)))⟩,
   ⟨s.remaining,miss a s (.lit a.degree) (.lit 0)⟩]

def fallback (a : Advice) (r : Row) (s : Scratch) : Fallback.Layout :=
  ⟨s.remaining,r.chosen,s.leftCount,s.rightCount,a.quota⟩

def side (a : Advice) (r : Row) (s : Scratch) (left : Bool) : RankUpdate.Layout :=
  ⟨if left then r.enterRank else r.exitRank,if left then s.leftCount else s.rightCount,
    if left then s.leftMask else s.rightMask,r.chosen,s.address,s.value,s.head,s.count,
    a.heads,a.lengths,a.offsets,a.clearing,a.quota⟩

def procedure (w : ℕ) (a : Advice) (s : Scratch) (r : Row) : Procedure w :=
  chain w (prepare a r s) <| (FastField.procedure w (find a s)).seq <| chain w (start a r s) <|
   (Fallback.procedure w (fallback a r s)).seq <| (RankUpdate.procedure w (side a r s true)).seq
      (RankUpdate.procedure w (side a r s false))

/-- External memory entering the real descending-color scan and each of the two scatters. -/
def scanInput {w : ℕ} (a : Advice) (s : Scratch) (r : Row) (m : Memory w) :=
  writes (start a r s) (FastField.image (find a s) (writes (prepare a r s) m))

def leftInput {w : ℕ} (a : Advice) (s : Scratch) (r : Row) (m : Memory w) :=
  Fallback.image (fallback a r s) (scanInput a s r m)

def rightInput {w : ℕ} (a : Advice) (s : Scratch) (r : Row) (m : Memory w) :=
  RankUpdate.image (side a r s true) (leftInput a s r m)

def image {w : ℕ} (a : Advice) (s : Scratch) (r : Row) (m : Memory w) :=
  RankUpdate.image (side a r s false) (rightInput a s r m)

def scans {w : ℕ} (a : Advice) (s : Scratch) (r : Row) (m : Memory w) :=
  ((scanInput a s r m) (s.remaining:Word w).val).val

def clears {w : ℕ} (a : Advice) (s : Scratch) (r : Row) (m : Memory w) :=
  RankUpdate.occurrenceCount (side a r s true) (leftInput a s r m)+
  RankUpdate.occurrenceCount (side a r s false) (rightInput a s r m)

structure Fits (w : ℕ) (a : Advice) (s : Scratch) (r : Row) : Prop where
  prep : ∀ x ∈ prepare a r s, x.dst+1<2^w
  fast : s.bit+1<2^w
  start : ∀ x ∈ Record.start a r s, x.dst+1<2^w
  chosen : r.chosen+1<2^w
  other : (s.remaining:Word w).val ≠ r.chosen
  left : RankUpdate.Fits w (side a r s true)
  right : RankUpdate.Fits w (side a r s false)

/-- The actual record code, including updates at both ends, consumes constant time per mask
chunk, one optional degree-length scan, and linear time in these two literal lists of edits. -/
theorem execute {w : ℕ} (a : Advice) (s : Scratch) (r : Row) (m : Memory w) (fit : Fits w a s r) :
    (procedure w a s r).Exec m (image a s r m)
      (1000+82*a.chunks+100*scans a s r m+18*clears a s r m) := by
  let pre := writes (prepare a r s) m
  let f := find a s
  let a0 := FastField.image f pre
  let scan := scanInput a s r m
  let l := leftInput a s r m
  let rgt := rightInput a s r m
  let ticks (left : Bool) (mem : Memory w) := RankUpdate.setupTicks (side a r s left)+4+18*RankUpdate.occurrenceCount (side a r s left) mem
  let scanCost := scans a s r m*(7+(2*(Fallback.update (fallback a r s)).work+8))+4
  let budget := writeCost (prepare a r s)+(2*(FastField.code f).work+8+(writeCost (start a r s)+(scanCost+(ticks true l+ticks false rgt))))
  have run : (procedure w a s r).Exec m (image a s r m) budget := by
    apply chain_exec _ _ _ _ _ fit.prep
    apply Procedure.Exec.then (FastField.execute f pre fit.fast)
    apply chain_exec _ _ _ _ _ fit.start
    apply Procedure.Exec.then (Fallback.execute (fallback a r s) scan fit.chosen fit.other)
    apply Procedure.Exec.then (RankUpdate.execute (side a r s true) l fit.left)
    exact RankUpdate.execute (side a r s false) rgt fit.right
  apply Procedure.Spec.mono run (fun _ e=>e) (fun _ _ e=>e)
  dsimp only [budget,scanCost,ticks]
  rw [FastField.work]
  change 108+(2*(1+41*a.chunks)+8+( _ + (scans a s r m*_+4+
    (( _+4+18*RankUpdate.occurrenceCount (side a r s true) l)+
    (_+4+18*RankUpdate.occurrenceCount (side a r s false) rgt))))) ≤ _
  simp only [start,miss,writeCost,RankUpdate.cell,Formula.work,Fallback.update,Fallback.count,Fallback.cell,
    RankUpdate.setupTicks,RankUpdate.pointer,RankUpdate.getRank,RankUpdate.increment,RankUpdate.directory,
    RankUpdate.activation,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,clears]
  dsimp only [l,rgt]
  omega

end Hierarchy.ProbeStage.Record

end OAI
