import OAI.Computability.BorderVNP.CubeISAHeaderDecodeFrame
import OAI.Computability.BorderVNP.CubeISAHeaderDecodeTotals

/-! # The complete native common-header declaration decoder

The program reads the coordinate and the packed upper-triangular words, writes
the full claimed table, and computes the ordinary column sums in a separate
array. Its success predicate checks every source word in its actual bit range.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.HeaderDecode

open VPVNP.BurstRAM Cube.DeclarationBits Cube.SelectorRead Finset

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

private theorem begin_run (l : Layout) (old : ℕ → ℕ) (s : Bank w) (m : Memory w)
    (room : Fits l w) (hs : Initial l old (.ofWords s m))
    (rank : readings s 43 = (decoded old l.source l.cw).val) :
    BoundedRun pub mac beginRows s m beginRows.slots (State l old 0) := by
  let z := NatState.ofWords s m
  have v20 : z.reg 20 = l.cw := hs.fixed.cw
  have v21 : z.reg 21 = l.rw := hs.fixed.rw
  have v22 : z.reg 22 = l.header+5 := hs.fixed.chosen
  have v23 : z.reg 23 = 0 := hs.cursor
  have v24 : z.reg 24 = l.source := hs.source
  have v25 : z.reg 25 = 1 := hs.fixed.one
  have v34 : z.reg 34 = l.cap := hs.fixed.cap
  have v43 : z.reg 43 = (decoded old l.source l.cw).val := rank
  have hm : z.mem = old := hs.memory
  have end0 : l.source+l.cw = l.start 0 := by simp [Layout.start,fieldStart,fieldsBefore]
  have small : l.source+l.cw < 2^w := end0 ▸ (l.start_mono (Nat.zero_le _)).trans_lt room.stream
  have safe : beginRows.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [beginRows,Code.block,Code.fixedSafe,Code.safeReadOnly,Code.fixedEval,
      Code.evalNat,addressOpFits,v20,v24,v25,v34,small,room.bound]
  apply (beginRows.runFixed pub mac s m safe).mono le_rfl
  rintro t ht
  rw [ht]
  change State l old 0 (beginRows.fixedEval (readings pub) z)
  have keep (j : Reg) (hj : j ≠ 24 ∧ j ≠ 41 ∧ j ≠ 42) :
      (beginRows.fixedEval (readings pub) z).reg j = z.reg j := by
    simp [beginRows,Code.block,Code.fixedEval,Code.evalNat,hj.1,hj.2.1,hj.2.2]
  obtain ⟨a,b,c,d,e,f,g,h,i,j,k⟩ := hs.fixed
  refine ⟨⟨(keep 20 (by decide)).trans a,(keep 21 (by decide)).trans b,(keep 22 (by decide)).trans c,
    (keep 25 (by decide)).trans d,(keep 28 (by decide)).trans e,(keep 29 (by decide)).trans f,
    (keep 30 (by decide)).trans g,(keep 31 (by decide)).trans h,(keep 32 (by decide)).trans i,
    (keep 33 (by decide)).trans j,(keep 34 (by decide)).trans k⟩,(keep 23 (by decide)).trans v23,?_,?_,?_,?_⟩
  · simp (config := {decide := true}) [beginRows,Code.block,Code.fixedEval,Code.evalNat,addressOp,v24,v20,end0]
  · simp (config := {decide := true}) [beginRows,Code.block,Code.fixedEval,Code.evalNat,v21]
  · simp (config := {decide := true}) [beginRows,Code.block,Code.fixedEval,Code.evalNat,addressOp,v25,v34]
  · funext x
    by_cases hx : x = l.header+5 <;>
      simp [beginRows,Code.block,Code.fixedEval,Code.evalNat,Layout.image,v22,v43,hm,hx]

private theorem coordinate_run (l : Layout) (old : ℕ → ℕ) (s : Bank w) (m : Memory w)
    (room : Fits l w) (hs : Initial l old (.ofWords s m)) :
    TestRun pub mac reader s m (Cube.SelectorRead.init.slots+l.cw*(Cube.SelectorRead.step.slots+1)+1+(requireLt 43 42).slots)
      (Cube.SelectorRead.Valid old l.source l.cw l.a)
      (fun z => Initial l old z ∧ z.reg 43 = (decoded old l.source l.cw).val) := by
  have end0 : l.source+l.cw = l.start 0 := by simp [Layout.start,fieldStart,fieldsBefore]
  have fit := (end0 ▸ (l.start_mono (Nat.zero_le _)).trans room.stream.le : l.source+l.cw ≤ 2^w)
  have hm : readings m = old := hs.memory
  apply (reader_run (pub := pub) (mac := mac) s m l.source l.cw l.a hs.source hs.width hs.bound
    room.small room.coordWidth fit).mono le_rfl (by rw [hm]) ?_
  rintro z ⟨mem,rank,keep⟩
  obtain ⟨a,b,c,d,e,f,g,h,i,j,k⟩ := hs.fixed
  refine ⟨⟨⟨(keep 20 (by simp [Scratch])).trans a,(keep 21 (by simp [Scratch])).trans b,
    (keep 22 (by simp [Scratch])).trans c,(keep 25 (by simp [Scratch])).trans d,(keep 28 (by simp [Scratch])).trans e,
    (keep 29 (by simp [Scratch])).trans f,(keep 30 (by simp [Scratch])).trans g,(keep 31 (by simp [Scratch])).trans h,
    (keep 32 (by simp [Scratch])).trans i,(keep 33 (by simp [Scratch])).trans j,(keep 34 (by simp [Scratch])).trans k⟩,
    (keep 23 (by simp [Scratch])).trans hs.cursor,(keep 24 (by simp [Scratch])).trans hs.source,
    (keep 41 (by simp [Scratch])).trans hs.width,(keep 42 (by simp [Scratch])).trans hs.bound,
    mem.trans hm⟩,hm ▸ rank⟩

/-- Cost of the coordinate reader and every entry in the rectangular scan. -/
def cost (l : Layout) := setup.slots + (Cube.SelectorRead.init.slots+l.cw*(Cube.SelectorRead.step.slots+1)+1+
  (requireLt 43 42).slots + (beginRows.slots + (l.entries*(entryCost l.rw+1)+1)))

/-- Exact native decoding of every compact field, including rejection of spare
binary codes. The declared table and coordinate are the only changed words. -/
theorem decode_run (l : Layout) (s : Bank w) (m : Memory w) (room : Fits l w)
    (frame : AtFrame l (readings pub) (readings m)) (primary : readings pub 0+63 < 2^w) (header : l.header+12 < 2^w) :
    TestRun pub mac decode s m (cost l) (Valid l (readings m)) (State l (readings m) l.entries) := by
  let old := readings m
  let first := (setup_run pub mac s m l frame room primary header).asTest (by decide)
  let good k := upper l.d l.a k → Cube.SelectorRead.Valid old (l.start k) l.rw (l.cap+1)
  have loop (t : Bank w) (mt : Memory w) (hs : State l old 0 (.ofWords t mt)) :=
    test_counted_loop (pub := pub) (macros := mac) 23 29 step l.entries (fun _ => entryCost l.rw) good (State l old)
      (fun _ _ hz => ⟨hz.cursor,hz.fixed.count⟩)
      (fun k hk u mu hz => step_test l old k u mu room hk hz) 0 (Nat.zero_le _) t mt hs
  apply (first.seq fun t mt hz => (coordinate_run l old t mt room hz).seq fun u mu hp =>
    ((begin_run l old u mu room hp.1 hp.2).asTest (by decide)).seq loop).mono
  · simp [cost]
  · simp [Valid,good,old]
  · exact fun _ hp => hp

/-- Compact decoding followed by the genuine column-total materialization pass. -/
def program : Code := .seq decode HeaderTotals.program

/-- Complete output image of the decoded coordinate, dense claim, and derived totals. -/
def Layout.finalImage (l : Layout) (mem : ℕ → ℕ) :=
  HeaderTotals.image (l.image mem l.entries) l.dense l.totals l.a (l.d*l.d) l.a

/-- The whole decoder including totals returns exactly on valid compact words. It
computes every total in native word operations, bounded by the public cap. -/
theorem program_run (l : Layout) (s : Bank w) (m : Memory w) (room : Fits l w)
    (frame : AtFrame l (readings pub) (readings m)) (primary : readings pub 0+63 < 2^w) (header : l.header+12 < 2^w)
    (totalsRoom : l.totals+l.a ≤ 2^w) (different : l.dense+l.entries ≤ l.totals ∨ l.totals+l.a ≤ l.dense)
    (sumRoom : l.d*l.d*l.cap < 2^w) :
    TestRun pub mac program s m (cost l + HeaderTotals.cost l.a (l.d*l.d)) (Valid l (readings m))
      (fun z => z.mem = l.finalImage (readings m)) := by
  let old := readings m
  have dec := decode_run (pub := pub) (mac := mac) l s m room frame primary header
  have strengthened : TestRun pub mac decode s m (cost l) (Valid l old)
      (fun z => State l old l.entries z ∧ Valid l old) := by
    exact ⟨fun ok => (dec.complete ok).mono le_rfl (fun _ hp => ⟨hp,ok⟩),
      fun r => ⟨(dec.sound r).1,(dec.sound r).2,(dec.sound r).1⟩⟩
  apply (strengthened.seq (b := HeaderTotals.program) (cb := HeaderTotals.cost l.a (l.d*l.d))
    (ob := True) (Q := fun z => z.mem = l.finalImage old) ?_).mono le_rfl (by simp [old]) (fun _ hp => hp)
  rintro t mt ⟨hs,valid⟩
  have hm : readings mt = l.image old l.entries := hs.memory
  have bounded (j : ℕ) (hj : j < l.a) (k : ℕ) (hk : k < l.d*l.d) :
      readings mt (l.dense+k*l.a+j) ≤ l.cap := by
    have key : k*l.a+j < l.entries := by
      calc _ < (k+1)*l.a := by rw [Nat.add_mul]; omega
           _ ≤ _ := Nat.mul_le_mul_right _ hk
    rw [hm]
    have inside : l.dense ≤ l.dense+k*l.a+j ∧ l.dense+k*l.a+j < l.dense+l.entries := by omega
    simp only [Layout.image,ite_eq_left inside,show l.dense+k*l.a+j-l.dense = k*l.a+j by omega,Layout.value]
    split
    · exact Nat.le_of_lt_succ ((valid.2 _ key ‹_›).2)
    · exact Nat.zero_le _
  apply ((HeaderTotals.run pub mac t mt l.dense l.totals l.a (l.d*l.d) l.cap hs.fixed.dense hs.fixed.totals
    hs.fixed.a hs.fixed.rows (by have := room.small; omega) room.denseEnd totalsRoom different sumRoom bounded).asTest (by decide)).mono
    le_rfl Iff.rfl
  intro z hz
  simpa only [hm,Layout.finalImage] using hz

end RoutingISA.HeaderDecode

end BorderVNP
end Computability
end OAI
