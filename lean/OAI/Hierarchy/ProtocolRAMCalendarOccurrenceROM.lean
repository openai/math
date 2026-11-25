import OAI.Hierarchy.ProtocolRAMCalendarJointHeader
import OAI.Hierarchy.ProtocolRAMPortROMTable

namespace OAI
/-! # A common finite input tape for every public occurrence directory -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native StockCommit
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section
variable {jobs w z d N k phases attempts : ℕ}



/-- All global overlays have stopped by the end of the last score page, so the
ordinary input tail can contain further finite directories. -/
theorem JointHeader.tail_words (b : JointHeader.Board) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest : Boot.Tape z d) (x : ℕ)
    (first : 2^z≤b.initial) (above : JointHeader.stop b z N k phases≤x) :
    JointHeader.words b z d N k phase π stock rest x=rest x := by
  let rows := GlobalTests.rows z N k
  let sl := FeedROM.sliceBank b.initial rows b.steps b.cap b.width
  let ht := FeedROM.halfBank b.initial rows b.steps b.cap b.width
  have score : ht.base+ht.size≤x :=
    (Nat.le_add_right (JointHeader.scores b z N k).base _).trans above
  have slice := sliceROM_size (b.initial+rows) b.steps (b.cap*b.width+1)
  have addr : sl.base+sl.size=ht.base := rfl
  have hl : sl.base+b.steps*(b.cap*b.width+1)≤x := by
    change b.steps*(b.cap*b.width+1)≤ sl.size at slice
    omega
  have inv : b.initial+rows≤x := by change sl.base≤x;omega
  have root : ¬ x<2^z := by omega
  change b.initial + GlobalTests.rows z N k ≤ x at inv
  change GlobalTests.allPages _ _ _ _ _ _ x=_
  rw [GlobalTests.all_frame _ _ _ _ phase _ x (.inr above)]
  change FeedROM.halfAdvice ht (feedAdvice sl b.steps (b.cap*b.width+1)
    (JointHeader.inventory b z N k stock (Boot.permutationWords π rest))) x=_
  simp only [FeedROM.halfAdvice,feedAdvice,JointHeader.inventory,fillSegment,
    not_lt.mpr score,not_lt.mpr hl,not_lt.mpr inv,and_false,ite_false,Boot.permutationWords,dite_eq_right root]

/-- One authentic native boot with the occurrence tables in the same permutation,
stock and score input. The public directory remains physically readable after
all sampler subdivisions. -/
theorem JointHeader.port_origin (b : JointHeader.Board) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest : Boot.Tape z d) (t : PortROM.Table attempts)
    (v : Fin jobs→Market z d k) {size : ℕ} (layout : Boot.Layout v size)
    (hd : 1≤d) (first : 2^z≤b.initial) (afterPages : JointHeader.stop b z N k phases≤t.base)
    (aboveHeap : heapEnd z d copies≤t.base) (fit : t.stop<2^(wordBits z d copies)) (within : t.stop≤ size)
    (before : ∀j,t.stop≤Boot.low (v j)) (i : Fin attempts) :
    (t.header i).Loaded (Boot.booted v size (JointHeader.words b z d N k phase π stock (t.words rest))) := by
  have raw := t.loaded rest (by unfold wordBits;omega) fit i
  have started := (Boot.start v layout hd π (JointHeader.words b z d N k phase π stock (t.words rest))
    (JointHeader.authentic (N:=N) (k:=k) b phase π stock (t.words rest) first)).2
  apply raw.frame
  intro x lo hi
  have low : t.base≤x := (Nat.le_add_right t.base _).trans lo
  have high := hi.trans_le (t.end_le i)
  have keep := started.kept x (aboveHeap.trans low) (fun j inside =>
    Nat.not_lt_of_ge inside.1 (high.trans_le (before j)))
  rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (high.trans_le within)] at keep
  exact keep.trans (JointHeader.tail_words b phase π stock (t.words rest) x first (afterPages.trans low))

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
