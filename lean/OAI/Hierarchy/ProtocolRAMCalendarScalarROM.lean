import OAI.Hierarchy.ProtocolRAMCalendarOccurrenceROM
import OAI.Hierarchy.ProtocolRAMScalarROMTable

namespace OAI
/-! # The true scalar phase-price pages share one finite input with the port directories -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native
open ThreeFlat.RAM
open scoped Fin.CommRing Classical
noncomputable section
variable {phases w z d N k jobs shapes : ℕ}



/-- A pre-existing core catalogue in the finite interval between the
permutation bank and the initial-stock bank survives every later ROM overlay.
This applies directly to the remap, supergroup, site, and core descriptor words. -/
theorem JointHeader.core_words (b : JointHeader.Board) (score : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest : Boot.Tape z d)
    (port : PortROM.Table shapes) (t : ScalarROM.Table phases)
    (portsAfter : b.initial≤port.base) (pricesAfter : port.stop≤t.base)
    (x : ℕ) (lo : 2^z≤x) (hi : x<b.initial) :
    JointHeader.words b z d N k score π stock (port.words (t.words rest)) x=rest x := by
  let rows := GlobalTests.rows z N k
  let raw := port.words (t.words rest)
  have under : x<b.initial+rows := hi.trans_le (Nat.le_add_right ..)
  have portAt := hi.trans_le portsAfter
  have scalarAt := portAt.trans_le ((Nat.le_add_right port.base _).trans pricesAfter)
  rw [JointHeader.below_scores b score π stock raw x (under.trans_le (JointHeader.order b z N k))]
  rw [JointHeader.lowData,FeedROM.before_stock _ _ _ _ _ _ _ under]
  simp only [JointHeader.inventory,fillSegment,not_le.mpr hi,false_and,ite_false,Boot.permutationWords,
    dite_eq_right (not_lt.mpr lo)]
  exact (port.frame _ x (.inl portAt)).trans (t.frame rest x (.inl scalarAt))

theorem JointHeader.core_origin (b : JointHeader.Board) (score : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest : Boot.Tape z d)
    (port : PortROM.Table shapes) (t : ScalarROM.Table phases) (v : Fin jobs→Market z d k) {size : ℕ}
    (layout : Boot.Layout v size) (hd : 1≤d) (first : 2^z≤b.initial)
    (portsAfter : b.initial≤port.base) (pricesAfter : port.stop≤t.base)
    (within : b.initial≤ size) (before : ∀i,b.initial≤Boot.low (v i))
    (x : ℕ) (lowPerm : 2^z≤x) (lo : heapEnd z d copies≤x) (hi : x<b.initial) :
    Boot.booted v size (JointHeader.words b z d N k score π stock (port.words (t.words rest))) x=rest x := by
  let raw := port.words (t.words rest)
  have started := (Boot.start v layout hd π (JointHeader.words b z d N k score π stock raw)
    (JointHeader.authentic (N:=N) (k:=k) b score π stock raw first)).2
  have keep := started.kept x lo (fun j h=>Nat.not_lt_of_ge h.1 (hi.trans_le (before j)))
  rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (hi.trans_le within)] at keep
  exact keep.trans (JointHeader.core_words b score π stock rest port t portsAfter pricesAfter x lowPerm hi)

/-- Any further immutable finite table is mounted directly on the raw input
tail above the last scalar page. No second copy or recalibration is required. -/
theorem JointHeader.tail_origin (b : JointHeader.Board) (score : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest : Boot.Tape z d)
    (port : PortROM.Table shapes) (t : ScalarROM.Table phases) (v : Fin jobs→Market z d k) {size : ℕ}
    (layout : Boot.Layout v size) (hd : 1≤d) (first : 2^z≤b.initial)
    (afterPages : JointHeader.stop b z N k phases≤port.base) (aboveHeap : heapEnd z d copies≤port.base)
    (afterPorts : port.stop≤t.base) (x : ℕ) (low : t.stop≤x) (outside : ∀i,x<Boot.low (v i)) (fit : x<size) :
    Boot.booted v size (JointHeader.words b z d N k score π stock (port.words (t.words rest))) x=rest x := by
  let raw := port.words (t.words rest)
  have entered := (Boot.start v layout hd π (JointHeader.words b z d N k score π stock raw)
    (JointHeader.authentic (N:=N) (k:=k) b score π stock raw first)).2
  have cost : t.base≤x := (Nat.le_add_right t.base _).trans low
  have after := afterPorts.trans cost
  have base_le : port.base≤x := (Nat.le_add_right port.base _).trans after
  have keep := entered.kept x (aboveHeap.trans base_le) (fun i reach=>Nat.not_lt_of_ge reach.1 (outside i))
  rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left fit] at keep
  exact keep.trans ((JointHeader.tail_words b score π stock raw x first (afterPages.trans base_le)).trans
    ((port.frame _ x (.inr after)).trans (t.frame _ x (.inr low))))

/-- The domain of the underlying permutation, both integral feed ROMs, the score
pages, all occurrence headers, and all quantized scalar prices inhabit one
boot state for every authentic input permutation. -/
theorem JointHeader.scalar_origin (b : JointHeader.Board) (score : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest : Boot.Tape z d)
    (port : PortROM.Table shapes) (t : ScalarROM.Table phases) (v : Fin jobs→Market z d k) {size : ℕ}
    (layout : Boot.Layout v size) (hd : 1≤d) (first : 2^z≤b.initial)
    (afterPages : JointHeader.stop b z N k phases≤port.base) (aboveHeap : heapEnd z d copies≤port.base)
    (afterPorts : port.stop≤t.base) (within : t.stop≤ size)
    (before : ∀i,t.stop≤Boot.low (v i)) (room : t.kinds*t.stride<2^(wordBits z d copies)) :
    t.Resident (Boot.booted v size (JointHeader.words b z d N k score π stock (port.words (t.words rest)))) := by
  have resident := t.resident rest room
  have midpoint : port.base≤port.stop := Nat.le_add_right ..
  let raw := port.words (t.words rest)
  have started := (Boot.start v layout hd π (JointHeader.words b z d N k score π stock raw)
    (JointHeader.authentic (N:=N) (k:=k) b score π stock raw first)).2
  apply resident.frame
  intro x lo hi
  have earlier := midpoint.trans (afterPorts.trans lo)
  have keep := started.kept x (aboveHeap.trans earlier) (fun j h =>
    Nat.not_lt_of_ge h.1 (hi.trans_le (before j)))
  rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (hi.trans_le within)] at keep
  exact keep.trans ((JointHeader.tail_words b score π stock raw x first (afterPages.trans earlier)).trans
    (port.frame _ x (.inr (afterPorts.trans lo))))

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
