import OAI.Hierarchy.ProtocolRAMCalendarGlobalHeader
import OAI.Hierarchy.ProtocolRAMCalendarHalfROM

namespace OAI
/-! # A single finite input tape for permutation, initial stock, reserve and scores -/

namespace Hierarchy.ProtocolRAM.Calendar.JointHeader
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native
open ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section
variable {z d N k q w jobs : ℕ}

structure Board where
  initial : ℕ
  steps : ℕ
  cap : ℕ
  width : ℕ
  precision : ℕ

def half (b : Board) (z N k : ℕ) :=
  FeedROM.halfBank b.initial (GlobalTests.rows z N k) b.steps b.cap b.width

def scores (b : Board) (z N k : ℕ) : GlobalTests.Layout :=
  ⟨(half b z N k).base+(half b z N k).size,GlobalTests.bits z N k,b.cap*b.width+1,b.precision⟩

def stop (b : Board) (z N k q : ℕ) :=
  (scores b z N k).base+q*GlobalTests.length (scores b z N k) z N k

theorem order (b : Board) (z N k : ℕ) :
    b.initial+GlobalTests.rows z N k≤(scores b z N k).base := by
  change b.initial+GlobalTests.rows z N k≤
    (FeedROM.sliceBank b.initial (GlobalTests.rows z N k) b.steps b.cap b.width).base+
      (FeedROM.sliceBank b.initial (GlobalTests.rows z N k) b.steps b.cap b.width).size+
      (half b z N k).size
  change b.initial+GlobalTests.rows z N k≤b.initial+GlobalTests.rows z N k+_+_
  omega

def inventory (b : Board) (z N k : ℕ) (stock : ℕ→ℕ) (m : Memory w) :=
  fillSegment b.initial (GlobalTests.rows z N k) (fun a=>(stock (a-b.initial):Word w)) m

def lowData (b : Board) (z N k : ℕ) (stock : ℕ→ℕ) (m : Memory w) :=
  FeedROM.mount b.initial (GlobalTests.rows z N k) b.steps b.cap b.width (inventory b z N k stock m)

def words (b : Board) (z d N k : ℕ) (phase : Fin q→PhasePrice) (π : Equiv.Perm (Fin (2^z)))
    (stock : ℕ→ℕ) (rest : Boot.Tape z d) : Boot.Tape z d :=
  GlobalTests.allPages (scores b z N k) z N k phase
    (lowData b z N k stock (Boot.permutationWords π rest))

theorem below_scores (b : Board) (phase : Fin q→PhasePrice) (π : Equiv.Perm (Fin (2^z)))
    (stock : ℕ→ℕ) (rest : Boot.Tape z d) (a : ℕ) (below : a<(scores b z N k).base) :
    words b z d N k phase π stock rest a=lowData b z N k stock (Boot.permutationWords π rest) a :=
  GlobalTests.all_frame _ _ _ _ phase _ a (.inl below)

theorem authentic (b : Board) (phase : Fin q→PhasePrice) (π : Equiv.Perm (Fin (2^z)))
    (stock : ℕ→ℕ) (rest : Boot.Tape z d) (space : 2^z≤b.initial) (i : Fin (2^z)) :
    words b z d N k phase π stock rest i.val=((π i).val : Word (wordBits z d copies)) := by
  have lo := i.isLt.trans_le space
  have hi : i.val<b.initial+GlobalTests.rows z N k := by omega
  rw [below_scores b phase π stock rest _ (hi.trans_le (order b z N k))]
  rw [lowData,FeedROM.before_stock _ _ _ _ _ _ _ hi]
  simp only [inventory,fillSegment,not_le.mpr lo,false_and,ite_false]
  exact Boot.permutationWords_get π rest i

theorem initial_stock (b : Board) (phase : Fin q→PhasePrice) (π : Equiv.Perm (Fin (2^z)))
    (stock : ℕ→ℕ) (rest : Boot.Tape z d) (i : Fin (GlobalTests.rows z N k)) :
    words b z d N k phase π stock rest (b.initial+i.val)=(stock i.val:Word (wordBits z d copies)) := by
  have inside : b.initial≤b.initial+i.val ∧ b.initial+i.val<b.initial+GlobalTests.rows z N k :=
    ⟨Nat.le_add_right ..,Nat.add_lt_add_left i.isLt _⟩
  rw [below_scores b phase π stock rest _ (inside.2.trans_le (order b z N k)),
    lowData,FeedROM.before_stock _ _ _ _ _ _ _ inside.2]
  simp only [inventory,fillSegment,ite_eq_left inside,Nat.add_sub_cancel_left]

/-- The original RAMMemory header and one physical CT launch establish every
phase's potential/payload lookup; the half table and the initial stock retain
their true addresses below those score pages. -/
theorem score_origin (b : Board) (phase : Fin q→PhasePrice) (π : Equiv.Perm (Fin (2^z)))
    (stock : ℕ→ℕ) (rest : Boot.Tape z d) (v : Fin jobs→Market z d k) {size : ℕ}
    (layout : Boot.Layout v size) (hd : 1≤d) (first : 2^z≤b.initial) (left : heapEnd z d copies≤b.initial)
    (fits : stop b z N k q≤ size) (before : ∀j,stop b z N k q≤Boot.low (v j)) (i : Fin q) :
    GlobalTests.Resident (GlobalTests.page (scores b z N k) z N k i.val) z N k (phase i)
      (Boot.booted v size (words b z d N k phase π stock rest)) := by
  have started := (Boot.start v layout hd π (words b z d N k phase π stock rest)
    (authentic (N:=N) (k:=k) b phase π stock rest first)).2
  apply GlobalTests.from_initial (scores b z N k) v π phase _ _ size started _ fits before i
  exact left.trans ((Nat.le_add_right ..).trans (order b z N k))

theorem low_origin (b : Board) (phase : Fin q→PhasePrice) (π : Equiv.Perm (Fin (2^z)))
    (stock : ℕ→ℕ) (rest : Boot.Tape z d) (v : Fin jobs→Market z d k) {size : ℕ}
    (layout : Boot.Layout v size) (hd : 1≤d) (first : 2^z≤b.initial)
    (fits : stop b z N k q≤ size) (before : ∀j,stop b z N k q≤Boot.low (v j))
    (a : ℕ) (lo : heapEnd z d copies≤a) (hi : a<(scores b z N k).base) :
    Boot.booted v size (words b z d N k phase π stock rest) a=
      lowData b z N k stock (Boot.permutationWords π rest) a := by
  have started := (Boot.start v layout hd π (words b z d N k phase π stock rest)
    (authentic (N:=N) (k:=k) b phase π stock rest first)).2
  have bounded : a<stop b z N k q := hi.trans_le (Nat.le_add_right ..)
  have keep := started.kept a lo (fun j hit=>Nat.not_lt_of_ge hit.1 (bounded.trans_le (before j)))
  rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (bounded.trans_le fits)] at keep
  exact keep.trans (below_scores b phase π stock rest a hi)

def coefficient (N k q steps : ℕ) :=
  GlobalTests.kinds N k+2*steps+6+3*q*GlobalTests.kinds N k

theorem stop_linear (b : Board) (z N k q : ℕ) (stride : b.cap*b.width+1≤2^z) :
    stop b z N k q≤b.initial+coefficient N k q b.steps*2^z := by
  have table := FeedROM.end_le b.initial (GlobalTests.rows z N k) b.steps b.cap b.width
  change (scores b z N k).base≤_ at table
  rw [GlobalTests.rowCount] at table
  have m := Nat.mul_le_mul_left b.steps stride
  have units : 1≤2^z := Nat.one_le_two_pow
  have pg := GlobalTests.pages_linear (scores b z N k) z N k q stride
  unfold stop coefficient
  nlinarith only [table,m,units,stride,pg]

theorem word_room (b : Board) (z d N k q : ℕ) (stride : b.cap*b.width+1≤2^z)
    (start : b.initial=heapEnd z d copies) (large : coefficient N k q b.steps+1≤2^z) :
    stop b z N k q<2^(wordBits z d copies) := by
  have h := stop_linear b z N k q stride
  rw [start] at h
  exact h.trans_lt (append_room large)

end
end Hierarchy.ProtocolRAM.Calendar.JointHeader

end OAI
