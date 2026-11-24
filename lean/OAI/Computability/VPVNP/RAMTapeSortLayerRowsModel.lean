import OAI.Computability.VPVNP.RAMTapeSortLayerRowsPorts
import OAI.Computability.VPVNP.RAMTapeSortRowModel

/-!
# Streams after a prefix of sorting rows

The local record array is immutable during one layer. The selected records
accumulate in reverse bit order and the row checks accumulate in reverse
row order. At a cross-site stride the unread messages are suffixes of the
supplied outgoing and incoming fields.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortLayerRows

open BurstRAM RAMSort RAMBoundary Boundary

variable {h d w : ℕ}

/-- Right comparator operand at a row, obtained from the partner in the local block for a local
stride and from the received row for a cross-site stride. -/
def other (s : Stage (h+d)) (current recv : Wires h (RawSlot w)) (i : Word h) : RawSlot w :=
  if s.stride < h then current (peerIndex s i) else recv i

/-- Output record at this row after comparing it with its partner and applying the stage's
minimum-or-maximum orientation. -/
def selected (s : Stage (h+d)) (v : Word d) (current recv : Wires h (RawSlot w))
    (i : Word h) : RawSlot w :=
  SortRow.chosen (keepMin s v i) (current i) (other s current recv i)

/-- Per-row validity bits checking both operands' formats and, on a cross-site stride, equality
of the sent record with the current row. -/
def checks (s : Stage (h+d)) (current send recv : Wires h (RawSlot w)) (i : Word h) : List Bool :=
  SortRow.selectOK (current i) (other s current recv i) ::
    (if s.stride < h then [] else [SortRow.verifyOK (current i) (send i)])

/-- The pending suffix for a given direction. On a local stride the following
fields have not been consumed. -/
def pending (s : Stage (h+d)) (field : Wires h (RawSlot w)) (tail : List Bool) (k : ℕ) : List Bool :=
  if s.stride < h then tail else blockBytes ((List.ofFn field).drop k) ++ tail

/-- Bits of the first k chosen records in reverse order prepended to the existing next-block
stack. -/
def pushed (f : Wires h (RawSlot w)) (next : List Bool) (k : ℕ) : List Bool :=
  (blockBytes ((List.ofFn f).take k)).reverse ++ next

/-- Flags for the first k completed rows, stacked in reverse row order ahead of earlier flags. -/
def latched (f : Word h → List Bool) (flags : List Bool) (k : ℕ) : List Bool :=
  ((List.ofFn f).take k).reverse.flatten ++ flags

theorem pending_cross {s : Stage (h+d)} (hj : ¬s.stride < h) (field : Wires h (RawSlot w))
    (tail : List Bool) (i : Word h) :
    pending s field tail i.val = recordBytes (field i) ++ pending s field tail (i.val+1) := by
  have hi : i.val < (List.ofFn field).length := by simp
  simp [pending, hj, List.drop_eq_getElem_cons hi, blockBytes, List.append_assoc]

theorem pushed_succ (f : Wires h (RawSlot w)) (next : List Bool) (i : Word h) :
    pushed f next (i.val+1) = (recordBytes (f i)).reverse ++ pushed f next i.val := by
  have hi : i.val < (List.ofFn f).length := by simp
  simp [pushed, List.take_succ_eq_append_getElem hi, blockBytes, List.append_assoc]

theorem latched_succ (f : Word h → List Bool) (flags : List Bool) (i : Word h) :
    latched f flags (i.val+1) = f i ++ latched f flags i.val := by
  have hi : i.val < (List.ofFn f).length := by simp
  simp [latched, List.take_succ_eq_append_getElem hi, List.append_assoc]

/-- Ambient state between callbacks, with all address and record scratch free. -/
def prefixBank (s : Stage (h+d)) (v : Word d) (current send recv : Wires h (RawSlot w))
    (next sendTail recvTail flags : List Bool) (k : ℕ) : Stacks Data :=
  bank v s.phase s.stride w (blockBytes (List.ofFn current)) (pushed (selected s v current recv) next k)
    (pending s send sendTail k) (pending s recv recvTail k) (latched (checks s current send recv) flags k)

/-- The incident stream at layer entry, beginning with the stage's record block exactly when
the stride crosses sites. -/
def fieldsBefore (s : Stage (h+d)) (field : Wires h (RawSlot w)) (tail : List Bool) :=
  if s.stride < h then tail else blockBytes (List.ofFn field) ++ tail

theorem prefixBank_zero (s : Stage (h+d)) (v : Word d) (current send recv : Wires h (RawSlot w))
    (next sendTail recvTail flags : List Bool) :
    prefixBank s v current send recv next sendTail recvTail flags 0 =
      bank v s.phase s.stride w (blockBytes (List.ofFn current)) next
        (fieldsBefore s send sendTail) (fieldsBefore s recv recvTail) flags := by
  simp [prefixBank, pushed, pending, latched, fieldsBefore, blockBytes]

theorem prefixBank_all (s : Stage (h+d)) (v : Word d) (current send recv : Wires h (RawSlot w))
    (next sendTail recvTail flags : List Bool) :
    prefixBank s v current send recv next sendTail recvTail flags (2^h) =
      bank v s.phase s.stride w (blockBytes (List.ofFn current))
        ((blockBytes (List.ofFn (selected s v current recv))).reverse ++ next) sendTail recvTail
        ((List.ofFn (checks s current send recv)).reverse.flatten ++ flags) := by
  have ht {α : Type} (f : Word h → α) : (List.ofFn f).take (2^h) = List.ofFn f :=
    List.take_of_length_le (by simp)
  have hd {α : Type} (f : Word h → α) : (List.ofFn f).drop (2^h) = [] :=
    List.drop_eq_nil_of_le (by simp)
  simp [prefixBank, pushed, pending, latched, ht, hd, blockBytes]

/-- The counter pass and the two physical record lookups per row have a quadratic
bound in the local row count, with linear dependence on the two widths. -/
def budget (h d w a j : ℕ) : ℕ :=
  6*h+7 + 2^h*(SortRowAddress.budget h d a j + 4096*(2^h+1)*(w+1) + 4*h+6)

theorem budget_le (s : Stage (h+d)) :
    budget h d w s.phase s.stride ≤ 8192*(2^h+1)^2*(h+d+w+1) := by
  let N := 2^h
  let m := h+d+w+1
  have ha := s.phase_le
  have hj := s.stride_lt
  have hm : 1 ≤ m := by dsimp [m]; omega
  let C := (N+1)*m
  have hn : 1 ≤ N+1 := Nat.succ_pos _
  have hnm : h+d+w+1 ≤ C := Nat.le_mul_of_pos_left m hn
  have hnn : N ≤ C := (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ hm)
  have hmul : (N+1)*(w+1) ≤ C := Nat.mul_le_mul_left _ (by dsimp [m]; omega)
  have hstep : SortRowAddress.budget h d s.phase s.stride + 4096*(N+1)*(w+1) + 4*h+6 ≤
      8192*((N+1)*m) := by
    unfold SortRowAddress.budget
    rw [Nat.mul_assoc 4096]
    change 28*h+16*d+6*s.phase+12*s.stride+7*N+29 + 4096*((N+1)*(w+1)) + 4*h+6 ≤ 8192*C
    omega
  have hsmall : 6*h+7 ≤ 8192*C := by omega
  calc
    budget h d w s.phase s.stride ≤ 8192*((N+1)*m) + N*(8192*((N+1)*m)) :=
      Nat.add_le_add hsmall (Nat.mul_le_mul_left N hstep)
    _ = 8192*(N+1)^2*m := by ring

end RAMTape.SortLayerRows

end VPVNP
end Computability
end OAI
