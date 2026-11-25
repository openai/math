import OAI.Computability.NearSquareRoot.InterchangeROMBinaryHaloMask
import OAI.Computability.NearSquareRoot.BoundedBranch
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelect
import Batteries.Tactic.OpenPrivate

/-! # Uniform linear-space register commands for five-axis padding and cropping -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BinaryHalo

open IntegerMultiplication Code CommonRegisters Space BoxMaskedRecords

/-- Trees represent arbitrary encoded records. The filling record is on the input
and may depend on the size of the payload lanes. -/
structure Packet where
  shape : Shape
  good : Good shape
  width : ℕ
  rows : List Tree
  fill : Tree
  length_le : rows.length ≤ shape.volume
  sized : ∀ x ∈ rows, size x ≤ width
  fill_sized : size fill ≤ width

def cost (q : Packet) := scanVolume q.shape.volume q.width

def input (grow : Bool) (q : Packet) : Tree :=
  if grow then send (q.shape.header, q.rows, q.fill) else send (q.shape.header, q.rows)

def output (grow : Bool) (q : Packet) : Tree :=
  if grow then send (expandWith (q.shape.mask,q.rows,q.fill)) else send (compress (.atom false) (q.shape.mask,q.rows))

private theorem le_cost (q : Packet) : q.shape.volume ≤ cost q := by
  exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))

/-- Both scans include generating the mask on the actual tape from the unary
five-field header. The constant is independent of the field and spectator ranges. -/
theorem task (grow : Bool) : Task cost (input grow) (output grow) := by
  have build := mask_task.on (fun q : Packet => ⟨q.shape,q.good⟩)
  have len (q : Packet) : q.rows.length ≤ q.shape.mask.length := by
    rw [mask_length _ q.good.hDE]; exact q.length_le
  have eq (q : Packet) : scanVolume q.shape.mask.length q.width = cost q := by
    rw [cost, mask_length _ q.good.hDE]
  cases grow with
  | true =>
    have scan := expandWith_task (fun q : Packet => q.shape.mask) Packet.rows Packet.fill Packet.width len
      Packet.sized Packet.fill_sized
    have both := (build.left (fun q : Packet => send (q.rows,q.fill))).compose scan
    apply both.bound 2
    intro q; dsimp only; rw [eq]; have := le_cost q; omega
  | false =>
    have scan := scan_task _ (compress_easy (.atom false : Tree)) (fun q : Packet => q.shape.mask)
      Packet.rows Packet.width len Packet.sized
    have both := (build.left (fun q : Packet => send q.rows)).compose scan
    apply both.bound 2
    intro q; dsimp only; rw [eq]; have := le_cost q; omega

/-- One fixed finite register bank and fixed command per direction. The data
fence adds the caller's parked deck and input to the linear execution allowance. -/
theorem commands : ∃ R : ℕ, ∃ cmd : Bool → Cmd, ∃ C : ℕ, ∀ grow,
    Within R (cmd grow) ∧ ∀ q env r base, DeckCap base r →
      let budget := C * (cost q+1)
      BoundedFits env (cmd grow) (pile 0 (input grow q) r) (pile 0 (output grow q) r)
        budget (base+(input grow q).count+budget) budget := by
  choose cmd C run using task
  obtain ⟨R,hR⟩ := Filter.Eventually.exists
    (Filter.eventually_all.mpr (fun grow => RegisterSelect.within_eventually (cmd grow)))
  refine ⟨R,cmd,max (C false) (C true),fun grow => ⟨hR grow,?_⟩⟩
  intro q env r base hr
  have hC : C grow ≤ max (C false) (C true) := by cases grow <;> simp
  have h := (run grow q env r).mono (Nat.mul_le_mul_right (cost q+1) hC)
  exact BoundedFits.of_fits h (fun i => Nat.add_le_add_right (hr.pile 0 (input grow q) i) _) le_rfl

open private header_bound from OAI.Computability.NearSquareRoot.InterchangeROMBinaryHaloMask
open private rows_size from OAI.Computability.NearSquareRoot.BoxMaskedRecords

/-- The header, records and supplied filling record all fit an absolute multiple
of the charged volume. This absorbs the input term in the physical fence. -/
theorem input_count_le (q : Packet) (grow : Bool) : (input grow q).count ≤ 16*(cost q + 1) := by
  have hs := header_bound q.good
  have hr := rows_size q.rows q.width q.sized
  have hf := q.fill_sized
  have hw : q.width+1 ≤ cost q := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have vol := le_cost q
  have hl : q.rows.length * (q.width+1) ≤ cost q :=
    Nat.mul_le_mul_right _ (q.length_le.trans (Nat.le_succ _))
  cases grow
  · change size (q.shape.header,q.rows) ≤ _
    change size q.shape.header + size q.rows + 1 ≤ _
    omega
  · change size (q.shape.header,q.rows,q.fill) ≤ _
    change size q.shape.header + (size q.rows + size q.fill + 1) + 1 ≤ _
    omega

/-- One absolute constant also bounds the total fresh data and return depth. -/
theorem linear_commands : ∃ R : ℕ, ∃ cmd : Bool → Cmd, ∃ C : ℕ, ∀ grow,
    Within R (cmd grow) ∧ ∀ q env r base, DeckCap base r →
      let budget := C * (cost q+1)
      BoundedFits env (cmd grow) (pile 0 (input grow q) r) (pile 0 (output grow q) r)
        budget (base+budget) budget := by
  obtain ⟨R,cmd,C,h⟩ := commands
  refine ⟨R,cmd,C+16,fun grow => ⟨(h grow).1,?_⟩⟩
  intro q env r base hr
  have run := (h grow).2 q env r base hr
  have sz := input_count_le q grow
  dsimp only at run ⊢
  rw [Nat.add_mul]
  exact run.mono (by omega) (by omega) (by omega)

end BinaryHalo

end NearSquareRoot
end Computability
end OAI
