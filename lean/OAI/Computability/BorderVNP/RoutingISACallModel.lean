import OAI.Computability.BorderVNP.RoutingISAHeader
import OAI.Computability.BorderVNP.RoutingISANatural

/-!
# Cell-call directory and signed call records

Three words describe each cell. Only its owner reads the argument address and length
and supplies the contiguous argument to private routine zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellDispatch

open VPVNP.BurstRAM

/-- The team number and bounds of the directory scan. -/
structure Frame where
  /-- Number identifying the current team. -/
  team : ℕ
  /-- First word of the three-word directory. -/
  base : ℕ
  /-- Number of directory rows. -/
  count : ℕ

/-- The three fields come from the live shared memory named by public operand zero. -/
def Frame.ofMemory {w : ℕ} (pub : Arg → Word w) (m : Memory w) : Frame :=
  ⟨(m (pub 0).val).val, (m ((pub 0).val + 14)).val, (m ((pub 0).val + 15)).val⟩

/-- The register invariant at row boundaries. -/
def Frame.Ready {w : ℕ} (f : Frame) (i : ℕ) (s : Bank w) : Prop :=
  (s 0).val = 0 ∧ (s 1).val = 1 ∧ (s 2).val = 3 ∧ (s 3).val = f.team ∧
    (s 4).val = f.base ∧ (s 5).val = f.count ∧ (s 6).val = i

/-- Address of the owner column of the indexed row. -/
def Frame.address (f : Frame) (i : ℕ) := i * 3 + f.base

/-- Chronological record of a genuine read from a directory word. -/
def loadEvent {w : ℕ} (m : Memory w) (a : ℕ) : TeamRAM.Event w :=
  ⟨.ordinary (some (a, none)), [m a], [], .plus⟩

/-- The fixed sixteen-instruction setup visits the three frame words in order. -/
def setupTrace {w : ℕ} (pub : Arg → Word w) (m : Memory w) : List (TeamRAM.Event w) :=
  [tick w, tick w, tick w, tick w, tick w, tick w, loadEvent m (pub 0).val,
   tick w, tick w, tick w, loadEvent m ((pub 0).val + 14),
   tick w, tick w, tick w, loadEvent m ((pub 0).val + 15), tick w]

/-- The two argument columns of row `i` determine the precise burst that is charged. -/
def Frame.burst {w : ℕ} (f : Frame) (m : Memory w) (i : ℕ) : TeamTranscript.Action (Word w) :=
  .burst (m (f.address i + 1)).val (m (f.address i + 2)).val

/-- A private path carries its complete choice string and its integer sign. -/
abbrev Outcome := List Bool × TeamRAM.Sign

/-- The native event carries the actual arguments as well as the choice string and sign. -/
def Frame.callEvent {w : ℕ} (f : Frame) (m : Memory w) (i : ℕ) (o : Outcome) : TeamRAM.Event w :=
  ⟨f.burst m i, TeamRAM.previous m (f.burst m i), o.1, o.2⟩

/-- The row has either its owner's exact private path or the unique skipped outcome. -/
def Frame.Valid {w : ℕ} (f : Frame) (m : Memory w) (macros : TeamOpcode.Macros w 8)
    (i : ℕ) (result : Option Outcome) : Prop :=
  if (m (f.address i)).val = f.team then
    ∃ o, result = some o ∧ (m (f.address i + 1)).val + (m (f.address i + 2)).val ≤ 2^w ∧
      macros 0 (TeamRAM.previous m (f.burst m i)) o.1 = some o.2
  else result = none

/-- The exact directory history of one loop iteration, including its true guard. -/
def Frame.rowTrace {w : ℕ} (f : Frame) (m : Memory w) (i : ℕ)
    (result : Option Outcome) : List (TeamRAM.Event w) :=
  [tick w, tick w, tick w, loadEvent m (f.address i), tick w] ++
    (match result with
    | none => [tick w]
    | some o => [tick w, loadEvent m (f.address i + 1), tick w, loadEvent m (f.address i + 2),
        f.callEvent m i o]) ++ [tick w]

end RoutingISA.CellDispatch

end BorderVNP
end Computability
end OAI
