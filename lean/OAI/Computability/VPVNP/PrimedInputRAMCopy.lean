import OAI.Computability.VPVNP.PrimedInputRAMChoices

/-!
# Assembling the inputs to the primed parses

The second pass of Section 11 copies the prescribed literal or a word from its designated
source to each rectangular output position. The first-pass scratch and header addresses
are separate from the output region. The machine copies the bits even when the assembled
primed message would fail a validator at a primed site.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open BurstRAM

variable {N w : ℕ}

/-- The value of a copied input cell is either an immediate word or a word read from external
memory. -/
inductive CopySource (w : ℕ)
  | literal (value : Word w)
  | fetch (address : Word w)

/-- Read the indicated word, or take the literal without an external probe. -/
def CopySource.get (m : Memory w) : CopySource w → Word w
  | .literal v => v
  | .fetch a => m a.val

/-- The source addresses carrying choices and headers are disjoint from the output array. -/
def CopySeparated (dest : Fin N ↪ Word w) (source : Fin N → CopySource w) : Prop :=
  ∀ i j a, source i = .fetch a → a ≠ dest j

private theorem get_writeMemory (dest : Fin N ↪ Word w) (source : Fin N → CopySource w)
    (hsep : CopySeparated dest source) (m : Memory w) (i j : Fin N) (v : Word w) :
    CopySource.get (writeMemory m (dest j) v) (source i) = CopySource.get m (source i) := by
  cases h : source i with
  | literal => rfl
  | fetch a =>
    have ha : a.val ≠ (dest j).val := fun h' ↦ hsep i j a h (Fin.ext h')
    simp [CopySource.get, writeMemory, ha]

/-- The copy loop reads each input from the current memory. -/
def scanCopies (dest : Fin N ↪ Word w) (source : Fin N → CopySource w) :
    List (Fin N) → Memory w → Memory w
  | [], m => m
  | i :: cells, m => scanCopies dest source cells (writeMemory m (dest i) (CopySource.get m (source i)))

/-- Assemble all endpoint positions in ascending rectangular address order. -/
def secondPass (dest : Fin N ↪ Word w) (source : Fin N → CopySource w) (m : Memory w) : Memory w :=
  scanCopies dest source (List.finRange N) m

/-- Because the output does not overwrite a source, every read sees the word left by
initialization or by the first pass. -/
theorem scanCopies_store (dest : Fin N ↪ Word w) (source : Fin N → CopySource w)
    (hsep : CopySeparated dest source) (cells : List (Fin N)) (m : Memory w) :
    scanCopies dest source cells m = store dest (fun i ↦ CopySource.get m (source i)) cells m := by
  induction cells generalizing m with
  | nil => rfl
  | cons i cells ih =>
    rw [scanCopies, store, ih]
    congr 1
    funext j
    exact get_writeMemory dest source hsep m j i _

theorem secondPass_at (dest : Fin N ↪ Word w) (source : Fin N → CopySource w) (m : Memory w)
    (hsep : CopySeparated dest source) (i : Fin N) :
    secondPass dest source m (dest i).val = CopySource.get m (source i) := by
  rw [secondPass, scanCopies_store dest source hsep]
  exact store_at _ _ _ _ (by simp)

/-- Every address outside the assembled array keeps its initial value, even in a layout
where some source addresses overlap with output addresses. -/
theorem secondPass_outside (dest : Fin N ↪ Word w) (source : Fin N → CopySource w) (m : Memory w)
    (a : ℕ) (ha : ∀ i, a ≠ (dest i).val) : secondPass dest source m a = m a := by
  have h (cells : List (Fin N)) (mem : Memory w) : scanCopies dest source cells mem a = mem a := by
    induction cells generalizing mem with
    | nil => rfl
    | cons i cells ih => rw [scanCopies, ih]; simp [writeMemory, ha]
  exact h _ _

/-- Private control for one item: fetch a source if necessary, write the word, then
return the next public cursor. -/
inductive CopyControl (w : ℕ)
  | visit
  | write (value : Word w)
  | done

/-- One deterministic burst that obtains a source word, writes it to the destination and
returns the next cursor. -/
def copyCall (src : CopySource w) (dest next : Word w) : Program w (CopyControl w) where
  start _ := .visit
  step
    | .visit => match src with
      | .literal v => .write dest v .done
      | .fetch a => .read a CopyControl.write
    | .write v => .write dest v .done
    | .done => .finish (some next)

/-- Exact copy trace and successor cursor, including a source read when the word comes from
memory. -/
def copyReport (src : CopySource w) (dest next : Word w) (m : Memory w) : Report w :=
  ⟨match src with
    | .literal v => [.write dest v]
    | .fetch a => [.read a (m a.val), .write dest (m a.val)], some next⟩

/-- Each deterministic call finishes in at most three elementary RAM instructions. -/
theorem execute_copyCall (src : CopySource w) (dest next : Word w) (m : Memory w) :
    execute (copyCall src dest next) 3 .visit m [] = some (copyReport src dest next m) := by
  cases src <;> rfl

theorem after_copyReport (src : CopySource w) (dest next : Word w) (m : Memory w) :
    after m (copyReport src dest next m).events = writeMemory m dest (CopySource.get m src) := by
  cases src <;> rfl

/-- Reports generated by the actual memory reads and writes of the loop. -/
def copyReports (dest : Fin N ↪ Word w) (source : Fin N → CopySource w) (next : Fin N → Word w) :
    List (Fin N) → Memory w → List (Report w)
  | [], _ => []
  | i :: cells, m => copyReport (source i) (dest i) (next i) m ::
    copyReports dest source next cells (writeMemory m (dest i) (CopySource.get m (source i)))

/-- Replaying the reports exactly implements the second-pass memory update. -/
theorem after_copyReports (dest : Fin N ↪ Word w) (source : Fin N → CopySource w)
    (next : Fin N → Word w) (cells : List (Fin N)) (m : Memory w) :
    after m ((copyReports dest source next cells m).map Report.events).flatten =
      scanCopies dest source cells m := by
  induction cells generalizing m with
  | nil => rfl
  | cons i cells ih =>
    simp only [copyReports, List.map_cons, List.flatten_cons, scanCopies]
    rw [show ∀ es tail, after m (es ++ tail) = after (after m es) tail by simp [after]]
    rw [after_copyReport, ih]

/-- All recorded reads use their actual values in external memory. -/
theorem correct_copyReports (dest : Fin N ↪ Word w) (source : Fin N → CopySource w)
    (next : Fin N → Word w) (cells : List (Fin N)) (m : Memory w) :
    Correct m ((copyReports dest source next cells m).map Report.events).flatten := by
  induction cells generalizing m with
  | nil => trivial
  | cons i cells ih =>
    cases h : source i <;>
      simp [copyReports, h, copyReport, CopySource.get, Correct, update, ih]

/-- One call and at most two probes per position, regardless of the copied values. -/
theorem copyReports_cost_le (dest : Fin N ↪ Word w) (source : Fin N → CopySource w)
    (next : Fin N → Word w) (cells : List (Fin N)) (m : Memory w) :
    RAMBuckets.cost Report.probes (copyReports dest source next cells m) ≤ 3 * cells.length := by
  induction cells generalizing m with
  | nil => rfl
  | cons i cells ih =>
    have h := ih (writeMemory m (dest i) (CopySource.get m (source i)))
    have hp : (copyReport (source i) (dest i) (next i) m).probes ≤ 2 := by
      cases source i <;> simp [copyReport, Report.probes, countProbes]
    simp only [copyReports, RAMBuckets.cost, List.length_cons]
    omega

end PrimedInputRAM

end VPVNP
end Computability
end OAI
