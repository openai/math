import OAI.Computability.VPVNP.RAMRecords
import Mathlib.Data.List.FinRange

/-!
# Choosing the internal primed bits of Section 11

The first pass visits the `2Rn` endpoint positions in flattened address order. At
the designated endpoint of each shared bit it branches once and writes that choice
to scratch. All initial memory outside those writes is preserved. No consistency
test on a primed sorting or successor message is part of this pass.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open BurstRAM

variable {N w : ℕ}

/-- Designated positions in the order the first pass visits them. -/
def owners (own : Fin N → Bool) : List (Fin N) := (List.finRange N).filter own

@[simp] theorem mem_owners (own : Fin N → Bool) (i : Fin N) : i ∈ owners own ↔ own i = true := by
  simp [owners]

theorem owners_nodup (own : Fin N → Bool) : (owners own).Nodup := (List.nodup_finRange N).filter _

theorem owners_length_le (own : Fin N → Bool) : (owners own).length ≤ N := by
  simpa [owners] using List.length_filter_le own (List.finRange N)

/-- A simultaneous choice of the shared bits indexed by their unique owners. -/
abbrev Assignment (own : Fin N → Bool) := {i : Fin N // own i = true} → Bool

/-- Only the restriction to the designated positions is used. -/
def bitAt {own : Fin N → Bool} (f : Assignment own) (i : Fin N) : Bool :=
  if h : own i then f ⟨i, h⟩ else false

/-- Branch choices in ascending endpoint order. -/
def branches {own : Fin N → Bool} (f : Assignment own) : List Bool := (owners own).map (bitAt f)

/-- An exact-length branch stream is equivalent to the independent bit choices. -/
def branchEquiv (own : Fin N → Bool) :
    {bs : List Bool // bs.length = (owners own).length} ≃ Assignment own where
  toFun bs i := bs.val[(owners own).idxOf i.val]'((List.idxOf_lt_length_of_mem ((mem_owners own _).mpr i.property)).trans_eq bs.property.symm)
  invFun f := ⟨branches f, by simp [branches]⟩
  left_inv bs := by
    apply Subtype.ext
    apply List.ext_getElem (by simpa [branches] using bs.property.symm)
    intro i hi hj
    have hx : i < (owners own).length := bs.property ▸ hj
    have hown := (mem_owners own _).mp (List.getElem_mem (l := owners own) hx)
    simp [branches, bitAt, hown, (owners_nodup own).idxOf_getElem _ hx]
  right_inv f := by
    funext i
    simp [branches, bitAt, i.property]

/-- Control for the single call associated to a position. -/
inductive CellControl
  | visit
  | emit (bit : Bool)
  | done

/-- The classifier, scratch address and successor state are computed from the public
position. This call takes one instruction at an unselected cell and three at an owner. -/
def cellCall (own : Bool) (addr next : Word w) (bitWord : Bool → Word w) : Program w CellControl where
  start _ := .visit
  step
    | .visit => if own then .branch CellControl.emit else .finish (some next)
    | .emit b => .write addr (bitWord b) .done
    | .done => .finish (some next)

@[simp] theorem execute_cell_owner (addr next : Word w) (bitWord : Bool → Word w)
    (m : Memory w) (b : Bool) :
    execute (cellCall true addr next bitWord) 3 .visit m [b] =
      some ⟨[.choice b, .write addr (bitWord b)], some next⟩ := rfl

@[simp] theorem execute_cell_skip (addr next : Word w) (bitWord : Bool → Word w) (m : Memory w) :
    execute (cellCall false addr next bitWord) 3 .visit m [] = some ⟨[], some next⟩ := rfl

/-- Scan the full endpoint list, retaining an exact branch stream. The address is
injective across all endpoints. The per-cell reports above implement its memory update. -/
def scan (own : Fin N → Bool) (addr : Fin N ↪ Word w) (bitWord : Bool → Word w) :
    List (Fin N) → List Bool → Memory w → Option (Memory w)
  | [], bits, m => if bits.isEmpty then some m else none
  | i :: cells, bits, m =>
    if own i then
      match bits with
      | [] => none
      | b :: bs => scan own addr bitWord cells bs (writeMemory m (addr i) (bitWord b))
    else scan own addr bitWord cells bits m

/-- Scan the entire input rectangle in order, consuming and storing one branch bit at each
designated owner and requiring the stream to be exhausted. -/
def firstPass (own : Fin N → Bool) (addr : Fin N ↪ Word w) (bitWord : Bool → Word w)
    (bits : List Bool) (m : Memory w) : Option (Memory w) :=
  scan own addr bitWord (List.finRange N) bits m

private theorem scan_accepts (own : Fin N → Bool) (addr : Fin N ↪ Word w) (bitWord : Bool → Word w)
    (cells : List (Fin N)) (bits : List Bool) (m : Memory w) :
    (scan own addr bitWord cells bits m).isSome ↔ bits.length = (cells.filter own).length := by
  induction cells generalizing bits m with
  | nil => cases bits <;> simp [scan]
  | cons i cells ih => cases h : own i <;> cases bits <;> simp [scan, h, ih]

/-- Both a short stream and a stream with extra branch choices reject. -/
theorem firstPass_accepts (own : Fin N → Bool) (addr : Fin N ↪ Word w) (bitWord : Bool → Word w)
    (bits : List Bool) (m : Memory w) :
    (firstPass own addr bitWord bits m).isSome ↔ bits.length = (owners own).length :=
  scan_accepts ..

/-- Accepted streams are in bijection with all assignments, for arbitrary initial memory. -/
def admissibleEquiv (own : Fin N → Bool) (addr : Fin N ↪ Word w) (bitWord : Bool → Word w)
    (m : Memory w) : {bs : List Bool // (firstPass own addr bitWord bs m).isSome} ≃ Assignment own :=
  (Equiv.subtypeEquivRight (fun bs ↦ firstPass_accepts own addr bitWord bs m)).trans (branchEquiv own)

/-- Each selected position receives its prescribed word, independent of old scratch contents. -/
def store (addr : Fin N ↪ Word w) (values : Fin N → Word w) :
    List (Fin N) → Memory w → Memory w
  | [], m => m
  | i :: cells, m => store addr values cells (writeMemory m (addr i) (values i))

private theorem scan_assignment (own : Fin N → Bool) (addr : Fin N ↪ Word w) (bitWord : Bool → Word w)
    (f : Fin N → Bool) (cells : List (Fin N)) (m : Memory w) :
    scan own addr bitWord cells ((cells.filter own).map f) m =
      some (store addr (bitWord ∘ f) (cells.filter own) m) := by
  induction cells generalizing m with
  | nil => rfl
  | cons i cells ih => cases h : own i <;> simp [scan, store, h, ih]

theorem firstPass_branches (own : Fin N → Bool) (addr : Fin N ↪ Word w) (bitWord : Bool → Word w)
    (f : Assignment own) (m : Memory w) :
    firstPass own addr bitWord (branches f) m = some (store addr (bitWord ∘ bitAt f) (owners own) m) :=
  scan_assignment ..

/-- Addresses outside the writes keep their original words, including all headers in
an address range disjoint from the scratch array. -/
theorem store_outside (addr : Fin N ↪ Word w) (values : Fin N → Word w) (cells : List (Fin N))
    (m : Memory w) (a : ℕ) (ha : ∀ i ∈ cells, a ≠ (addr i).val) :
    store addr values cells m a = m a := by
  induction cells generalizing m with
  | nil => rfl
  | cons i cells ih =>
    rw [store, ih _ (fun j hj ↦ ha j (List.mem_cons_of_mem _ hj))]
    simp [writeMemory, ha i (List.mem_cons_self ..)]

theorem store_at (addr : Fin N ↪ Word w) (values : Fin N → Word w) (cells : List (Fin N))
    (m : Memory w) {i : Fin N} (hi : i ∈ cells) : store addr values cells m (addr i).val = values i := by
  induction cells generalizing m with
  | nil => simp at hi
  | cons j cells ih =>
    by_cases hit : i ∈ cells
    · exact ih _ hit
    · have he : i = j := (List.mem_cons.mp hi).resolve_right hit
      subst j
      rw [store, store_outside]
      · simp [writeMemory]
      · intro j hj h
        exact hit (addr.injective (Fin.ext h) ▸ hj)

/-- A contiguous rectangular scratch region following the headers. -/
def scratchAddress (base : ℕ) (fit : base + N ≤ 2 ^ w) : Fin N ↪ Word w where
  toFun i := ⟨base + i.val, (Nat.add_lt_add_left i.isLt base).trans_le fit⟩
  inj' _ _ h := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

theorem store_header (base : ℕ) (fit : base + N ≤ 2 ^ w) (values : Fin N → Word w)
    (cells : List (Fin N)) (m : Memory w) {a : ℕ} (ha : a < base) :
    store (scratchAddress base fit) values cells m a = m a := by
  apply store_outside
  intro i _
  change a ≠ base + i.val
  omega

/-- A per-cell report, retaining the actual choice even when the overwritten word already
has the chosen value. `next` allows the caller to supply the encoded successor cursor. -/
def cellReport (own : Bool) (addr next : Word w) (bitWord : Bool → Word w) (b : Bool) : Report w :=
  ⟨if own then [.choice b, .write addr (bitWord b)] else [], some next⟩

theorem execute_cellReport (own : Bool) (addr next : Word w) (bitWord : Bool → Word w)
    (m : Memory w) (b : Bool) :
    execute (cellCall own addr next bitWord) 3 .visit m (if own then [b] else []) =
      some (cellReport own addr next bitWord b) := by cases own <;> rfl

/-- Genuine per-cell reports for the first pass in its cursor order. -/
def reports (own : Fin N → Bool) (addr : Fin N ↪ Word w) (next : Fin N → Word w)
    (bitWord : Bool → Word w) (f : Fin N → Bool) (cells : List (Fin N)) : List (Report w) :=
  cells.map (fun i ↦ cellReport (own i) (addr i) (next i) bitWord (f i))

/-- Replaying the actual event reports gives exactly the scratch updates. -/
theorem after_reports (own : Fin N → Bool) (addr : Fin N ↪ Word w) (next : Fin N → Word w)
    (bitWord : Bool → Word w) (f : Fin N → Bool) (cells : List (Fin N)) (m : Memory w) :
    after m ((reports own addr next bitWord f cells).map Report.events).flatten =
      store addr (bitWord ∘ f) (cells.filter own) m := by
  induction cells generalizing m with
  | nil => rfl
  | cons i cells ih =>
    cases h : own i <;>
      simpa [reports, cellReport, h, store, after, update] using ih (m := _)

/-- The paper charges one unit to start every call and one for every scratch write. -/
theorem reports_cost (own : Fin N → Bool) (addr : Fin N ↪ Word w) (next : Fin N → Word w)
    (bitWord : Bool → Word w) (f : Fin N → Bool) (cells : List (Fin N)) :
    RAMBuckets.cost Report.probes (reports own addr next bitWord f cells) =
      cells.length + (cells.filter own).length := by
  induction cells with
  | nil => rfl
  | cons i cells ih =>
    cases h : own i <;>
      simp [reports, cellReport, h, RAMBuckets.cost, Report.probes, countProbes] at ih ⊢ <;> omega

/-- At most one write probe and one call per cell. Unselected cells only use their call. -/
theorem firstPass_budget (own : Fin N → Bool) :
    (List.finRange N).length = N ∧ (owners own).length ≤ N ∧
      (List.finRange N).length + (owners own).length ≤ 2*N := by
  have := owners_length_le own
  simp only [List.length_finRange]
  exact ⟨trivial, this, by omega⟩

end PrimedInputRAM

end VPVNP
end Computability
end OAI
