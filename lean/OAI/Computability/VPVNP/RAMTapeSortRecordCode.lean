import OAI.Computability.VPVNP.RAMTapeSortField

/-! # Returning stack routines for sorting, selecting and validating two complete records -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Sorter

open BurstRAM RAMBoundary

/-- Select either a record-equality check or a sorting comparison that retains the designated
minimum or maximum. -/
inductive Mode where
  | verify | select (keepMin : Bool)
  deriving DecidableEq, Fintype

/-- Post-comparison transfer through the saved operands, temporary staging and next-block
output, including the discard and verification cases. -/
inductive Route where
  | verifyLeft | verifyRight | discardOther (takeLeft : Bool) | saved (takeLeft : Bool) | staged
  deriving DecidableEq, Fintype

/-- The stack to drain at this cleanup or transfer step. -/
def Route.src : Route → Port
  | .verifyLeft => .savedLeft
  | .verifyRight => .savedRight
  | .discardOther left => if left then .savedRight else .savedLeft
  | .saved left => if left then .savedLeft else .savedRight
  | .staged => .tmp

/-- Destination for a moved bit, using staging and then the next block for the selected
operand. Verification and discard routes drop the bit. -/
def Route.dst : Route → Option Port
  | .saved _ => some .tmp
  | .staged => some .next
  | _ => none

/-- Control of a five-field comparator, retaining the observed fields, cleanup route and
Boolean verdict through the final return. -/
inductive State where
  | field (i : Fin 5) (info : RecordInfo) (s : FieldState)
  | clean (route : Route) (ok : Bool)
  | put (route : Route) (ok bit : Bool)
  | emit (ok : Bool)
  | done
  deriving DecidableEq, Fintype

/-- Choose the next cleanup, staging or verdict state after exhausting the current route's
source stack. -/
def Route.after (ok : Bool) : Route → State
  | .verifyLeft => .clean .verifyRight ok
  | .verifyRight | .staged => .emit ok
  | .discardOther left => .clean (.saved left) ok
  | .saved _ => .clean .staged ok

/-- Check that each scanned five-word operand is a canonical encoded record. -/
def bothCanonical (info : RecordInfo) : Bool :=
  canonical (fun i ↦ (info i).left) && canonical (fun i ↦ (info i).right)

/-- After all fields are scanned, choose the operand-transfer route and verdict for equality
checking or minimum/maximum selection. -/
def cleanup (mode : Mode) (info : RecordInfo) : State :=
  match mode with
  | .verify => .clean .verifyLeft (bothCanonical info && equalDecision info)
  | .select keepMin => .clean (.discardOther (leDecision info == keepMin)) (bothCanonical info)

private def emptyInfo : RecordInfo := fun _ ↦ ⟨.zero,.zero,.eq⟩

/-- Save the observation for the completed field, then start the next field or proceed to
cleanup after field five. -/
def fieldExit (mode : Mode) (j : Fin 5) (f : RecordInfo) (s : WordState) : State :=
  let newInfo := Function.update f j (observe s)
  if h : j.val + 1 < 5 then .field ⟨j.val+1,h⟩ newInfo (.tick WordState.start)
  else cleanup mode newInfo

/-- Execute the field comparisons, drain or transfer the saved records, and emit the validity
bit for the selected mode. -/
def recordCode (mode : Mode) : StackCode Port State
  | .field j info (.done s) => .goto (fieldExit mode j info s)
  | .field j info s => (fieldCode s).rename id (.field j info)
  | .clean route ok => .pop route.src fun x ↦ x.elim (route.after ok) fun bit ↦
      if route.dst.isSome then .put route ok bit else .clean route ok
  | .put route ok bit => .push (route.dst.getD .tmp) bit (.clean route ok)
  | .emit ok => .push .valid ok .done
  | .done => .halt true

/-- Start at field zero with empty field observations and an initial word comparison state. -/
def entry : State := .field 0 emptyInfo (.tick WordState.start)

/-- Package the five-field record comparator as a returning finite routine for the chosen mode. -/
def routine (mode : Mode) : FiniteRoutine Port :=
  FiniteRoutine.ofStackCode (recordCode mode) id entry (fun s ↦ decide (s = .done))

/-- Sort two raw records and stage the requested minimum or maximum with a canonical-format
verdict. -/
def select (keepMin : Bool) : FiniteRoutine Port := routine (.select keepMin)
/-- Consume both records and emit the verdict that they are canonical and equal in all fields. -/
def verify : FiniteRoutine Port := routine .verify

/-- Validity flag for a sorting selection, requiring both operands to be canonically encoded. -/
def selectOK {w : ℕ} (a b : RawSlot w) : Bool := bothCanonical (expected a b)
/-- Validity flag for checking a transmitted copy, requiring canonical encodings and equal
words in all five fields. -/
def verifyOK {w : ℕ} (a b : RawSlot w) : Bool := selectOK a b && equalDecision (expected a b)

/-- The raw operand selected by the record order and the wire's minimum-or-maximum direction. -/
def chosen {w : ℕ} (keepMin : Bool) (a b : RawSlot w) : RawSlot w :=
  if leDecision (expected a b) == keepMin then a else b

/-- The returned validity bit for a comparison checks both five-word encodings. -/
theorem selectOK_iff {w : ℕ} (hw : 2 ≤ w) (a b : RawSlot w) :
    selectOK a b = true ↔ (∃ r, (RAMSerialization.recordFormat hw).words r = a) ∧
      ∃ r, (RAMSerialization.recordFormat hw).words r = b := by
  simp only [selectOK, bothCanonical, expected, Bool.and_eq_true, canonical_iff hw]

/-- The outgoing field must be exactly the same canonical five words as
the staged local record. -/
theorem verifyOK_iff {w : ℕ} (hw : 2 ≤ w) (a b : RawSlot w) :
    verifyOK a b = true ↔ (∃ r, (RAMSerialization.recordFormat hw).words r = a) ∧ a = b := by
  rw [verifyOK, Bool.and_eq_true, selectOK_iff hw, equalDecision_eq, decide_eq_true_iff]
  constructor
  · exact fun h ↦ ⟨h.1.1, h.2⟩
  · rintro ⟨h,rfl⟩; exact ⟨⟨h,h⟩,rfl⟩

/-- The selected bit string represents the requested comparator output
even when a malformed slot was presented and its validity bit is false. -/
theorem chosen_parsed {w : ℕ} (hw : 2 ≤ w) (keepMin : Bool) (a b : RawSlot w) :
    RAMSort.parsedSlot hw (chosen keepMin a b) =
      if keepMin then min (RAMSort.parsedSlot hw a) (RAMSort.parsedSlot hw b)
      else max (RAMSort.parsedSlot hw a) (RAMSort.parsedSlot hw b) := by
  unfold chosen
  rw [leDecision_eq hw]
  by_cases he : RAMSort.parsedSlot hw a ≤ RAMSort.parsedSlot hw b
  · cases keepMin <;> simp [he]
  · have hr := le_of_not_ge he
    cases keepMin <;> simp [he,min_eq_right hr,max_eq_left hr]

private theorem install_id (base small : Stacks Port) : installStacks id base small = small := by
  funext p
  exact installStacks_at Function.injective_id base small p

private def prefixInfo (n : ℕ) (f : RecordInfo) : RecordInfo :=
  fun i ↦ if i.val < n then f i else emptyInfo i

private def position (mode : Mode) (f : RecordInfo) (n : ℕ) : State :=
  if h : n < 5 then .field ⟨n,h⟩ (prefixInfo n f) (.tick WordState.start) else cleanup mode f

private theorem fieldExit_eq {w : ℕ} (mode : Mode) (j : Fin 5) (a b : RawSlot w) (s : WordState)
    (hobs : observe s = expected a b j) :
    fieldExit mode j (prefixInfo j.val (expected a b)) s = position mode (expected a b) (j.val+1) := by
  let f := expected a b
  have hf : Function.update (prefixInfo j.val f) j (observe s) = prefixInfo (j.val+1) f := by
    funext k
    by_cases he : k = j
    · subst k; simp [prefixInfo, hobs, f]
    · have hn : k.val ≠ j.val := fun hv ↦ he (Fin.ext hv)
      have hlt : k.val < j.val + 1 ↔ k.val < j.val := by omega
      simp [Function.update_of_ne he, prefixInfo, hlt]
  change fieldExit mode j (prefixInfo j.val f) s = position mode f (j.val+1)
  unfold fieldExit
  rw [hf]
  unfold position
  split
  · rfl
  · have hall : prefixInfo (j.val+1) f = f := by
      funext k
      have hk := k.isLt
      simp [prefixInfo, show k.val < j.val+1 by omega]
    simp [hall]

private theorem field_run (mode : Mode) {w : ℕ} (a b : RawSlot w) (j : Fin 5) (base : Bank) :
    StackRuns (recordCode mode) (8*w+3) (position mode (expected a b) j.val)
      {base with left := wordBits (a j) ++ base.left, right := wordBits (b j) ++ base.right, width := List.replicate w true, widthBack := []}.stacks
      (position mode (expected a b) (j.val+1))
      {base with width := List.replicate w true, widthBack := [], savedLeft := (wordBits (a j)).reverse ++ base.savedLeft, savedRight := (wordBits (b j)).reverse ++ base.savedRight}.stacks := by
  let f := expected a b
  have hr := field_runs WordState.start base (wordBits (a j)) (wordBits (b j)) (by simp)
  have hl := hr.lift (target := recordCode mode) id Function.injective_id (.field j (prefixInfo j.val f))
    (fun _ ↦ []) (fun q hq ↦ by cases q <;> first | rfl | contradiction)
  simp only [install_id, length_wordBits] at hl
  rw [position, dite_eq_left j.isLt]
  have hx := fieldExit_eq mode j a b _ (observe_fold a b j)
  exact hl.trans (.cons (.goto (show recordCode mode _ = .goto _ from congrArg StackOp.goto hx)) (.nil ..))

private theorem bytes_fields {w : ℕ} (a : RawSlot w) :
    Boundary.recordBytes a = wordBits (a 0) ++ (wordBits (a 1) ++ (wordBits (a 2) ++
      (wordBits (a 3) ++ wordBits (a 4)))) := by
  rw [Boundary.recordBytes, Boundary.recordWords, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ,
    List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rfl

/-- The five-word pass consumes exactly two records and preserves their
complete bit strings on the two save stacks. -/
theorem record_run (mode : Mode) {w : ℕ} (a b : RawSlot w) (base : Bank) :
    StackRuns (recordCode mode) (5*(8*w+3)) entry
      {base with left := Boundary.recordBytes a ++ base.left, right := Boundary.recordBytes b ++ base.right, width := List.replicate w true, widthBack := []}.stacks
      (cleanup mode (expected a b))
      {base with width := List.replicate w true, widthBack := [], savedLeft := (Boundary.recordBytes a).reverse ++ base.savedLeft, savedRight := (Boundary.recordBytes b).reverse ++ base.savedRight}.stacks := by
  let go (j : Fin 5) (lt rt ls rs : List Bool) :=
    field_run mode a b j {base with left := lt, right := rt, savedLeft := ls, savedRight := rs}
  let n := 8*w+3
  rw [show 5*(8*w+3) = n+(n+(n+(n+n))) by omega]
  simp only [bytes_fields, List.append_assoc, List.reverse_append]
  refine (go 0 _ _ base.savedLeft base.savedRight).trans ?_
  refine (go 1 _ _ _ _).trans ?_
  refine (go 2 _ _ _ _).trans ?_
  refine (go 3 _ _ _ _).trans ?_
  let saved (z : RawSlot w) (s : List Bool) := (wordBits (z 3)).reverse ++
    ((wordBits (z 2)).reverse ++ ((wordBits (z 1)).reverse ++ ((wordBits (z 0)).reverse ++ s)))
  exact go 4 base.left base.right (saved a base.savedLeft) (saved b base.savedRight)

end RAMTape.Sorter

end VPVNP
end Computability
end OAI
