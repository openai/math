import OAI.Computability.VPVNP.RAMTapeSortRowAddressScan
import OAI.Computability.VPVNP.RAMTapeSortRowAddressUnary
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord
import OAI.Computability.VPVNP.RAMSortFieldIndex

/-! # The bitonic sorter’s finite row-address machine

The global wire has the row bits followed by the site bits in little-endian
order. The phase and stride are unary counters on the tape. Two indexed reads
supply the direction. A third pass toggles the stride bit within the row, if
present, and converts the resulting offset to a unary record count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortRowAddress

open BurstRAM TapeWord

/-- The phase and stride bit positions queried in the global wire address to determine the
comparator orientation. -/
inductive Axis where | phase | stride
  deriving DecidableEq

instance : Fintype Axis := derive_fintype% _

/-- Ports for the row and site indices, stage parameters, orientation and partner decisions,
and scratch for bit scans and unary conversion. -/
inductive Port where
  | row | site | index (axis : Axis) | orientation | offset | localFlag
  | observed (axis : Axis) | bits | count | rev | tmp
  deriving DecidableEq, Fintype

/-- The unary index of the phase bit to read from the concatenated row and site address. -/
abbrev Port.phase : Port := .index .phase
/-- The unary index of the stride bit used for both orientation and partner selection. -/
abbrev Port.stride : Port := .index .stride

private abbrev marks (n : ℕ) := List.replicate n true

private structure Work where
  observed : Axis → List Bool := fun _ => []
  orientation : List Bool := []
  localFlag : List Bool := []
  offset : ℕ := 0
  bits : List Bool := []
  count : List Bool := []
  rev : List Bool := []

private def number (a j : ℕ) : Axis → ℕ
  | .phase => a
  | .stride => j

private def frame (row site : List Bool) (a j : ℕ) (s : Work) : Stacks Port
  | .row => row
  | .site => site
  | .index ax => marks (number a j ax)
  | .observed ax => s.observed ax
  | .orientation => s.orientation
  | .offset => marks s.offset
  | .localFlag => s.localFlag
  | .bits => s.bits
  | .count => s.count
  | .rev => s.rev
  | .tmp => []

private def copy (src dst : Port) := SuccessorFields.prependCopy src dst .tmp

private theorem copy_run (src dst : Port) (hd : src ≠ dst) (hs : src ≠ .tmp) (ht : dst ≠ .tmp)
    (s : Stacks Port) (h : s .tmp = []) :
    (copy src dst).Runs (5*(s src).length+2) s (Function.update s dst (s src ++ s dst)) :=
  SuccessorFields.prependCopy_runs _ _ _ hd hs ht s h

private def scanPorts (flag : Port) : IndexScan.Port → Port
  | .bits => .bits
  | .count => .count
  | .rev => .rev
  | .flag => flag

private def readWire (axis : Axis) : FiniteRoutine Port :=
  (((copy .site .bits).followedBy (copy .row .bits)).followedBy
    (copy (.index axis) .count)).followedBy ((IndexScan.routine false).onPorts (scanPorts (.observed axis)))

private theorem readWire_run (axis : Axis) (row site : List Bool) (a j : ℕ) (obs : Axis → List Bool)
    (ho : obs axis = []) :
    let k := number a j axis
    let g := value (row ++ site)
    ∃ t ≤ 8*(row.length+site.length)+6*k+9, (readWire axis).Runs t
      (frame row site a j {observed := obs})
      (frame row site a j {observed := Function.update obs axis [g.testBit k]}) := by
  let k := number a j axis
  let F := frame row site a j
  let s₀ : Work := {observed := obs}
  let s₁ := {s₀ with bits := site}
  let s₂ := {s₁ with bits := row ++ site}
  let s₃ := {s₂ with count := marks k}
  let s₄ : Work := {observed := Function.update obs axis [(value (row ++ site)).testBit k]}
  have c₁ := copy_run .site .bits (by decide) (by decide) (by decide) (F s₀) rfl
  have c₂ := copy_run .row .bits (by decide) (by decide) (by decide) (F s₁) rfl
  have c₃ := copy_run (.index axis) .count (by intro h; cases h) (by intro h; cases h) (by decide) (F s₂) rfl
  have e₁ : Function.update (F s₀) Port.bits (site ++ []) = F s₁ := by
    funext p; cases p <;> simp [F, s₀, s₁, frame, Function.update]
  have e₂ : Function.update (F s₁) Port.bits (row ++ site) = F s₂ := by
    funext p; cases p <;> rfl
  have e₃ : Function.update (F s₂) Port.count (marks k ++ []) = F s₃ := by
    funext p; cases p <;> simp [F, s₂, s₃, frame, Function.update]
  change (copy ..).Runs (5*site.length+2) (F s₀) (Function.update (F s₀) .bits (site ++ [])) at c₁
  change (copy ..).Runs (5*row.length+2) (F s₁) (Function.update (F s₁) .bits (row ++ site)) at c₂
  change (copy ..).Runs (5*(marks k).length+2) (F s₂) (Function.update (F s₂) .count (marks k ++ [])) at c₃
  rw [e₁] at c₁
  rw [e₂] at c₂
  rw [e₃, List.length_replicate] at c₃
  obtain ⟨n, hn, hscan⟩ := IndexScan.runs false k (row ++ site)
  have scan : ((IndexScan.routine false).onPorts (scanPorts (.observed axis))).Runs n (F s₃) (F s₄) := by
    apply FiniteRoutine.runs_onPorts_framed _ (by intro x y h; cases x <;> cases y <;> simp_all [scanPorts]) hscan
    · intro p; cases p <;> first | rfl | exact ho
    · intro p; cases p <;> first | rfl | exact Function.update_self ..
    · intro p h
      cases p with
      | observed z =>
        exact Function.update_of_ne (by intro e; subst z; exact h .flag rfl) ..
      | bits => exact (h .bits rfl).elim
      | count => exact (h .count rfl).elim
      | row | site | index | orientation | offset | localFlag | rev | tmp => rfl
  refine ⟨_, ?_, ((c₁.followedBy c₂).followedBy c₃).followedBy scan⟩
  simp only [List.length_append] at hn
  dsimp only [k] at *
  omega

private inductive EqState where | phase | stride (x : Bool) | emit (b : Bool) | done
  deriving DecidableEq, Fintype

private def eqCode : StackCode Port EqState
  | .phase => .pop (.observed .phase) fun x => .stride (x.getD false)
  | .stride x => .pop (.observed .stride) fun y => .emit (x == y.getD false)
  | .emit b => .push .orientation b .done
  | .done => .halt true

private def equalBits : FiniteRoutine Port := FiniteRoutine.ofStackCode eqCode id .phase (· == .done)

private theorem equalBits_run (row site : List Bool) (a j : ℕ) (x y : Bool) :
    equalBits.Runs 3 (frame row site a j {observed := fun | .phase => [x] | .stride => [y]})
      (frame row site a j {orientation := [x == y]}) := by
  let F := frame row site a j
  let s₀ : Work := {observed := fun | .phase => [x] | .stride => [y]}
  let s₁ : Work := {observed := fun | .phase => [] | .stride => [y]}
  let s₂ : Work := {}
  let s₃ : Work := {orientation := [x == y]}
  have e₁ : Function.update (F s₀) (.observed .phase) [] = F s₁ := by
    funext p; cases p <;> first | rfl | rename_i k; cases k <;> rfl
  have e₂ : Function.update (F s₁) (.observed .stride) [] = F s₂ := by
    funext p; cases p <;> first | rfl | rename_i k; cases k <;> rfl
  have e₃ : Function.update (F s₂) Port.orientation [x == y] = F s₃ := by
    funext p; cases p <;> rfl
  have run : StackRuns eqCode 3 .phase (F s₀) .done (F s₃) := by
    refine .cons (.pop rfl) ?_
    change StackRuns eqCode 2 (.stride x) (Function.update (F s₀) (.observed .phase) []) _ _
    rw [e₁]
    refine .cons (.pop rfl) ?_
    change StackRuns eqCode 1 (.emit (x == y)) (Function.update (F s₁) (.observed .stride) []) _ _
    rw [e₂]
    refine .cons (.push rfl) ?_
    change StackRuns eqCode 0 .done (Function.update (F s₂) .orientation [x == y]) _ _
    rw [e₃]
    exact .nil ..
  exact FiniteRoutine.runs_ofStackCode_framed Function.injective_id rfl rfl
    (fun q h => by simp only [beq_iff_eq] at h; subst q; rfl) run (fun _ => rfl) (fun _ => rfl)
    (fun p h => (h p rfl).elim)

private def unaryPorts : Unary.Port → Port
  | .bits => .rev
  | .out => .offset
  | .tmp => .tmp

private def offsetRoutine : FiniteRoutine Port :=
  (((copy .row .bits).followedBy (copy .stride .count)).followedBy
    ((IndexScan.routine true).onPorts (scanPorts .localFlag))).followedBy (Unary.routine.onPorts unaryPorts)

private theorem offset_run (row site : List Bool) (a j : ℕ) (direction : Bool) :
    let peer := IndexScan.flip j row
    ∃ t ≤ 12*row.length+6*j+7*value peer+8, offsetRoutine.Runs t
      (frame row site a j {orientation := [direction]})
      (frame row site a j {orientation := [direction], offset := value peer, localFlag := [decide (j<row.length)]}) := by
  let F := frame row site a j
  let s₀ : Work := {orientation := [direction]}
  let s₁ := {s₀ with bits := row}
  let s₂ := {s₁ with count := marks j}
  let peer := IndexScan.flip j row
  let s₃ := {s₀ with localFlag := [decide (j < row.length)], rev := peer.reverse}
  let s₄ := {s₃ with offset := value peer, rev := []}
  have c₁ := copy_run .row .bits (by decide) (by decide) (by decide) (F s₀) rfl
  have c₂ := copy_run .stride .count (by decide) (by decide) (by decide) (F s₁) rfl
  have e₁ : Function.update (F s₀) Port.bits (row ++ []) = F s₁ := by
    funext p; cases p <;> simp [F, s₀, s₁, frame, Function.update]
  have e₂ : Function.update (F s₁) Port.count (marks j ++ []) = F s₂ := by
    funext p; cases p <;> simp [F, s₁, s₂, frame, Function.update]
  change (copy ..).Runs (5*row.length+2) (F s₀) (Function.update (F s₀) .bits (row ++ [])) at c₁
  change (copy ..).Runs (5*(marks j).length+2) (F s₁) (Function.update (F s₁) .count (marks j ++ [])) at c₂
  rw [e₁] at c₁
  rw [e₂, List.length_replicate] at c₂
  obtain ⟨n, hn, hscan⟩ := IndexScan.runs true j row
  have scan : ((IndexScan.routine true).onPorts (scanPorts .localFlag)).Runs n (F s₂) (F s₃) := by
    apply FiniteRoutine.runs_onPorts_framed _ (by intro x y h; cases x <;> cases y <;> simp_all [scanPorts]) hscan
    · intro p; cases p <;> rfl
    · intro p; cases p <;> rfl
    · intro p h; cases p <;> first | rfl | exact (h .bits rfl).elim | exact (h .count rfl).elim
                                         | exact (h .rev rfl).elim | exact (h .flag rfl).elim
  obtain ⟨u, hu, hunary⟩ := Unary.runs peer
  have un : (Unary.routine.onPorts unaryPorts).Runs u (F s₃) (F s₄) := by
    apply FiniteRoutine.runs_onPorts_framed _ (by intro x y h; cases x <;> cases y <;> simp_all [unaryPorts]) hunary
    · intro p; cases p <;> rfl
    · intro p; cases p <;> rfl
    · intro p h; cases p <;> first | rfl | exact (h .bits rfl).elim | exact (h .out rfl).elim
  refine ⟨_, ?_, ((c₁.followedBy c₂).followedBy scan).followedBy un⟩
  simp only [peer, IndexScan.length_flip] at hu
  omega

/-- All input-dependent parameters are bit stacks. The instruction table is fixed. -/
def routine : FiniteRoutine Port :=
  (((readWire .phase).followedBy (readWire .stride)).followedBy equalBits).followedBy offsetRoutine

/-- Initialize the row-address machine with the given row and site bits, unary phase and
stride, and empty work stacks. -/
def initial (row site : List Bool) (a j : ℕ) : Stacks Port := frame row site a j {}

/-- The three outputs are a one-bit orientation, a one-bit local stride indicator,
and the unary record offset. The original row, site and both counters are retained. -/
def final (row site : List Bool) (a j : ℕ) (keepMin localStride : Bool) (offset : ℕ) : Stacks Port :=
  frame row site a j {orientation := [keepMin], localFlag := [localStride], offset := offset}

theorem initial_port (row site : List Bool) (a j : ℕ) (p : Port) :
    initial row site a j p = match p with
      | .row => row
      | .site => site
      | .index .phase => List.replicate a true
      | .index .stride => List.replicate j true
      | _ => [] := by
  cases p <;> first | rfl | rename_i ax; cases ax <;> rfl

theorem final_port (row site : List Bool) (a j : ℕ) (keepMin localStride : Bool)
    (offset : ℕ) (p : Port) :
    final row site a j keepMin localStride offset p = match p with
      | .orientation => [keepMin]
      | .localFlag => [localStride]
      | .offset => List.replicate offset true
      | _ => initial row site a j p := by
  cases p <;> rfl

/-- Tick allowance for the indexed phase and stride reads and conversion of the possibly
toggled h-bit row index to a unary offset. -/
def budget (h d a j : ℕ) : ℕ := 28*h+16*d+6*a+12*j+7*2^h+29

/-- The maximum phase, equal to the total width, reads a zero direction bit.
This also covers empty row and site words. -/
theorem runs_bits (row site : List Bool) (a j : ℕ) :
    let g := value site * 2^row.length + value row
    let off := if j < row.length then RAMSort.partner j (value row) else value row
    ∃ t ≤ budget row.length site.length a j, routine.Runs t (initial row site a j)
      (final row site a j (g.testBit j == g.testBit a) (decide (j < row.length)) off) := by
  let g := value (row ++ site)
  let obs : Axis → List Bool := Function.update (fun _ => []) .phase [g.testBit a]
  obtain ⟨t, ht, h₁⟩ := readWire_run .phase row site a j (fun _ => []) rfl
  obtain ⟨u, hu, h₂⟩ := readWire_run .stride row site a j obs rfl
  have he : Function.update obs Axis.stride [g.testBit j] =
      fun | .phase => [g.testBit a] | .stride => [g.testBit j] := by funext ax; cases ax <;> rfl
  change (readWire .stride).Runs u _ (frame row site a j {observed := Function.update obs .stride [g.testBit j]}) at h₂
  rw [he] at h₂
  have eq := equalBits_run row site a j (g.testBit a) (g.testBit j)
  obtain ⟨v, hv, h₃⟩ := offset_run row site a j (g.testBit a == g.testBit j)
  have chain := ((h₁.followedBy h₂).followedBy eq).followedBy h₃
  have hval := value_lt (IndexScan.flip j row)
  rw [IndexScan.length_flip] at hval
  have hg : g = value site * 2^row.length + value row := by simp [g, value_append, Nat.mul_comm, Nat.add_comm]
  change routine.Runs _ (initial row site a j)
    (final row site a j (g.testBit a == g.testBit j) (decide (j < row.length)) (value (IndexScan.flip j row))) at chain
  rw [hg, IndexScan.flip_value, BEq.comm] at chain
  refine ⟨_, ?_, chain⟩
  change t ≤ 8*(row.length+site.length)+6*a+9 at ht
  change u ≤ 8*(row.length+site.length)+6*j+9 at hu
  unfold budget
  omega

theorem runs {h d : ℕ} (i : Word h) (v : Word d) (a j : ℕ) :
    let g := v.val * 2^h + i.val
    let off := if j < h then RAMSort.partner j i.val else i.val
    ∃ t ≤ budget h d a j, routine.Runs t (initial (wordBits i) (wordBits v) a j)
      (final (wordBits i) (wordBits v) a j (g.testBit j == g.testBit a) (decide (j<h)) off) := by
  simpa only [length_wordBits, value_wordBits] using runs_bits (wordBits i) (wordBits v) a j

/-- Running the row-address program in a caller's register bank changes only
the three designated output stacks. -/
theorem runs_framed {K : Type} [DecidableEq K] (ports : Port → K) (hp : Function.Injective ports)
    {h d : ℕ} (i : Word h) (v : Word d) (a j : ℕ) (s : Stacks K)
    (hi : ∀ p, s (ports p) = initial (wordBits i) (wordBits v) a j p) :
    let g := v.val * 2^h + i.val
    let off := if j < h then RAMSort.partner j i.val else i.val
    ∃ t ≤ budget h d a j, (routine.onPorts ports).Runs t s
      (Function.update (Function.update (Function.update s (ports .orientation)
        [g.testBit j == g.testBit a]) (ports .localFlag) [decide (j < h)]) (ports .offset) (marks off)) := by
  obtain ⟨t, ht, run⟩ := runs i v a j
  refine ⟨t, ht, ?_⟩
  apply FiniteRoutine.runs_onPorts_framed _ hp run hi
  · intro p
    rw [final_port]
    cases p <;> simp [Function.update, hp.eq_iff, hi]
  · intro k hk
    simp [Function.update, Ne.symm (hk .orientation), Ne.symm (hk .localFlag), Ne.symm (hk .offset)]

/-- The lower-numbered wire in an XOR pair is the one with a zero stride bit. -/
theorem lt_partner_iff (g j : ℕ) : g < RAMSort.partner j g ↔ g.testBit j = false := by
  have same (k : ℕ) (hk : j < k) : (RAMSort.partner j g).testBit k = g.testBit k := by
    simp [RAMSort.partner, Nat.testBit_two_pow_of_ne hk.ne]
  have toggled : (RAMSort.partner j g).testBit j = !(g.testBit j) := by
    simp [RAMSort.partner, Nat.testBit_two_pow_self]
  cases h : g.testBit j with
  | false =>
    have lt := Nat.lt_of_testBit j h (by simpa [h] using toggled)
      (fun k hk => (same k hk).symm)
    simp [lt]
  | true =>
    have lt := Nat.lt_of_testBit j (by simpa [h] using toggled) h same
    simp [Nat.not_lt_of_ge lt.le]

private theorem direction_eq (g a : ℕ) : RAMSort.phaseDirection a g = !(g.testBit a) := by
  simp only [RAMSort.phaseDirection, Nat.testBit_eq_decide_div_mod_eq, ← decide_not, decide_eq_decide]
  have := Nat.mod_lt (g / 2^a) (by decide : 0 < 2)
  omega

/-- The machine's orientation chooses precisely the output assigned by the
bitonic comparator, with the row's own record as the first input. -/
theorem select_eq_comparator {α : Type*} [LinearOrder α] (g a j : ℕ) (own other : α) :
    (if g.testBit j == g.testBit a then min own other else max own other) =
      if g < RAMSort.partner j g then RAMSort.lower (RAMSort.phaseDirection a g) own other
      else RAMSort.upper (RAMSort.phaseDirection a g) other own := by
  simp only [lt_partner_iff, direction_eq]
  cases g.testBit j <;> cases g.testBit a <;> simp [RAMSort.lower, RAMSort.upper, min_comm, max_comm]

/-- A nonlocal stride changes precisely bit `j-h` of the site. The allocated
physical field specifies the same peer as the global wire calculation. -/
theorem cross_siteBit {h d : ℕ} (s : RAMSort.Stage (h+d)) (hc : h ≤ s.stride) :
    ((RAMSort.crossStageEquiv h d).symm ⟨s,hc⟩).siteBit = s.stride - h := by
  change s.phase - h - 1 - (s.phase - s.stride - 1) = s.stride - h
  have := s.stride_lt
  omega

end RAMTape.SortRowAddress

end VPVNP
end Computability
end OAI
