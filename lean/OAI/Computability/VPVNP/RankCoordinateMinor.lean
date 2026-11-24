import OAI.Computability.VPVNP.RankCoordinateDimension
import OAI.Computability.VPVNP.RankCoordinateColumn

/-! # Physical scalar reads from the two Cramer minors

A query recomputes the two selected indices in the original matrix and its
transpose. For the replaced-row minor, a register equality selects either an
ordinary matrix entry or the target entry at the selected column. All large
matrices are accessed through scalar calls.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.Minor

open RAMTape UniversalCountStack Dispatch BurstRAM TapeWord

variable {K : Type} [DecidableEq K] {r width : ℕ}

/-- Compare two caller registers and use the returned bit to enter a subroutine. -/
def equalBranch (ports : ISA.Port r 0 → K) (x y : Fin r) (ordinary replacement : FiniteRoutine K) :
    FiniteRoutine K :=
  ((ISA.compareRegs .eq x y).onPorts ports).followedBy (.ofRoutine
    (Routine.popCase (ports (.work 0)) (Routine.halt false) ordinary.body replacement.body))

private theorem choose_runs {flag : K} (low high : FiniteRoutine K) {cap t : ℕ} {s u : Stacks K}
    {b : Bool} (hf : s flag = []) (hcap : ∀ k, (Function.update s flag [b] k).length ≤ cap)
    (arm : (if b then high else low).BoundedRun cap t s u) :
    (FiniteRoutine.ofRoutine (Routine.popCase flag (Routine.halt false) low.body high.body)).BoundedRun cap (t+1)
      (Function.update s flag [b]) u := by
  let code := Routine.popCase flag (Routine.halt false) low.body high.body
  change SpaceRun code.standalone cap (t+1) (some code.entry) (Function.update s flag [b]) none u
  have back : Function.update s flag [] = s := by rw [← hf, Function.update_eq_self]
  cases b with
  | false =>
    change low.BoundedRun cap t s u at arm
    have tail := arm.linkRoutine code (Sum.inr ∘ Sum.inr ∘ Sum.inl) none (fun _ ↦ rfl)
    refine .cons hcap ?_ tail
    simpa only [Function.update_self, List.head?_cons, List.tail_cons, Function.update_idem, back, Function.comp_apply] using
      (StackStep.pop (s := Function.update s flag [false]) (show code.standalone (some code.entry) = _ from rfl))
  | true =>
    change high.BoundedRun cap t s u at arm
    have tail := arm.linkRoutine code (Sum.inr ∘ Sum.inr ∘ Sum.inr) none (fun _ ↦ rfl)
    refine .cons hcap ?_ tail
    simpa only [Function.update_self, List.head?_cons, List.tail_cons, Function.update_idem, back, Function.comp_apply] using
      (StackStep.pop (s := Function.update s flag [true]) (show code.standalone (some code.entry) = _ from rfl))

/-- Branching preserves the call's space cap even if one of its subcalls takes
exponentially many steps. The comparison itself scans only two binary words. -/
theorem equalBranch_runs {ports : ISA.Port r 0 → K} {bank : Regs r width → Stacks K} {persistent : Word width}
    (hb : RegisterBank ports bank persistent) (rs : Regs r width) (x y : Fin r) (low high : FiniteRoutine K)
    {cap t : ℕ} {out : Stacks K} (hc : width+(20*width+10) ≤ cap)
    (arm : (if rs x = rs y then high else low).BoundedRun cap t (bank rs) out) :
    (equalBranch ports x y low high).BoundedRun cap ((20*width+10)+(t+1)) (bank rs) out := by
  let localBank := ISA.bank Fin.elim0 persistent rs []
  let bit := decide (rs x = rs y)
  have step := ISA.compareRegs_run .eq x y Fin.elim0 persistent rs []
  have small := spaceRun_of_steps (cap := cap) step fun k ↦
    (Nat.add_le_add_right (RegisterTable.bank_length_le Fin.elim0 persistent rs k) _).trans hc
  have cmp := FiniteRoutine.BoundedRun.onPorts (a := ISA.compareRegs .eq x y) hb.injective (bank rs) small
    (fun k _ ↦ arm.initial_cap k)
  have install : installStacks ports (bank rs) localBank = bank rs :=
    installStacks_eq hb.injective _ _ (hb.inside rs)
  rw [← installStacks_update hb.injective] at cmp
  change SpaceRun _ _ _ _ (installStacks ports (bank rs) localBank) none
    (Function.update (installStacks ports (bank rs) localBank) (ports (.work 0)) [bit]) at cmp
  rw [install] at cmp
  have flag := hb.inside rs (.work 0)
  change bank rs (ports (.work 0)) = [] at flag
  have hchoice := choose_runs low high flag cmp.final_cap (b := bit)
    (by simpa only [bit, decide_eq_true_eq] using arm)
  exact FiniteRoutine.BoundedRun.followedBy cmp hchoice

variable {F : Type*} [Field F] [DecidableEq F] {n m : ℕ}

/-- The original column selected at this ordinal by the greedy row algorithm on the transpose. -/
def column (A : Matrix (Fin n) (Fin m) F) (j : Fin (rankQuery A)) : Fin m :=
  greedyRowIndex A.transpose (Fin.cast (by rw [rankQuery_eq, rankQuery_eq, Matrix.rank_transpose]) j)

/-- The original row and column bases, presented by two independent index queries. -/
def square (A : Matrix (Fin n) (Fin m) F) := A.submatrix (greedyRowIndex A) (column A)

/-- Replace the selected row of the greedy square minor by the target restricted to the same
selected columns. -/
def replaced (A : Matrix (Fin n) (Fin m) F) (target : Fin m → F) (k : Fin (rankQuery A)) :=
  (square A).updateRow k (target ∘ column A)

theorem greedyCoordinate_eq (A : Matrix (Fin n) (Fin m) F) (target : Fin m → F) (k : Fin (rankQuery A)) :
    greedyCoordinateQuery A target k = squareDetQuery (replaced A target k) / squareDetQuery (square A) :=
  greedyCoordinateQuery_eq_baseColumns A target k

/-- The two index calls precede a single scalar read. -/
def read (rows cols scalar : FiniteRoutine K) : FiniteRoutine K := (rows.followedBy cols).followedBy scalar

/-- Entry query for the unchanged square minor. The raw scalar reader sees an original
row and an original column in the caller's registers. -/
theorem read_square_runs (A : Matrix (Fin n) (Fin m) F) (i j : Fin (rankQuery A)) (rows cols scalar : FiniteRoutine K)
    {cap tr tc ts : ℕ} {start middle : Stacks K} (located : Fin n → Fin m → Stacks K) (output : F → Stacks K)
    (rowRun : rows.BoundedRun cap tr start middle)
    (colRun : cols.BoundedRun cap tc middle (located (greedyRowIndex A i) (column A j)))
    (scalarRun : scalar.BoundedRun cap ts (located (greedyRowIndex A i) (column A j))
      (output (A (greedyRowIndex A i) (column A j)))) :
    (read rows cols scalar).BoundedRun cap (tr+tc+ts) start (output (square A i j)) :=
  (rowRun.followedBy colRun).followedBy scalarRun

/-- Entry query for the row-replaced square minor. The last comparison uses the
original query ordinal, and the target is evaluated at the same selected column. -/
theorem read_replaced_runs (A : Matrix (Fin n) (Fin m) F) (target : Fin m → F)
    (k i j : Fin (rankQuery A)) {ports : ISA.Port r 0 → K} {bank : Regs r width → Stacks K}
    {persistent : Word width} (hb : RegisterBank ports bank persistent) (rowOrdinal replaceOrdinal : Fin r)
    (rows cols scalar targetRead : FiniteRoutine K) {cap tr tc ts tt : ℕ} {start middle : Stacks K}
    (located : Fin n → Fin m → Regs r width) (output : F → Stacks K)
    (rowRun : rows.BoundedRun cap tr start middle)
    (colRun : cols.BoundedRun cap tc middle (bank (located (greedyRowIndex A i) (column A j))))
    (scalarRun : scalar.BoundedRun cap ts (bank (located (greedyRowIndex A i) (column A j)))
      (output (A (greedyRowIndex A i) (column A j))))
    (targetRun : targetRead.BoundedRun cap tt (bank (located (greedyRowIndex A i) (column A j)))
      (output (target (column A j))))
    (hi : ∀ a b, (located a b rowOrdinal).val = i.val) (hk : ∀ a b, (located a b replaceOrdinal).val = k.val)
    (hc : width+(20*width+10) ≤ cap) :
    ∃ t ≤ tr+tc+(20*width+10)+(max ts tt+1),
      (read rows cols (equalBranch ports rowOrdinal replaceOrdinal scalar targetRead)).BoundedRun cap t start
        (output (replaced A target k i j)) := by
  let a := greedyRowIndex A i
  let b := column A j
  have eqTest : located a b rowOrdinal = located a b replaceOrdinal ↔ i = k := by
    rw [Fin.ext_iff, hi, hk, Fin.ext_iff]
  by_cases he : i = k
  · have arm := targetRun
    have h := equalBranch_runs hb (located a b) rowOrdinal replaceOrdinal scalar targetRead hc
      (t := tt) (out := output (target b)) (by rw [ite_eq_left (eqTest.mpr he)]; exact arm)
    refine ⟨(tr+tc)+((20*width+10)+(tt+1)), by have := Nat.le_max_right ts tt; omega, ?_⟩
    simpa only [read, replaced, he, Matrix.updateRow_self, Function.comp_apply, b] using
      (rowRun.followedBy colRun).followedBy h
  · have arm := scalarRun
    have h := equalBranch_runs hb (located a b) rowOrdinal replaceOrdinal scalar targetRead hc
      (t := ts) (out := output (A a b)) (by rw [ite_eq_right (eqTest.not.mpr he)]; exact arm)
    refine ⟨(tr+tc)+((20*width+10)+(ts+1)), by have := Nat.le_max_left ts tt; omega, ?_⟩
    simpa only [read, replaced, Matrix.updateRow_ne he, square, Matrix.submatrix_apply, a, b] using
      (rowRun.followedBy colRun).followedBy h

end RankQuery.Stack.Coordinate.Minor

end VPVNP
end Computability
end OAI
