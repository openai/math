import OAI.Computability.NearSquareRoot.VisitedCells
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.EquivFin

/-!
# Aligned scans on physical tapes

The linear tables in an interchange stage take a column from a fixed family
of aligned streams to an equally sized output column. Intermediate streams
and copies can be assigned extra tracks of that family. This machine writes
the table output in place and rewinds every tape to its initial head position.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeScan

open IntegerMultiplication

inductive Phase
  | forward | rewind | halt
  deriving DecidableEq

instance : Finite Phase :=
  Finite.of_injective (fun s : Phase => (match s with
    | .forward => 0 | .rewind => 1 | .halt => 2 : Fin 3))
    (by intro a b h; cases a <;> cases b <;> first | rfl | contradiction)

variable {A I : Type} [Inhabited A]

/-- A distinguished stream supplies the end-of-data test; all streams share
its length. The extra alphabet letter is blank. -/
def rule (ref : I) (table : (I → A) → I → A) : TM.Rule (Option A) Phase I
  | .forward, read =>
      if (read ref).isSome then
        some (.forward, fun i => (some (table (fun j => (read j).getD default) i), .right))
      else some (.rewind, fun i => (read i, .left))
  | .rewind, read =>
      if (read ref).isSome then some (.rewind, fun i => (read i, .left))
      else some (.halt, fun i => (read i, .right))
  | .halt, _ => none

/-- Absolute tape contents represented relative to head position `p`. -/
private def tapeAt (p : ℤ) (v : ℤ → Option A) : TM.Tape (Option A) :=
  ⟨p, fun d => v (p+d)⟩

def configAt (phase : Phase) (p : ℤ) (v : ℤ → I → Option A) :
    TM.Config (Option A) Phase I :=
  ⟨phase, fun i => tapeAt p (fun z => v z i)⟩

/-- Well-formed aligned streams put every component of a row in the same
absolute position. Values of `x` outside the given interval are ignored. -/
def streams (n : ℕ) (x : ℤ → I → A) : ℤ → I → Option A :=
  fun z i => if 0 ≤ z ∧ z < (n : ℤ) then some (x z i) else none

private def scanned (n : ℕ) (x : ℤ → I → A) (table : (I → A) → I → A) (k : ℕ) :=
  streams n (fun z => if z < (k : ℤ) then table (x z) else x z)

omit [Inhabited A] in
private theorem stepAt {m : TM.Rule (Option A) Phase I} {q q' : Phase}
    {p : ℤ} {v v' : ℤ → I → Option A} {write : I → Option A} {d : TM.Move}
    (hstep : m q (v p) = some (q', fun i => (write i, d)))
    (here : ∀ i, write i = v' p i)
    (away : ∀ z, z ≠ p → ∀ i, v z i = v' z i) :
    TM.advance m (configAt q p v) = some (configAt q' (p+d.shift) v') := by
  unfold TM.advance
  simp only [configAt, tapeAt, add_zero, hstep, Option.map_some, Option.some.injEq,
    TM.Config.mk.injEq, true_and]
  funext i
  unfold TM.Tape.apply
  congr 1
  funext z
  change (if z + d.shift = 0 then write i else v (p + (z+d.shift)) i) = v' (p+d.shift+z) i
  split_ifs with hz
  · rw [show p + d.shift + z = p by omega, here]
  · have e : p + (z + d.shift) ≠ p := by omega
    rw [away _ e, show p + (z+d.shift) = p + d.shift + z by omega]

private theorem advanceForward {n k : ℕ} (hk : k < n) (x : ℤ → I → A)
    (ref : I) (table : (I → A) → I → A) :
    TM.advance (rule ref table) (configAt .forward k (scanned n x table k)) =
      some (configAt .forward (k+1) (scanned n x table (k+1))) := by
  apply stepAt (d := .right) (write := fun i => some (table (x k) i))
  · have h : (k : ℤ) < n := by exact_mod_cast hk
    simp [rule, scanned, streams, h]
  · intro i
    have h : (k : ℤ) < n := by exact_mod_cast hk
    simp [scanned, streams, h]
  · intro z hz i
    have he : z < (k:ℤ)+1 ↔ z < (k : ℤ) := by omega
    simp [scanned, streams, he]

private theorem advanceTurn (n : ℕ) (ref : I) (table : (I → A) → I → A)
    (v : ℤ → I → Option A) (hv : v n ref = none) :
    TM.advance (rule ref table) (configAt .forward n v) =
      some (configAt .rewind ((n : ℤ)-1) v) := by
  apply stepAt (d := .left) (write := v n) (by simp [rule, hv]) <;> intros <;> rfl

private theorem advanceBack (p : ℤ) (ref : I) (table : (I → A) → I → A)
    (v : ℤ → I → Option A) (hv : (v p ref).isSome = true) :
    TM.advance (rule ref table) (configAt .rewind p v) =
      some (configAt .rewind (p-1) v) := by
  apply stepAt (d := .left) (write := v p) (by simp [rule, hv]) <;> intros <;> rfl

private theorem advanceHalt (ref : I) (table : (I → A) → I → A)
    (v : ℤ → I → Option A) (hv : v (-1) ref = none) :
    TM.advance (rule ref table) (configAt .rewind (-1) v) =
      some (configAt .halt 0 v) := by
  apply stepAt (d := .right) (write := v (-1)) (by simp [rule, hv]) <;> intros <;> rfl

private def trajectory (n : ℕ) (x : ℤ → I → A) (table : (I → A) → I → A) (t : ℕ) :=
  if t ≤ n then configAt .forward t (scanned n x table t)
  else if t ≤ 2*n+1 then configAt .rewind (2*(n : ℤ)-t) (scanned n x table n)
  else configAt .halt 0 (scanned n x table n)

private theorem trajectory_step {n t : ℕ} (ht : t < 2*n+2) (x : ℤ → I → A)
    (ref : I) (table : (I → A) → I → A) :
    TM.advance (rule ref table) (trajectory n x table t) =
      some (trajectory n x table (t+1)) := by
  by_cases h : t < n
  · simpa [trajectory, Nat.le_of_lt h, Nat.succ_le_of_lt h] using advanceForward h x ref table
  by_cases he : t = n
  · subst t
    simpa [trajectory, show n+1 ≤ 2*n+1 by omega, show ¬ n+1 ≤ n by omega,
      show (2*(n : ℤ)-(n+1)) = n-1 by omega] using
      advanceTurn n ref table (scanned n x table n) (by simp [scanned, streams])
  by_cases hb : t < 2*n+1
  · have hn : ¬ t ≤ n := by omega
    have hn' : ¬ t+1 ≤ n := by omega
    have h₁ : 0 ≤ 2*(n:ℤ)-t := by omega
    have h₂ : 2*(n:ℤ)-t < n := by omega
    have hh := advanceBack (2*(n:ℤ)-t) ref table (scanned n x table n)
      (by simp only [scanned, streams, h₁, h₂, and_self, ite_true, Option.isSome_some])
    simpa [trajectory, hn, hn', Nat.le_of_lt hb, Nat.succ_le_of_lt hb,
      show 2*(n:ℤ)-((t:ℤ)+1)=2*(n:ℤ)-t-1 by omega] using hh
  · have e : t = 2*n+1 := by omega
    subst t
    simpa [trajectory,show ¬ 2*n+1 ≤ n by omega, show ¬ 2*n+1+1 ≤ n by omega,
      show ¬ 2*n+1 ≤ 2*n by omega, show 2*(n:ℤ)-(2*n+1) = -1 by omega] using
      advanceHalt ref table (scanned n x table n) (by simp [scanned, streams])

private theorem reaches {n : ℕ} (x : ℤ → I → A) (ref : I) (table : (I → A) → I → A)
    (t : ℕ) (ht : t ≤ 2*n+2) :
    Trace (TM.advance (rule ref table)) (trajectory n x table 0) t (trajectory n x table t) := by
  induction t with
  | zero => exact .nil _
  | succ t ih => exact (ih (by omega)).trans (.single (trajectory_step (by omega) x ref table))

omit [Inhabited A] in
private theorem get_initial (n : ℕ) (x : ℤ → I → A) (table : (I → A) → I → A) :
    scanned n x table 0 = streams n x := by
  funext z i
  by_cases h : 0 ≤ z <;> simp [scanned, streams, h, not_lt.mpr]

omit [Inhabited A] in
private theorem get_final (n : ℕ) (x : ℤ → I → A) (table : (I → A) → I → A) :
    scanned n x table n = streams n (fun z => table (x z)) := by
  funext z i
  by_cases h : z < n <;> simp [scanned, streams, h]

/-- The run starts at zero, halts at zero, and includes both end tests.
Each tape visits only cells in `[-1,n]`, including on the rewind. -/
theorem table_scan (n : ℕ) (x : ℤ → I → A) (ref : I) (table : (I → A) → I → A) :
    let start := configAt .forward 0 (streams n x)
    let stop := configAt .halt 0 (streams n (fun z => table (x z)))
    Trace (TM.advance (rule ref table)) start (2*n+2) stop ∧
    TM.advance (rule ref table) stop = none ∧
    ∀ t ≤ 2*n+2, ∀ c, Trace (TM.advance (rule ref table)) start t c →
      ∀ i, -1 ≤ (c.tape i).pos ∧ (c.tape i).pos ≤ n := by
  have hi : trajectory n x table 0 = configAt .forward 0 (streams n x) := by
    simp [trajectory, get_initial]
  have hf : trajectory n x table (2*n+2) =
      configAt .halt 0 (streams n (fun z => table (x z))) := by
    simp [trajectory, show ¬ 2*n+2 ≤ n by omega, show ¬ 2*n+2 ≤ 2*n+1 by omega, get_final]
  refine ⟨hi ▸ hf ▸ reaches x ref table (2*n+2) le_rfl, rfl, ?_⟩
  intro t ht c hc i
  rw [← hi] at hc
  rw [trace_endpoint_unique hc (reaches x ref table t ht)]
  unfold trajectory
  split_ifs <;> simp only [configAt, tapeAt] <;> omega

/-- Actual P192 input tapes loaded by finite, aligned words. -/
def loadedRows {n : ℕ} (q : Phase) (x : Fin n → I → A) : TM.Config (Option A) Phase I :=
  ⟨q, fun i => TM.Tape.loaded none (List.ofFn (fun j : Fin n => some (x j i)))⟩

private def extendRows {n : ℕ} (x : Fin n → I → A) (z : ℤ) : I → A :=
  if h : z.toNat < n then x ⟨z.toNat, h⟩ else fun _ => default

omit [Inhabited A] in
private theorem initial_rows {n : ℕ} (q : Phase) (x : Fin n → I → A) (y : ℤ → I → A)
    (hy : ∀ j : Fin n, y j = x j) :
    configAt q 0 (streams n y) = loadedRows q x := by
  apply congrArg (TM.Config.mk q)
  funext i
  apply congrArg (TM.Tape.mk 0)
  funext z
  cases z with
  | ofNat k =>
    by_cases h : k < n
    · let j : Fin n := ⟨k,h⟩
      have hh : y (Int.ofNat k) i = x j i := congrFun (hy j) i
      simpa [streams, h] using hh
    · simp [streams, h]
  | negSucc k =>
    simp [streams]

/-- Fixed finite-alphabet table evaluation on genuine loaded streams, with
the number of visited tape/address pairs bounded across the complete trace. -/
theorem loaded_table_scan [Fintype I] (ref : I) (table : (I → A) → I → A) {n : ℕ}
    (x : Fin n → I → A) :
    let start := loadedRows .forward x
    let stop := loadedRows .halt (fun j => table (x j))
    Trace (TM.advance (rule ref table)) start (2*n+2) stop ∧
    TM.advance (rule ref table) stop = none ∧
    VisitsAtMost (rule ref table) start (2*n+2) (Fintype.card I * (n+2)) := by
  have hx (j : Fin n) : extendRows x j = x j := by simp [extendRows]
  have a := table_scan n (extendRows x) ref table
  dsimp only at a ⊢
  rw [initial_rows _ _ _ hx, initial_rows _ (fun j => table (x j)) _ (fun j => congrArg table (hx j))] at a
  refine ⟨a.1, a.2.1, ?_⟩
  convert visitsAtMost_of_common_fence (-1) n a.2.2 using 2
  omega

end InterchangeScan

end NearSquareRoot
end Computability
end OAI
