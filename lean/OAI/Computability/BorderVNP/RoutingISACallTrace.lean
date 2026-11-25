import OAI.Computability.BorderVNP.RoutingISACallModel

/-!
# Directory traces, multiplicity and cost

One optional path outcome is stored per row. The rows without an owner match
have the unique skipped outcome. The ordinary prefix and the final loop guard
have fixed cost, and only an owned row adds a burst charge.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellDispatch

open VPVNP.BurstRAM

variable {w : ℕ}

/-- A complete choice of outcomes accepted by the indicated consecutive directory rows. -/
def Frame.Admitted (f : Frame) (m : Memory w) (macros : TeamOpcode.Macros w 8) :
    ℕ → List (Option Outcome) → Prop
  | _, [] => True
  | i, x :: xs => f.Valid m macros i x ∧ f.Admitted m macros (i+1) xs

/-- The complete loop history consists of row traces followed by a final false guard. -/
def Frame.scanTrace (f : Frame) (m : Memory w) :
    ℕ → List (Option Outcome) → List (TeamRAM.Event w)
  | _, [] => [tick w]
  | i, x :: xs => f.rowTrace m i x ++ f.scanTrace m (i+1) xs

/-- Exact cost of one iteration. The owner pays for two address additions, two
directory reads and the native burst call in place of the other teams' no-op. -/
def Frame.rowCost (f : Frame) (m : Memory w) (i : ℕ) : Option Outcome → ℕ
  | none => 7
  | some _ => 11 + (m (f.address i + 2)).val

/-- Sum of the row charges, including the final failed loop test. -/
def Frame.scanCost (f : Frame) (m : Memory w) : ℕ → List (Option Outcome) → ℕ
  | _, [] => 1
  | i, x :: xs => f.rowCost m i x + f.scanCost m (i+1) xs

private theorem trace_append (xs ys : List (TeamRAM.Event w)) :
    traceCost (xs++ys) = traceCost xs + traceCost ys := VPVNP.RAMBuckets.cost_append ..

/-- The native chronological trace incurs the sum of the actual burst and ordinary costs. -/
theorem Frame.traceCost_scan (f : Frame) (m : Memory w) (i : ℕ) (xs : List (Option Outcome)) :
    traceCost (f.scanTrace m i xs) = f.scanCost m i xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    rw [scanTrace, scanCost, trace_append, ih]
    congr 1
    cases x <;> simp [rowTrace,rowCost,callEvent,burst,traceCost,VPVNP.RAMBuckets.cost,
      TeamTranscript.Action.extra,tick,loadEvent]
    omega

/-- Exactly sixteen ordinary instructions initialize the scan. -/
theorem traceCost_setup (pub : Arg → Word w) (m : Memory w) : traceCost (setupTrace pub m) = 16 := by
  simp [traceCost, setupTrace, VPVNP.RAMBuckets.cost, TeamTranscript.Action.extra,tick,loadEvent]

/-- Setup followed by the full directory costs sixteen fixed ticks plus the charged scan. -/
theorem Frame.traceCost_directory (f : Frame) (pub : Arg → Word w) (m : Memory w)
    (xs : List (Option Outcome)) :
    traceCost (setupTrace pub m ++ f.scanTrace m 0 xs) = 16 + f.scanCost m 0 xs := by
  rw [trace_append, traceCost_setup, f.traceCost_scan]

/-- Every admitted array of private choices gives a distinct chronological trace.
The ownership comparison fixes the skip/call status at every row. -/
theorem Frame.scanTrace_inj (f : Frame) (m : Memory w) (macros : TeamOpcode.Macros w 8)
    {i : ℕ} {xs ys : List (Option Outcome)}
    (hx : f.Admitted m macros i xs) (hy : f.Admitted m macros i ys)
    (len : xs.length = ys.length) (eq : f.scanTrace m i xs = f.scanTrace m i ys) : xs = ys := by
  induction xs generalizing i ys with
  | nil => simpa using len.symm
  | cons x xs ih =>
    cases ys with
    | nil => simp at len
    | cons y ys =>
      obtain ⟨hx,tx⟩ := hx
      obtain ⟨hy,ty⟩ := hy
      have tailLen : xs.length = ys.length := by simpa using len
      by_cases own : (m (f.address i)).val = f.team
      · rw [Valid, ite_eq_left own] at hx hy
        obtain ⟨u,rfl,_⟩ := hx
        obtain ⟨v,rfl,_⟩ := hy
        simp only [scanTrace, rowTrace, List.cons_append, List.nil_append, List.cons.injEq,
          true_and] at eq
        have h₁ := congrArg TeamRAM.Event.choices eq.1
        have h₂ := congrArg TeamRAM.Event.sign eq.1
        have uv : u = v := Prod.ext h₁ h₂
        exact congrArg₂ List.cons (congrArg some uv) (ih tx ty tailLen eq.2)
      · rw [Valid, ite_eq_right own] at hx hy
        subst x y
        apply congrArg (List.cons none)
        apply ih tx ty tailLen
        exact List.append_cancel_left eq

end RoutingISA.CellDispatch

end BorderVNP
end Computability
end OAI
