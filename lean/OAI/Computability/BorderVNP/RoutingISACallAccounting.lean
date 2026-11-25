import OAI.Computability.BorderVNP.RoutingISACallTrace

/-! # Private path identities, weights and aggregate charges in a cell directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellDispatch

open VPVNP.BurstRAM

variable {w : ℕ}

/-- Consecutive directory indices whose recorded owner is the team running the scan. -/
def Frame.ownedRows (f : Frame) (m : Memory w) (i n : ℕ) : List ℕ :=
  (List.range' i n).filter fun j => (m (f.address j)).val = f.team

private theorem scan_charge (f : Frame) (m : Memory w) (macros : TeamOpcode.Macros w 8)
    (i : ℕ) (xs : List (Option Outcome)) (ad : f.Admitted m macros i xs) :
    f.scanCost m i xs = 1 + 7 * xs.length + 4 * (f.ownedRows m i xs.length).length +
      ((f.ownedRows m i xs.length).map (fun j => (m (f.address j + 2)).val)).sum := by
  induction xs generalizing i with
  | nil => simp [Frame.scanCost, Frame.ownedRows]
  | cons x xs ih =>
    obtain ⟨valid, rest⟩ := ad
    rw [Frame.scanCost, ih (i+1) rest]
    by_cases own : (m (f.address i)).val = f.team
    · rw [Frame.Valid, ite_eq_left own] at valid
      obtain ⟨o, rfl, _⟩ := valid
      simp [Frame.rowCost, Frame.ownedRows, List.range'_succ, own]
      omega
    · rw [Frame.Valid, ite_eq_right own] at valid
      subst x
      simp [Frame.rowCost, Frame.ownedRows, List.range'_succ, own]
      omega

/-- All rows cost seven ordinary ticks, with four extra ticks and the argument length
charged at each actual owned row. The setup and the final false guard cost seventeen. -/
theorem Frame.directory_charge (f : Frame) (pub : Arg → Word w) (m : Memory w)
    (macros : TeamOpcode.Macros w 8) (xs : List (Option Outcome)) (ad : f.Admitted m macros 0 xs) :
    traceCost (setupTrace pub m ++ f.scanTrace m 0 xs) =
      17 + 7 * xs.length + 4 * (f.ownedRows m 0 xs.length).length +
        ((f.ownedRows m 0 xs.length).map (fun j => (m (f.address j + 2)).val)).sum := by
  rw [f.traceCost_directory, scan_charge f m macros 0 xs ad]
  omega

/-- The burst instructions recover the complete signed private choice strings,
including zero-bit private paths. -/
def burstOutcome (e : TeamRAM.Event w) : Option Outcome :=
  match e.action with
  | .burst .. => some (e.choices, e.sign)
  | .ordinary .. => none

private theorem scan_bursts (f : Frame) (m : Memory w) (i : ℕ) (xs : List (Option Outcome)) :
    (f.scanTrace m i xs).filterMap burstOutcome = xs.filterMap id := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    rw [Frame.scanTrace, List.filterMap_append, ih]
    cases x <;> rfl

/-- Extracting the native burst records gives exactly the ordered private path outcomes. -/
theorem Frame.directory_bursts (f : Frame) (pub : Arg → Word w) (m : Memory w)
    (xs : List (Option Outcome)) :
    (setupTrace pub m ++ f.scanTrace m 0 xs).filterMap burstOutcome = xs.filterMap id := by
  rw [List.filterMap_append, scan_bursts]
  rfl

private theorem scan_weight (f : Frame) (m : Memory w) (i : ℕ) (xs : List (Option Outcome)) :
    ((f.scanTrace m i xs).map (TeamRAM.Sign.value ∘ TeamRAM.Event.sign)).prod =
      ((xs.filterMap id).map (TeamRAM.Sign.value ∘ Prod.snd)).prod := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    rw [Frame.scanTrace, List.map_append, List.prod_append, ih]
    cases x <;> simp [Frame.rowTrace, tick, loadEvent, Frame.callEvent, TeamRAM.Sign.value]

/-- The entire native history has the product of the private path signs, with multiplicities. -/
theorem Frame.directory_weight (f : Frame) (pub : Arg → Word w) (m : Memory w)
    (xs : List (Option Outcome)) :
    ((setupTrace pub m ++ f.scanTrace m 0 xs).map (TeamRAM.Sign.value ∘ TeamRAM.Event.sign)).prod =
      ((xs.filterMap id).map (TeamRAM.Sign.value ∘ Prod.snd)).prod := by
  rw [List.map_append, List.prod_append, scan_weight]
  change 1 * _ = _
  exact one_mul _

end RoutingISA.CellDispatch

end BorderVNP
end Computability
end OAI
