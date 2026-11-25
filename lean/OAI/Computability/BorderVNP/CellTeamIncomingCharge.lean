import OAI.Computability.BorderVNP.CubeHostScatterTeamClock
import OAI.Computability.BorderVNP.CubePhysicalPadding
import OAI.Computability.BorderVNP.PackedCellAddresses

/-! # Charging true cell inputs to the checked group schedule

The exterior bank of an owned cell consists of its original attached port
words and the incident ends of surviving crossing cables. Port deliveries and
one-copy opaque site descriptions charge the actual received intervals. Both
ends of a real cable may belong to the same processor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRowClock

open Physical Crossing Packing.CellAddresses
open scoped Classical

/-- Sum a quantity only over members assigned to the running team. -/
def assignedSum {I : Type*} [Fintype I] (owner : I → ℕ) (team : ℕ) (size : I → ℕ) :=
  ∑ i, if owner i = team then size i else 0

/-- Grouping a family of delivered or attached items by its actual receiving cell
preserves the selected total with its complete multiplicities. -/
theorem assignedSum_fibers {I C : Type*} [Fintype I] [Fintype C] (cell : I → C)
    (owner : C → ℕ) (team : ℕ) (size : I → ℕ) :
    assignedSum owner team (fun c => ∑ i : {i // cell i=c}, size i.val) =
      assignedSum (owner ∘ cell) team size := by
  classical
  rw [assignedSum,assignedSum,← Fintype.sum_fiberwise cell (fun i => if (owner ∘ cell) i=team then size i else 0)]
  apply Finset.sum_congr rfl
  intro c _
  have eq (i : {i // cell i=c}) : cell i.val=c := i.property
  by_cases own : owner c=team <;> simp [Function.comp_apply,eq,own]

/-- Charge a subset of the genuinely delivered fields at their true receiver.
Injectivity prevents a paid private site string from being reused as multiple
independently transported boxes. -/
theorem assignedSum_subitems {I A C : Type*} [Fintype I] [Fintype A] (select : I ↪ A)
    (cell : I → C) (recv : A → C) (owner : C → ℕ) (team : ℕ) (size : I → ℕ) (incoming : A → ℕ)
    (route : ∀ i, recv (select i)=cell i) (span : ∀ i, size i ≤ incoming (select i)) :
    assignedSum (owner ∘ cell) team size ≤ assignedSum (owner ∘ recv) team incoming := by
  classical
  let load (a : A) := if owner (recv a)=team then incoming a else 0
  calc
    _ ≤ ∑ i : I, load (select i) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp only [Function.comp_apply,load]
      rw [route]
      split <;> first | exact span i | rfl
    _ = ∑ a ∈ Finset.univ.map select, load a := (Finset.sum_map ..).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

variable {g : GroupWeights.Layout} {teams : TeamNative.Layout} {orig mem : ℕ → ℕ}
variable {n blocks b K h : ℕ} {D : LengthDeclaration n g.groups}
variable {A : Type*} [Fintype A] {label : Fin g.cells → Label (n+1) g.groups}
variable {recv : A → Fin g.cells} {incoming : A → ℕ}

/-- Incoming width counts the actual words in the stored group weight at its
full scale. Thus the true checked native team total bounds every received bit. -/
theorem assignedIncoming_le_stored (result : GroupWeights.ScheduleResult g teams orig mem)
    (image : GroupWeights.PhysicalImage g orig blocks b K h D label recv incoming) (team : Fin (teams.r+1)) :
    let owner := fun s : Fin g.groups => mem (teams.owners+s.val)
    1000000*assignedSum (fun a => owner (label (recv a) D.1)) team.val incoming ≤ mem (teams.totals+team.val) := by
  classical
  intro owner
  let group (a : A) := label (recv a) D.1
  have byGroup : assignedSum (fun a => owner (group a)) team.val incoming =
      assignedSum owner team.val (incomingWidth label recv incoming D.1) := by
    change assignedSum (owner ∘ group) team.val incoming = _
    rw [← assignedSum_fibers group owner team.val incoming]
    apply Finset.sum_congr rfl
    intro s _
    by_cases yes : owner s = team.val
    · simp only [yes,ite_true,incomingWidth]
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype _ (fun _ => by simp [group]) _).symm
    · simp [yes]
  rw [byGroup,assignedSum,Finset.mul_sum,stored_team_eq result team]
  apply Finset.sum_le_sum
  intro s _
  by_cases owns : owner s = team.val
  · simp only [← show mem (teams.owners+s.val) = owner s from rfl] at owns
    simp only [show owner s = mem (teams.owners+s.val) from rfl,owns,ite_true,result.weights _ s.isLt,
      image.weight_eq s,TeamNative.scaledWeight,Nat.mul_add]
    omega
  · change 1000000*(if owner s=team.val then _ else _) ≤ (if owner s=team.val then _ else _)
    simp [owns]

/-- Exact physical delivery words and raw padded incidence charged to one successful
native capacity check, in the unscaled bit units used by the cell preparer. -/
theorem assigned_input_bounds (result : GroupWeights.ScheduleResult g teams orig mem)
    (image : GroupWeights.PhysicalImage g orig blocks b K h D label recv incoming) (team : Fin (teams.r+1))
    (X : ℕ) (pass : TeamNative.unscale (mem (teams.totals+team.val)) ≤ (X : ℚ)/256) :
    let owner := fun s : Fin g.groups => mem (teams.owners+s.val)
    assignedSum (fun a => owner (label (recv a) D.1)) team.val incoming ≤ X ∧
      ownedRaw owner team.val (blocks*(h*b)) D.1 ≤ 1000000*X/256 := by
  intro owner
  have limit := (TeamBudget.Layout.le_teamLimit ⟨teams.r+1,X,teams.totals⟩ _).2 pass
  change mem (teams.totals+team.val) ≤ 1000000*X/256 at limit
  have h := assignedIncoming_le_stored result image team
  have d := Nat.div_le_self (1000000*X) 256
  change 1000000*assignedSum (fun a => owner (label (recv a) D.1)) team.val incoming ≤ mem (teams.totals+team.val) at h
  exact ⟨by omega,(ownedRaw_le_stored result image team).trans limit⟩

end Cube.TeamRowClock

end BorderVNP
end Computability
end OAI
