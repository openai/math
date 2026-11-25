import OAI.Computability.BorderVNP.DiagonalPreparedBroadcastGuards
import OAI.Computability.BorderVNP.CubePhysicalGreedyTally
import OAI.Computability.BorderVNP.RoutingISASignedPrepBroadcast

/-! # The same cube declaration capacity on every prepared positive team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open VPVNP.BurstRAM GroupWeights RoutingISA RoutingISA.LocalRow
open scoped BigOperators
open private loads_congr from OAI.Computability.BorderVNP.CubePhysicalGreedyTally

/-- Public group and total checks expressed on the common physical cells and
delivery rows. These amounts include the chosen cube coordinate, all incident
lists, delivered data, and the raw slot charge. -/
def declarationCapacity {n d : ℕ} {A Cell : Type*} [Fintype A]
    (R X blocks b K h : ℕ) (decl : LengthDeclaration n d)
    (label : Cell → Label (n+1) d) (recv : A → Cell) (size : A → ℕ) : Prop :=
  let weight := declarationWeight blocks b K h decl label recv size
  let budget : TeamBudget.Layout := ⟨R+1,X,0⟩
  (∀ j, TeamNative.loads R weight d j ≤ budget.teamLimit) ∧
    (∑ i ∈ Finset.range d, weight i) ≤ budget.totalLimit

/-- A native weight table representing the fixed public rows performs the two
checks on their actual, shared numerical values. Thus a successful preparation
on one team certifies the same bound at every equivalent row layout. -/
theorem declarationCapacity_iff {n blocks b K h X : ℕ} {l : GroupWeights.Layout} {t : TeamNative.Layout}
    {input : ℕ → ℕ} {decl : LengthDeclaration n l.groups} {A : Type*} [Fintype A]
    {label : Fin l.cells → Label (n+1) l.groups} {recv : A → Fin l.cells} {size : A → ℕ}
    (image : PhysicalImage l input blocks b K h decl label recv size) :
    capacities l t X input ↔ declarationCapacity t.r X blocks b K h decl label recv size := by
  let weight := declarationWeight blocks b K h decl label recv size
  have words (i : ℕ) (hi : i < l.groups) : l.weight input i = weight i :=
    (image.weight_eq ⟨i,hi⟩).trans (by simp only [weight,declarationWeight,dite_eq_left hi])
  have load := loads_congr t.r l.groups (l.weight input) weight words
  have total : (∑ i ∈ Finset.range l.groups, l.weight input i) = ∑ i ∈ Finset.range l.groups, weight i :=
    Finset.sum_congr rfl (fun i hi => words i (Finset.mem_range.mp hi))
  unfold capacities declarationCapacity
  rw [load,total]
  rfl

/-- At a fixed public geometry a header is eligible exactly when its
coordinate minimizes its announced row sums and those rows fit the shared
greedy schedule. Range is checked separately on the incoming bits. -/
def broadcastAllowed {n d cap : ℕ} {A Cell : Type*} [Fintype A]
    (R X blocks b K h : ℕ) (label : Cell → Label (n+1) d) (recv : A → Cell) (size : A → ℕ)
    (raw : Broadcast n d cap) : Prop :=
  let decl : LengthDeclaration n d := (Fin.ofNat (n+1) (readCode (n+1) raw.1),
    fun pair j => readCode (cap+1) (raw.2 pair j))
  LocalRow.declaredMinimum raw ∧ declarationCapacity R X blocks b K h decl label recv size

end Cube.Physical

end BorderVNP
end Computability
end OAI
