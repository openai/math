import OAI.Computability.BorderVNP.CubeGroupWeightPhysicalSchedule
import OAI.Computability.BorderVNP.CubeMeanPacked
import OAI.Computability.BorderVNP.CubePhysicalTally

/-! # Native greedy ownership in the tagged path expansion

The owner of each symbol is computed from the actual selected cut, its crossing
lists, incoming deliveries and raw padded slots. Thus two selector tuples can
give different team allocations in the same polynomial path sum.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Crossing Diagonal Diagonal.CellEntries MvPolynomial
open scoped Classical

variable {n d blocks b h K s B D r : ℕ} {Cell A : Type*} [Fintype A]

/-- The integral weight word charged to the group entering the first-minimum schedule.
Addresses outside the group list have zero weight. -/
def declarationWeight (blocks b K h : ℕ) (decl : LengthDeclaration n d)
    (label : Cell → Label (n+1) d) (recv : A → Cell) (dataWidth : A → ℕ) (k : ℕ) : ℕ :=
  if hk : k < d then TeamNative.scaledWeight (incidentWidth blocks K h decl ⟨k,hk⟩)
    (incomingWidth label recv dataWidth decl.1 ⟨k,hk⟩) (groupRaw (blocks*(h*b)) decl.1 ⟨k,hk⟩)
  else 0

/-- Group ownership in the physical schedule generated from the unique passing declaration. -/
def greedyOwner (r b s : ℕ) (label : Cell → Label (n+1) d) (recv : A → Cell) (dataWidth : A → ℕ)
    (select : Packet n d blocks → Selector n K h) (g : Fin d) : Fin (r+1) :=
  let i := chosen b s select
  let decl : LengthDeclaration n d := (i,subtotals itemRow (crossCount b s select) i)
  TeamNative.owner r (declarationWeight blocks b K h decl label recv dataWidth) g.val

private theorem loads_congr (r k : ℕ) (f g : ℕ → ℕ) (he : ∀ j < k, f j = g j) :
    TeamNative.loads r f k = TeamNative.loads r g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [TeamNative.loads,ih (fun j hj => he j (by omega)),he k (by omega)]

/-- The owner RAM word written by the native group-weight program equals the physical
least-loaded team for this very selector tuple. -/
theorem greedyOwner_stored {l : GroupWeights.Layout} {teams : TeamNative.Layout} {orig mem : ℕ → ℕ}
    (result : GroupWeights.ScheduleResult l teams orig mem)
    {decl : LengthDeclaration n l.groups} (select : Packet n l.groups blocks → Selector n K h)
    (pass : passesLengths b s select decl) (label : Fin l.cells → Label (n+1) l.groups)
    (recv : A → Fin l.cells) (dataWidth : A → ℕ)
    (image : GroupWeights.PhysicalImage l orig blocks b K h decl label recv dataWidth)
    (g : Fin l.groups) :
    mem (teams.owners+g.val) = (greedyOwner teams.r b s label recv dataWidth select g).val := by
  obtain rfl := (passesLengths_iff _ _ _ _).mp pass
  rw [result.owners g g.isLt]
  unfold greedyOwner TeamNative.owner
  apply congrArg Fin.val
  apply congrArg firstMinimum
  apply loads_congr
  intro j hj
  have hk : j < l.groups := hj.trans g.isLt
  exact (image.weight_eq ⟨j,hk⟩).trans (by simp [declarationWeight,hk])

section Network
variable {P : Type*} {bits : P → ℕ} {C : Type} [Fintype C] [DecidableEq C]
variable {Param Gadget E : Type*} [Fintype Param] [Fintype Gadget] [Field E]

set_option synthInstance.maxSize 768 in
/-- The mean-balanced physical placement and the path's own native greedy team assignment
give the original network value as the sum of the realized team tallies. -/
theorem value_eq_greedy_tallied_paths {m : ℕ} (N : Network D P bits) (cell : N.Site → C)
    (recv : A → C) (dataWidth : A → ℕ) (ord : N.CrossingEdge cell ≃ Fin m)
    (cs : List C) (nodup : cs.Nodup) (cover : cs.toFinset = Finset.univ) (hd : 0 < d) (hb : 0 < h*b)
    {W : ℝ} {M : ℕ} (budget : PackedLabelBudget N cell recv dataWidth W M (d^(n+1)))
    (tags : N.Tables (Entry Param Gadget)) (x : Ports bits)
    (pos : TableEntry n b h K s → Gadget) (values : Gadget → E) (valid : ValidTables (values ∘ pos))
    (words : PowerWords (Fin (r+1)) Param Gadget B N tags) :
    let slot := meanPackedEmbedding N cell recv dataWidth ord cs nodup cover n d hd hb budget
    let label := meanPackedLabel N cell recv dataWidth cs n d hd
    let record := pathTag N cell slot tags x (fun _ => pos)
    let tally (a : Path N cell n d (blocksFor W (h*b) (d^(n+1))) b h K s) :=
      pathTally slot tags x (fun _ => pos) words label (greedyOwner r b s label recv dataWidth a.2.2.2.1) a
    N.value (fun v e p => interpret values (tags v e p)) x =
      ∑ a ∈ Finset.univ.filter (fun a => record a ≠ 0), monomial (tally a).exponents ((tally a).coefficient values) := by
  intro slot label record tally
  rw [value_eq_physical_paths N cell slot tags x (fun _ => pos) values (fun _ => valid),Finset.sum_filter]
  refine Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) ?_
  intro a _
  by_cases hz : record a = 0
  · simp only [hz,ne_self_iff_false,ite_false]
    exact congrArg (interpret values) hz
  · rw [ite_eq_left hz]
    exact interpret_path_tally slot tags x (fun _ => pos) words label
      (greedyOwner r b s label recv dataWidth a.2.2.2.1) values a hz

end Network
end Cube.Physical

end BorderVNP
end Computability
end OAI
