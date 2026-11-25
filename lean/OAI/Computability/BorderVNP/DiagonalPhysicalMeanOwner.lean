import OAI.Computability.BorderVNP.CubePhysicalGreedyTally
import OAI.Computability.BorderVNP.DiagonalPhysicalAssignments

/-! # The public cell placement and native owner used for each diagonal path -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.PacketPlacement

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical
open scoped Classical

variable {D n d b h K : ℕ} {Team C A P : Type} {bits : P → ℕ}
variable [Fintype C] [DecidableEq C] [Fintype A]

/-- The public placement selects its actual padded wire slots and its first-minimum
team for every possible selector tuple. The equivalence numbers physical teams
in exactly the order in which the native assignment scans them. -/
noncomputable def ofNativeMean {r : ℕ} (number : Fin (r+1) ≃ Team) (s : ℕ)
    (N : Network D P bits) (cell : N.Site → C) (recv : A → C) (w : A → ℕ)
    {m : ℕ} (ord : N.CrossingEdge cell ≃ Fin m) (cs : List C) (hn : cs.Nodup)
    (cover : cs.toFinset = Finset.univ) (hd : 0 < d) (hb : 0 < h*b) {W : ℝ} {M : ℕ}
    (budget : PackedLabelBudget N cell recv w W M (d^(n+1))) : PacketPlacement Team n d b h K N :=
  ofMean N cell recv w ord cs hn cover hd hb budget
    (fun u g => number (greedyOwner r b s (meanPackedLabel N cell recv w cs n d hd) recv w u g))

omit [Fintype C] [DecidableEq C] in
/-- Reindexing the cells of a packed network to the native directory preserves the
declared symbol weights and therefore every greedy owner. -/
theorem greedyOwner_reindex {r blocks s : ℕ} {C' : Type} (cells : C ≃ C') (label : C → Label (n+1) d)
    (recv : A → C) (w : A → ℕ) (select : Packet n d blocks → Selector n K h) (g : Fin d) :
    greedyOwner r b s (label ∘ cells.symm) (cells ∘ recv) w select g = greedyOwner r b s label recv w select g := by
  let decl : LengthDeclaration n d := (chosen b s select,subtotals itemRow (crossCount b s select) (chosen b s select))
  apply congrArg (fun f : ℕ → ℕ => TeamNative.owner r f g.val) (a₁ := declarationWeight blocks b K h decl _ _ w)
  funext k
  simp [declarationWeight,incomingWidth,decl]

/-- The owner used by the diagonal path sum has exactly the team number read from the
native owner table after the unique passing length declaration is scheduled. -/
theorem ofNativeMean_owner_stored {l : GroupWeights.Layout} {teams : TeamNative.Layout}
    (number : Fin (teams.r+1) ≃ Team) (s : ℕ) (N : Network D P bits)
    (cell : N.Site → C) (recv : A → C) (w : A → ℕ) (cells : C ≃ Fin l.cells) {m : ℕ}
    (ord : N.CrossingEdge cell ≃ Fin m) (cs : List C) (hn : cs.Nodup) (cover : cs.toFinset = Finset.univ)
    (hd : 0 < l.groups) (hb : 0 < h*b) {W : ℝ} {M : ℕ}
    (budget : PackedLabelBudget N cell recv w W M (l.groups^(n+1)))
    {orig mem : ℕ → ℕ} (sched : GroupWeights.ScheduleResult l teams orig mem)
    (select : Packet n l.groups (blocksFor W (h*b) (l.groups^(n+1))) → Selector n K h)
    {decl : LengthDeclaration n l.groups} (pass : passesLengths b s select decl)
    (image : GroupWeights.PhysicalImage l orig (blocksFor W (h*b) (l.groups^(n+1))) b K h decl
      (meanPackedLabel N cell recv w cs n l.groups hd ∘ cells.symm) (cells ∘ recv) w)
    (g : Fin l.groups) :
    let placement : PacketPlacement Team n l.groups b h K N := ofNativeMean number s N cell recv w ord cs hn cover hd hb budget
    mem (teams.owners+g.val) = (number.symm (placement.team select g)).val := by
  intro placement
  have eq := greedyOwner_stored sched select pass _ _ _ image g
  rw [greedyOwner_reindex cells] at eq
  simpa only [placement,ofNativeMean,ofMean,Equiv.symm_apply_apply] using eq

end Diagonal.CellEntries.PacketPlacement

end BorderVNP
end Computability
end OAI
