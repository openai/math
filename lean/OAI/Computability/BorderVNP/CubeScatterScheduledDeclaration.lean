import OAI.Computability.BorderVNP.CubeScatterTransmissionPayload

/-! # Reading the physical shared writer's declaration after the native owner schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase RoutingISA RoutingISA.CubeLengths BorderVNP.Cube BorderVNP.Cube.Physical

variable {n blocks b h K s : ℕ} {g : SharedRows.Layout} {l : GroupWeights.Layout} {teams : TeamNative.Layout}
variable {before mem : ℕ → ℕ} {decl : LengthDeclaration n l.groups}

/-- The native weight/owner schedule preserves every word of the earlier declared
row table. Its stored group-owner words and the physical selector width give the
input frame read by the common shared-interval writer. -/
theorem SymbolFrame.of_nativeDeclaration (result : GroupWeights.ScheduleResult l teams before mem)
    (rows : StoredRows before g.lengths decl.2) (groups : g.groups = l.groups)
    (axes : g.axes = n+1) (axis : g.axis = decl.1.val)
    (selectors : g.selectors = 2*blocks*(l.groups.choose 2)^n *
      VPVNP.MotifWidths.selectorBits K (Fintype.card (Cube.Edge (n+1))) h)
    (aligned : g.owners = teams.owners)
    (room : g.lengths+l.groups*l.groups*(n+1) ≤ min l.weights (min teams.totals teams.owners)) :
    SymbolFrame g mem blocks K h decl (fun x => TeamNative.owner teams.r (l.weight before) x.val) := by
  apply SymbolFrame.of_schedule result _ aligned
  refine ⟨groups,axes,axis,?_,selectors⟩
  intro x y j
  let k := (entryOrder l.groups (n+1) ((x,y),j)).val
  have bound : k < l.groups*l.groups*(n+1) := (entryOrder l.groups (n+1) ((x,y),j)).isLt
  have fresh : g.lengths+k < min l.weights (min teams.totals teams.owners) := (Nat.add_lt_add_left bound _).trans_le room
  have ht : g.lengths+k < min teams.totals teams.owners := fresh.trans_le (min_le_right ..)
  have lw := fresh.trans_le (min_le_left ..)
  have tw := ht.trans_le (min_le_left ..)
  have ow := ht.trans_le (min_le_right ..)
  exact (result.other (g.lengths+k) (fun _ _ => by omega) (fun _ => by omega) (fun _ _ => by omega)).trans (rows x y j)

/-- On a genuine passing declaration the frame for these same physical shared
writers uses the tuple-dependent greedy owners of the manuscript's weighted groups. -/
theorem SymbolFrame.of_nativeGroupImage {A : Type*} [Fintype A]
    (result : GroupWeights.ScheduleResult l teams before mem)
    (select : Packet n l.groups blocks → Selector n K h) (pass : passesLengths b s select decl)
    (label : Fin l.cells → Label (n+1) l.groups) (recv : A → Fin l.cells) (dataWidth : A → ℕ)
    (image : GroupWeights.PhysicalImage l before blocks b K h decl label recv dataWidth)
    (groups : g.groups = l.groups) (axes : g.axes = l.axes) (axis : g.axis = l.axis)
    (selectors : g.selectors = l.selectors) (lengths : g.lengths = l.rows) (aligned : g.owners = teams.owners)
    (room : g.lengths+l.groups*l.groups*(n+1) ≤ min l.weights (min teams.totals teams.owners)) :
    SymbolFrame g mem blocks K h decl (greedyOwner teams.r b s label recv dataWidth select) := by
  have fields := SymbolFrame.of_nativeDeclaration result (lengths ▸ image.rows) groups
    (axes.trans image.axes) (axis.trans image.axis) (selectors.trans image.selectors) aligned room
  exact SymbolFrame.of_greedy result select pass label recv dataWidth image fields.toDeclarationFields aligned

end TeamContraction

end BorderVNP
end Computability
end OAI
