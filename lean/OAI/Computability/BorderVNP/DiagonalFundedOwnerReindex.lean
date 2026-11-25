import OAI.Computability.BorderVNP.PackedNativeDemandCableCast
import OAI.Computability.BorderVNP.CubeScatterReturnedOwnedFamily

/-! # Original ownership on the native report's reindexed cable directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical

variable {D C ne ne' np n d blocks K h : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (edge : N.Edge ↪ Fin ne) (he : ne=ne')
    (port : P ↪ Fin np) (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site)
    (live : (Fin dir.teams × Fin dir.sites) ↪ P) (gap : ℕ) (bounds : dir.DestinationBounds)

local notation3 (prettyPrint := false) "castEdge" => edge.trans (finCongr he).toEmbedding
local notation3 (prettyPrint := false) "recv[" e "]" => receiver N cell e port dir old live gap bounds
local notation3 (prettyPrint := false) "width[" e "]" => fun i : Fin (rows N cell e port dir old live gap).length =>
  (rows N cell e port dir old live gap)[i.val].width

/-- Reindexing the padded cable rectangle preserves the whole greedy
allocation. Both the incoming volumes and their receiver indices change
together with the dependent row list. -/
theorem greedyOwner_cast_cables (R b s : ℕ) (label : Fin C → Label (n+1) d) :
    greedyOwner (blocks:=blocks) (K:=K) (h:=h) R b s label recv[castEdge] width[castEdge] =
      greedyOwner R b s label recv[edge] width[edge] := by
  subst ne'
  rfl

end Packing.RoutingOutputs.NativeDemands

namespace TeamContraction

open _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical _root_.OAI.Computability.BorderVNP.Cube.Scatter _root_.OAI.Computability.BorderVNP.Cube.Scatter.Assignment RoutingISA

/-- Transport the actual recorded route and its host-table read together.
The new assignment has precisely the selectors of the original assignment. -/
theorem reindexIssuedOwner {R w : ℕ} {ar : CubeArena.Layout}
    {decl : LengthDeclaration ar.n ar.header.d} {group : Fin ar.header.d → Fin (R+1)}
    {family : TeamRows.Returns (Fin (R+1)) ar w} {raw : Symbols ar.header.d → List Bool}
    {registered native : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) →
      Fin ar.header.d → Fin (R+1)}
    {q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) registered}
    {Cell : Type*} {oldLabel label : Cell → Label (ar.n+1) ar.header.d} {word : Cell → ℕ}
    (owners : registered=native) (labels : oldLabel=label)
    (original : ObservedOwned ar decl group family registered raw q)
    (read : ∀ c, word c=(registered q.1 (oldLabel c (chosen ar.b ar.s q.1))).val) :
    ∃ assigned : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) native,
      assigned.1=q.1 ∧ ObservedOwned ar decl group family native raw assigned ∧
      ∀ c, word c=(native assigned.1 (label c (chosen ar.b ar.s assigned.1))).val := by
  subst native label
  exact ⟨q,rfl,original,read⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
