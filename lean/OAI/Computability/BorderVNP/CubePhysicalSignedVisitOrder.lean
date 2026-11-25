import OAI.Computability.BorderVNP.CubePhysicalReportLedger
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleNative

/-! # Actual owned-cube triple ranks for the signed path tally -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger

open Crossing Diagonal Diagonal.CellEntries RoutingISA FiniteEvaluator
open BorderVNP.Cube.Tally VPVNP.BurstRAM
open scoped Classical

variable {n d blocks b h K s D B T H U : ℕ} {P : Type*} {bits : P → ℕ}
    {Cell : Type} [DecidableEq Cell] {N : Network D P bits} {cell : N.Site → Cell}
    (tags : N.Tables (Entry (Fin H) (Fin U))) (words : PowerWords (Fin T) (Fin H) (Fin U) B N tags)
    (label : Cell → Label (n+1) d) (team : Fin d → Fin T)
    (a : Path N cell n d blocks b h K s) (t : Fin T)

/-- The genuine vertex ordering of the team's native directed symbol-pair scan. The
grouping coordinate is chosen from this very path's packet selectors. -/
noncomputable def nativeVertexOrder :
    Fin (CubeVisits.teamList (chosen b s a.2.2.2.1) blocks (Fin.val ∘ team) t.val).length ≃
      {v // pathOwner label team a (.inr v)=t} :=
  (CubeVisits.teamEquiv (chosen b s a.2.2.2.1) blocks (Fin.val ∘ team) t.val).trans
    (Equiv.subtypeEquivRight fun _ => Fin.val_inj)

/-- Keep the proven cell and use orders and number the owned vertices by their
physical rank in the true generated three-word column. -/
noncomputable def Orders.withNativeVertices (o : Orders tags words label team a t) :
    Orders tags words label team a t :=
  { o with
    nVertex := (CubeVisits.teamList (chosen b s a.2.2.2.1) blocks (Fin.val ∘ team) t.val).length
    vertices := nativeVertexOrder label team a t }

/-- The packet selectors, incident words and edge assignments passed to the native
lookup are those of the same physical path. The singleton reservation is filled
from its actual singleton word at each legal lane. -/
noncomputable def pathBanks (base singles : ℕ) : Padding.Banks.Data n d blocks b h K s :=
  ⟨chosen b s a.2.2.2.1,base,singles,a.2.2.2.1,a.2.2.1,a.2.2.2.2,
    Scatter.SingleRowData.extendSlots a.2.1⟩

variable {d' : TeamRowPrepare.Layout} {NN : Network D P bits} {host : NN.Site → Cell}

omit [DecidableEq Cell] in
/-- Reading the actual triple at its finite native rank returns the table position
of that packet and vertex in the mathematical signed expansion. -/
theorem nativeVisit_id (base singles : ℕ) (owner : Fin d'.d → Fin T)
    (path : Path NN host n d'.d blocks b h K s) (labels : Cell → Label (n+1) d'.d)
    (thisTeam : Fin T) (same : d'.teamID=thisTeam.val) (id : TableEntry n b h K s → Fin U)
    (i : Fin (CubeVisits.teamList (chosen b s path.2.2.2.1) blocks (Fin.val ∘ owner) thisTeam.val).length) :
    id ((CubeTriple.visits (l:=d') (pathBanks path base singles) (Fin.val ∘ owner)
      (Fin.cast (by rw [same]; rfl) i)).entry D) =
      pathPacketID (fun _ => id) path ((nativeVertexOrder labels owner path thisTeam) i).val := by
  let line := fun v => CubeVisits.teamList (chosen b s path.2.2.2.1) blocks (Fin.val ∘ owner) v
  have get {A : Type} {xs ys : List A} (hxy : xs=ys) (j : Fin xs.length) :
      ys.get (Fin.cast (congrArg List.length hxy) j)=xs.get j := by subst ys; rfl
  have agree := get (congrArg line same.symm) i
  let atEntry := fun pv : Packet n d'.d blocks × Vertex (n+1) =>
    id (packetEntry D b s (path.2.2.2.1 pv.1) pv.2 (path.2.2.1 pv.1) (path.2.2.2.2 pv.1))
  exact congrArg atEntry agree

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI
