import OAI.Computability.BorderVNP.FiniteEvaluatorCubeBanks
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeVisitTeams
import OAI.Computability.BorderVNP.FiniteDiagonalCubePlan

/-! # All native vertex reads on one complete routed field assignment

Each directory rank is the corresponding entry of the actual team traversal.
Its visit uses the physical packet-bank address and the assignment recovered
from the routed words. Multiplying these addressed entries recovers exactly
the cube factor in the fully opened field path.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally Padding.Banks
open FiniteEvaluator RoutingISA VPVNP.BurstRAM DiagonalTallyPacketEmit
open scoped Classical BigOperators

variable {D R w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable (V : FieldRawLayout L S) (R : ℕ) (raw : V.Raw R)

local notation "axis" => chosen L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "path" => Prod.snd (V.read R raw)

/-- Packets and vertices in the exact order of this team's native triple directory. -/
noncomputable def teamPairs (team : Fin (R+1)) :=
  CubeVisits.teamList axis L.blocks (V.owners R raw.1.1) team

/-- Physical lookup on the actual local directory ordinal. -/
noncomputable def teamVisit (packetBase : ℕ) (team : Fin (R+1)) (j : Fin (V.teamPairs R raw team).length) :
    Visit L.dimension L.bitWidth L.copies L.alternatives L.supply :=
  let pv := (V.teamPairs R raw team).get j
  V.visit R raw packetBase pv.1 pv.2

/-- Every lookup in the emitted directory has its true selector and incident
wire words in the team's memory after a successful owned-group traversal. -/
theorem team_banks (packetBase singleBase : ℕ) (m : Memory w) (team : Fin (R+1))
    (views : ∀ x, V.owners R raw.1.1 (x.row axis).1=team → (V.bankData R raw packetBase singleBase).Holds m x)
    (j : Fin (V.teamPairs R raw team).length) :
    let z := V.teamVisit R raw packetBase team j
    VertexAt m z.base z.selector z.vertex z.ends z.supply :=
  V.visit_of_owned R raw packetBase singleBase m team views _ _
    ((CubeVisits.mem_teamList ..).mp (List.get_mem (V.teamPairs R raw team) j))

/-- The actual assigned scalar of a local directory position. -/
noncomputable def teamEntry (packetBase : ℕ) (team : Fin (R+1)) (j : Fin (V.teamPairs R raw team).length) : F :=
  L.table ((V.teamPairs R raw team).get j).1 ((V.teamVisit R raw packetBase team j).entry D)

/-- The product of all true local directory reads over all teams is precisely
the assigned cube product, permitting packet-dependent scalar tables. -/
theorem team_entries (packetBase : Fin (R+1) → ℕ) :
    (∏ t : Fin (R+1), ∏ j : Fin (V.teamPairs R raw t).length, V.teamEntry R raw (packetBase t) t j) =
      cubeTermWeight L.table (fun _ _ => 1) path.2 := by
  let factor (pv : Packet L.dimension L.alphabet L.blocks × Vertex (L.dimension+1)) :=
    (packetNetwork D L.bitWidth L.supply (path.2.2.2.1 pv.1)).read (packetTables (L.table pv.1) D (path.2.2.2.1 pv.1))
      (path.2.2.2.2 pv.1) (path.2.2.1 pv.1) pv.2
  calc
    _ = ∏ t : Fin (R+1), ∏ j : Fin (V.teamPairs R raw t).length, factor ((V.teamPairs R raw t).get j) :=
      Finset.prod_congr rfl fun t _ => Finset.prod_congr rfl fun j _ =>
        V.visit_value R raw (packetBase t) _ _
    _ = ∏ pv, factor pv := CubeVisits.team_product axis L.blocks (V.owners R raw.1.1) factor
    _ = _ := by rw [Fintype.prod_prod_type,cubeTermWeight,one_mul]; rfl

/-- Each complete raw path carries the sparse host value times precisely the
entries of the addressed team vertex directories. -/
theorem pathValue_team_entries (x : Ports bits) (packetBase : Fin (R+1) → ℕ) :
    S.pathValue L x path (V.read R raw).1 =
      S.hostValue L x path (V.read R raw).1 *
        ∏ t : Fin (R+1), ∏ j : Fin (V.teamPairs R raw t).length, V.teamEntry R raw (packetBase t) t j := by
  rw [V.team_entries R raw packetBase,FieldSiteDirectory.pathValue]

end FiniteDiagonal.FieldRawLayout

namespace FiniteDiagonal.FieldPacketPlan

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical Diagonal
open scoped Classical

variable {D m d : ℕ} {P : Type*} {bits : P → ℕ} {F : Type*} [Field F]
  {Cell A : Type} [Fintype Cell] [DecidableEq Cell] [Fintype A]
  (N : Network D P bits) [DecidableEq N.Edge] (cell : N.Site → Cell)
  (recv : A → Cell) (dataWidth : A → ℕ) (ord : N.CrossingEdge cell ≃ Fin m)
  (cs : List Cell) (hcs : cs.toFinset = Finset.univ) (cube : FixedCube F) (hd : 0 < d)
  {W : ℝ} {M : ℕ} (budget : PackedLabelBudget N cell recv dataWidth W M (d^(cube.pred+1)))

/-- Every local read in the deterministically balanced public plan uses the scalar
table of the selected finite cube identity. The same installed deck serves all packets. -/
theorem publicPlan_table (p : Packet cube.pred d (blocksFor W (cube.h*cube.b) (d^(cube.pred+1)))) :
    (publicPlan N cell recv dataWidth ord cs hcs cube hd budget).table p = cube.table := rfl

end FiniteDiagonal.FieldPacketPlan

end BorderVNP
end Computability
end OAI
