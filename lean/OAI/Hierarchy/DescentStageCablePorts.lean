import OAI.Hierarchy.DescentGrainSizes
import OAI.Hierarchy.DescentPackedCensusPorts

namespace OAI
/-! # Authentic local signed cable ports at a selected group stage -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentColonies StarKeys PackedCensus DescentCompiler
open scoped Classical BigOperators
noncomputable section

variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
  {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (S : AtomSchedule)
local notation "Q" => (A.z*G.b)
abbrev CellPorts (g : J) (v : V) (x : Block k) := Ports W A.pos A.block A.grainCount (g,v) x

theorem quantum_positive (e : W.graph.Edge) (mem : e∈W.core) : 0<A.grainCount e := by
  simpa only [grainCount, A.widths e mem, Nat.div_self (Nat.mul_pos A.unitPos G.base_pos)]
    using Nat.zero_lt_one

theorem local_port_count (ready : A.StateBounds S i) (g : J) (v : V) (x : Block k) :
    Fintype.card (A.CellPorts g v x)≤A.cap :=
  ports_fit W A.pos A.block A.grainCount (fun q=>A.hub q.2) A.records A.wire A.hist Q A.cap
    (Nat.mul_pos A.wirePos (Nat.mul_pos A.unitPos G.base_pos))
    (A.grainCount_fit S ready) (g,v) x (A.small (g,v) x)

/-- A chronological producer may permute the real local slots independently
in every group. The chosen map is used by both masks on the same cable. -/
abbrev PortOrder (cap : ℕ) := ∀u : J×V,∀x : Block k,A.CellPorts u.1 u.2 x ↪ Fin cap

def order_of_cap (ready : A.StateBounds S i) {cap : ℕ} (room : A.cap≤cap) : A.PortOrder cap :=
  fun u x=>(Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb ((A.local_port_count S ready u.1 u.2 x).trans room))

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
