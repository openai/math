import OAI.Hierarchy.DescentSeedIncidenceLoad
import OAI.Hierarchy.DescentSeedSiteGeometry
import OAI.Hierarchy.DescentSeedMarkedGraph
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! Packed original census and actor cells on each padded host. -/
namespace Hierarchy.DescentInitialHost.PackedSeed
open DescentSixParty Catalyst DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)
local notation "N" => X.network.copyGraph
local notation "A" => markedInput X
abbrev Original (v : Site N) := {e : (A).graph.Edge // (A).graph.src e=v ∧ e∈(A).core}

def value (marked : Bool) (wire hist s : ℕ) (v : Site N) : ℕ :=
  if marked then Fintype.card (Original X v) else
    incidenceLoad N (wire*s) 256 v + if hubFlag N v then 0 else hist

end
end Hierarchy.DescentInitialHost.PackedSeed

namespace Hierarchy.DescentInitialHost.PackedSeed
set_option Elab.async false
open Catalyst DescentSIMDLookup
open scoped Classical Fin.CommRing

noncomputable def fixedRow {F : Type} [Field F] {k p H : ℕ}
    (X : Approximation F k p) (host : Site X.network.copyGraph ↪ Fin H)
    (marked : Bool) (wire hist s b l : ℕ) (v : Fin H) : Cell (b * 2 ^ l) :=
  DescentSIMDLookup.encode b (2 ^ l) (fun _ =>
    dite (∃ u : Site X.network.copyGraph, host u = v)
      (fun found => (value X marked wire hist s found.choose : Cell b))
      (fun _ => 0))

noncomputable def actorRow {F : Type} [Field F] {k p H : ℕ}
    (X : Approximation F k p) (host : Site X.network.copyGraph ↪ Fin H)
    (l : ℕ) (v : Fin H) : Cell (1 * 2 ^ l) :=
  DescentSIMDLookup.encode 1 (2 ^ l) (fun _ =>
    ite (∃ u : Site X.network.copyGraph, host u = v) (1 : Cell 1) 0)

end Hierarchy.DescentInitialHost.PackedSeed

end OAI
