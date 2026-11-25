import OAI.Hierarchy.TaggedWirePhysicalMatrix
import OAI.Hierarchy.ProbePlacedPacket
import OAI.Hierarchy.ProbeBroadcastMatrix

namespace OAI
/-! # Literal signed packet matrices on native demand, installed, and broadcast rows -/

noncomputable section
namespace Hierarchy.WireTelescope.PhysicalMatrix
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.Diagonal.MotifOuterTerms
open Probe
open scoped BigOperators Classical

variable {k S : ℕ} [Nonempty (Fin k)] {F E A B : Type} [Field F] [Fintype E] [Fintype A] [Fintype B]
variable {edge : E→Chord k} {req : A→E} (P : Packet F edge req) (place : Fin k ↪ Fin S)
omit [Nonempty (Fin k)] in
private theorem packet_input (root : Fin k) (r : ℕ) :
    placeWidths place (P.inputWidths r)=optionWidths (fun a=>physicalChord place (edge (req a))) (fun _=>r*P.width) := by
  let : Nonempty (Fin S) := ⟨place root⟩
  exact physical_demand (edge:=edge) (req:=req) place P.width r

omit [Nonempty (Fin k)] in
private theorem packet_output (root : Fin k) (r : ℕ) (G : PortGraph (Fin k) B)
    (h : Histogram (Fin P.terms) r) :
    placeWidths place (P.outputWidths h+G.chordWidths (fun _=>r*P.selectorBits))=
      optionWidths (fun e=>physicalChord place (edge e)) (histWidth P.count h)+
        placeWidths place (G.chordWidths (fun _=>r*P.selectorBits)) := by
  let : Nonempty (Fin S) := ⟨place root⟩
  rw [map_add]
  exact congrArg (· + placeWidths place (G.chordWidths (fun _=>r*P.selectorBits)))
    (physical_histogram_width P h place)

def packetMatrix (root : Fin k) (r : ℕ) (G : PortGraph (Fin k) B) (h : Histogram (Fin P.terms) r) :
    SiteMatrix (State (optionWidths (fun a=>physicalChord place (edge (req a))) (fun _=>r*P.width)))
      (State (optionWidths (fun e=>physicalChord place (edge e)) (histWidth P.count h) +
        placeWidths place (G.chordWidths (fun _=>r*P.selectorBits)))) F := by
  exact cast (congrArg₂ (fun u v : Widths S=>SiteMatrix (State u) (State v) F)
    (packet_input P place root r) (packet_output P place root r G h)) (matrix place (P.broadcastMatrix root r G h))

private theorem reindex_sum {J : Type} [Fintype J] {u v : Widths S} {old new : J→Widths S}
    (input : u=v) (output : ∀j,old j=new j)
    (m : ∀j,SiteMatrix (State u) (State (old j)) F) (n : ∀j,SiteMatrix (State v) (State (new j)) F)
    (same : ∀j,HEq (m j) (n j))
    (law : ∀x,(raw F u).coeff x=∑j,SiteMatrix.act (m j) (raw F (old j)).coeff x)
    (x : ∀s,State v s) :
    (raw F v).coeff x=∑j,SiteMatrix.act (n j) (raw F (new j)).coeff x := by
  subst v
  have eqn := funext output
  subst new
  have mat : m=n := funext fun j=>eq_of_heq (same j)
  subst n
  exact law x

theorem packetMatrix_action (root : Fin k) (r : ℕ) (G : PortGraph (Fin k) B) (conn : BroadcastConnected G)
    (x : ∀s,State (optionWidths (fun a=>physicalChord place (edge (req a))) (fun _=>r*P.width)) s) :
    (raw F _).coeff x=∑h,SiteMatrix.act (packetMatrix P place root r G h) (raw F _).coeff x := by
  exact reindex_sum (packet_input P place root r) (packet_output P place root r G)
    (fun h=>matrix place (P.broadcastMatrix root r G h)) (packetMatrix P place root r G)
    (fun _=>(cast_heq _ _).symm)
    (place_sum place (P.broadcastMatrix root r G) (P.broadcastMatrix_action root r G conn)) x

end Hierarchy.WireTelescope.PhysicalMatrix

end
end OAI
