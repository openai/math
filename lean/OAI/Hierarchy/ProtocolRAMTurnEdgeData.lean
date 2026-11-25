import OAI.Hierarchy.ProtocolRAMTurnGeometry
import OAI.Hierarchy.TaggedWireCoreVisits
import OAI.Hierarchy.TaggedWireRowGraph

namespace OAI
/-! # The literal paid-edge words and unreversed visit dictionary of a mounted board -/

noncomputable section
namespace Hierarchy.ProtocolRAMTurnEdges

open AdaptiveProbe ProbeStage CoreBoard WordSeats WireTelescope SettledMatrix VisitOrder
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProtocolRAMTurnGeometry
open scoped Classical

variable {h d k edges K : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {place : Site h d k → Fin K} (B : Mount (S:=S) π place edges)

def walk : ProtocolRAMTurnGeometry.Source edges h d k → List (Fin edges) :=
  Sum.elim (fun e=>[e]) (Sum.elim B.ordinary B.centers)

def visit (_inj : Function.Injective place) (pad : Chord K) : ProtocolRAMTurnGeometry.Source edges h d k → ℕ → ℕ
  | .inl e,j => if j=0 then (filledChord B.actual pad e).1.1.val else (filledChord B.actual pad e).1.2.val
  | .inr (.inl i),j => (place (site π (commodityTurn i j))).val
  | .inr (.inr c),j => (place (site π (reserveTurn c j))).val

def ends (_inj : Function.Injective place) (pad : Chord K) (e : Fin edges) : ℕ×ℕ := ((filledChord B.actual pad e).1.1.val,(filledChord B.actual pad e).1.2.val)

theorem walk_length (s : ProtocolRAMTurnGeometry.Source edges h d k) :
    (walk B s).length=ProtocolRAMTurnGeometry.length s := by
  rcases s with e|i|c
  · rfl
  · exact length_ordinary B i
  · exact length_center B c

end Hierarchy.ProtocolRAMTurnEdges
end

end OAI
