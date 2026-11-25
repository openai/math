import OAI.Hierarchy.DescentTerminalEmitterInputFrames
import OAI.Hierarchy.DescentTerminalEpochAdmission

namespace OAI
/-! # Reading both authentic admission words after the complete terminal issuer -/
namespace Hierarchy.DescentTerminalEmitter
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentExteriorShelf DescentExterior DescentGL
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (S : Shape) (L : Layout)
local notation "j" => S.plane.headBits
local notation "r" => S.plane.restBits
local notation "e" => S.plane.exteriors
local notation "t" => S.plane.bitLanes
local notation "n" => e*2^(j+r)
local notation "origin" => L.plane.exterior
local notation "flag" => flagAt («j»:=j) («r»:=r) («t»:=t) («e»:=e) origin

theorem accepted {A T : Type} (m : Memory w) (room : Room S L w) (pos : 0<w) (width : 2^j*t≤w)
    (seed : ℕ) (lo : BeforeKey S L seed) (hi : AfterFlights S L seed) (fl : AfterFlights S L flag)
    (record : Fin e→Plane j r→Fin t→Bool) (layouts : T→Fin e→DescentGL.Layout (j+(j+r)))
    (decode : (A→Bool)→Option T) (z : A⊕Hidden e j r t→Bool)
    (previous : m seed=0 ↔ ∃choice,decode (z∘Sum.inl)=some choice)
    (inputs : ∀choice,decode (z∘Sum.inl)=some choice→Loaded origin (layouts choice) record (z∘Sum.inr) m) :
    (result S L m seed=0 ∧ result S L m flag=0) ↔ ∃choice,proposed decode layouts record z=some choice := by
  have seed_read := printed_before S L m room lo hi
  have flag_read := after_flights S L m room fl
  exact (and_congr (Iff.of_eq (congrArg (fun x : Word w => x=0) seed_read))
      (Iff.of_eq (congrArg (fun x : Word w => x=0) flag_read))).trans
    (both_flags origin pos width room.plane.frame record layouts decode z m (m seed) previous inputs)

end
end Hierarchy.DescentTerminalEmitter

end OAI
