import OAI.Hierarchy.DescentOrdinaryRosterRead

namespace OAI
/-! Successive original measured host rotors use one physical layout. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage
open DescentCompiler DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentOrdinaryPeerRows DescentOrdinaryPeerSlots DescentOrdinaryPeerLifts DescentTenHopRoster
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {q ε u : ℝ} {S : AtomSchedule}
  {W : MarkedWorld F d P bits} {i z D wire hist z' D' : ℕ}
  {source : Reached W G q ε S k i z D wire hist} {he : 0≤ε}
  {T : StageInput W G u ε} {p : (T.result he).Choice} {n : Normalize ((T.result he).state p)}
  {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
  (ticket : OrdinaryLink source he T p n target)
local notation "slots" => 2^packExponent 20 source.placement.degree+2
local notation "width" => (2^(k+1)-1)*slots
local notation "window" => gap source.placement.degree+gainExponent 20 source.placement.degree
local notation "shapes" => shapeSet window k slots
local notation "E" => target.placement.degree
local notation "N" => Fintype.card source.V
local notation "N₁" => Fintype.card target.V

include ticket in
theorem OrdinaryLink.issued_hostRotor {w H R : ℕ} (base : ℕ) (count old : Bank) (m : Memory w)
    (lo : N≤H) (hi : N₁≤R) (cf : count.Fits w base) (sf : old.Fits w base)
    (cap : H*source.placement.degree≤old.size)
    (safe : DescentOrdinaryPeerCount.roof base H source.placement.degree R E<2^w)
    (measured : m count.base=(N:Word w))
    (prior : ∀h j,m (old.base+h.val*source.placement.degree+j.val)=
      (((hostRotor (source.vertex.trans (Fin.castLEEmb lo)) (hostRoster source.placement (source.vertex.trans Fin.valEmbedding))
        h j).elim H Fin.val : ℕ) : Word w)) :
    let deg:=source.placement.degree
    let a:=DescentOrdinaryPeerCount.program w base H deg R E count old shapes
    a.Runs m ∧ (∀x,x<base ∨ DescentOrdinaryPeerCount.roof base H deg R E≤x→a.image m x=m x) ∧
      a.image m (DescentOrdinaryPeerCount.newCount base H deg R E).base=(N₁:Word w) ∧
      ∀h j,a.image m ((peers base H deg R E).base+h.val*E+j.val)=
      (((hostRotor (target.vertex.trans (Fin.castLEEmb hi)) (hostRoster target.placement (target.vertex.trans Fin.valEmbedding))
        h j).elim R Fin.val : ℕ) : Word w) := by
  let sender:=source.vertex.trans (Fin.castLEEmb lo)
  let rs:=hostRotor sender (hostRoster source.placement (source.vertex.trans Fin.valEmbedding))
  have supports (v : source.V) (z : Fin H) : (∃j,rs (sender v) j=some z) ↔ ∃u∈source.placement.near v,sender u=z :=
    original_hostRotor_rows source.placement sender v z
  have issued:=ticket.issued_peers base count old rs m lo hi cf sf cap safe measured prior supports
  refine ⟨issued.1,issued.2.1,issued.2.2.1,?_⟩
  intro h j
  have cast_choice := apply_dite (fun x : ℕ => (x : Word w))
    (∃v, (target.vertex v).val = h.val)
    (fun yes => ordinalPeer ((target.placement.mutual yes.choose).map
      (target.vertex.trans Fin.valEmbedding)) R j.val) (fun _ => R)
  exact (issued.2.2.2 h j).trans (cast_choice.symm.trans (congrArg (fun x : ℕ => (x : Word w))
    (genuine_hostRotor target.placement (target.vertex.trans (Fin.castLEEmb hi)) h j)))

end
end Hierarchy.DescentSixParty.Chronology

end OAI
