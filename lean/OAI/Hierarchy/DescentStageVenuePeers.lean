import OAI.Hierarchy.DescentVenueRosterDefinition
import OAI.Hierarchy.DescentOrdinaryRosterTransfer
import OAI.Hierarchy.DescentDatedStageVenue

namespace OAI
/-! # Induction of the actual geometric peer roster across a named ordinary date -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage
open DescentHostDegree DescentHostDirectory DescentOrdinaryPeerRows
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P:Type} [Field F] {d k:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits}
  {G:PoweredGadget F} {q ε u:ℝ} {S:AtomSchedule} {age z D wire hist z' D' H R w:ℕ}
  (r:Reached W G q ε S k age z D wire hist)

theorem Reached.venueRoster_rows (wide:Fintype.card r.V≤H)(v:r.V)(peer:Fin H):
    (∃j,r.venueRoster wide ((r.vertex v).castLE wide) j=some peer) ↔
      ∃u∈r.placement.near v,(r.vertex u).castLE wide=peer:=by
  change _ ↔ ∃ u ∈ r.placement.near v, (r.vertex.trans (Fin.castLEEmb wide)) u = peer
  rw [←Chronology.original_hostRotor_rows r.placement (r.vertex.trans (Fin.castLEEmb wide)) v peer]
  constructor
  · rintro ⟨j,ok⟩;exact ⟨Fin.cast r.branch.symm j,ok⟩
  · rintro ⟨j, ok⟩
    refine ⟨Fin.cast r.branch j, ?_⟩
    unfold venueRoster
    rw [Fin.cast_cast, Fin.cast_refl]
    exact ok

theorem Reached.venueRoster_missing (wide:Fintype.card r.V≤H)(h:Fin H)
    (missing:¬∃u,(r.vertex u).castLE wide=h)(j:Fin D):r.venueRoster wide h j=none:=by
  change ¬ ∃ u, (r.vertex.trans (Fin.castLEEmb wide)) u = h at missing
  simp only [venueRoster, hostRotor, dite_eq_right missing]

theorem Reached.roster_read (wide:Fintype.card r.V≤H) (input:Dated.Operands) {M precision floor:ℕ} {m:Memory w}
    (mounted:stageVenue r wide input M precision floor (r.venueRoster wide) m)
    (h:Fin H)(j:Fin r.placement.degree):
    m (input.roster.base+h.val*r.placement.degree+j.val)=
      (((hostRotor (r.vertex.trans (Fin.castLEEmb wide)) (hostRoster r.placement (r.vertex.trans Fin.valEmbedding)) h j).elim H Fin.val : ℕ) : Word w):=by
  have original:=mounted.2.1.roster h (Fin.cast r.branch j)
  simpa only [r.branch, Dated.Operands.ports, DescentPackedColony.target, Reached.venueRoster, Fin.val_cast, Fin.cast_cast, Fin.cast_refl, id_eq, Nat.add_assoc] using original

namespace Chronology
variable {source:Reached W G q ε S k age z D wire hist} {he:0≤ε} {T:StageInput W G u ε}
  {p:(T.result he).Choice} {n:Normalize ((T.result he).state p)}
  {target:Reached n.result G q ε S k (age+1) z' D' wire hist}
  (ticket:OrdinaryLink source he T p n target)
local notation "slots" => 2^packExponent 20 source.placement.degree+2
local notation "shapes" => shapeSet (gap source.placement.degree+gainExponent 20 source.placement.degree) k slots
local notation "N" => Fintype.card source.V
local notation "N₁" => Fintype.card target.V
local notation "E" => target.placement.degree

include ticket in
theorem OrdinaryLink.venue_peers (base:ℕ)(input:Dated.Operands)(count:Bank)(m:Memory w)
    (lo:N≤H)(hi:N₁≤R) {M precision floor:ℕ}
    (mounted:stageVenue source lo input M precision floor (source.venueRoster lo) m)
    (prior:floor≤base) (countRoom:count.Fits w base)(measured:m count.base=(N:Word w))
    (room:DescentOrdinaryPeerCount.roof base H D R D'<2^w):
    let a:=DescentOrdinaryPeerCount.program w base H source.placement.degree R E count input.roster shapes
    a.Runs m ∧ (∀x,x<base ∨ DescentOrdinaryPeerCount.roof base H D R D'≤x→a.image m x=m x) ∧
    a.image m (DescentOrdinaryPeerCount.newCount base H D R D').base=(N₁:Word w) ∧
    ∀h j,a.image m ((peers base H D R D').base+h.val*D'+j.val)=(((target.venueRoster hi h j).elim R Fin.val : ℕ) : Word w):=by
  dsimp only
  have acc:=mounted.1
  have oldFits:input.roster.Fits w base:=⟨acc.roster.1,acc.roster.2.1,acc.roster.2.2.trans prior⟩
  have records:=ticket.issued_hostRotor base count input.roster m lo hi countRoom oldFits
    (by simpa only [source.branch, Dated.Operands.ports] using acc.rosterRoom)
    (by simpa only [source.branch,target.branch] using room) measured (source.roster_read lo input mounted)
  refine ⟨records.1,?_,?_,?_⟩
  · simpa only [source.branch,target.branch] using records.2.1
  · simpa only [source.branch,target.branch] using records.2.2.1
  · intro h j
    have found:=records.2.2.2 h (Fin.cast target.branch.symm j)
    simpa only [source.branch,target.branch,Fin.val_cast,Reached.venueRoster] using found

end Chronology
end
end Hierarchy.DescentSixParty

end OAI
