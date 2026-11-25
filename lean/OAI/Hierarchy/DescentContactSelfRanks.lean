import OAI.Hierarchy.DescentContactPeerAgreement
import OAI.Hierarchy.DescentResetPeerJointAuxValues

namespace OAI
/-! Both auxiliary predecessor-relative self digits on the dense reset directory. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup
open DescentResetOriginHaloRAM DescentGroupPeerOrder DescentSortedRoster DescentResetStemCompactOrder
open DescentContactCoordinateJoint DescentResetPeerJointRAM DescentCommonHost DescentResetWindowResidentSources
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ} {input : Reached W G q ε S k i z D w hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8000
set_option maxHeartbeats 900000
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "width" => (DescentDenseHostOrder.roster (Z).graph r Ht).card
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "used" => Fintype.card B.next.V
variable {H O ww b : ℕ} (old : Fintype.card input.V≤O) (live : used≤H)
local notation "host" => input.vertex.trans (Fin.castLEEmb old)
local notation "vertex" => B.frame.host.symm.toEmbedding.trans host
local notation "raw" => (Z).rawHostRank T vertex
local notation "dense" => compactActorOrder B old
local notation "names" => compactActorName B old
local notation "adj" => DescentPacking.PackedMatch.Local.Stage.hostRotor host (hostRoster A ((host).trans Fin.valEmbedding))
local notation "P₀" => O*width

theorem current_self_words (near : Fin P₀→Fin 3→Option (Fin P₀)) (u : Host) :
    let key:=(dense u.1.2).castLE live
    let vals:=DescentResetPeerJointPacked.Aux.value width names adj near key
    vals 0=haloNumber B u (receiverRoot B u).1+1 ∧
    vals 1=jointNumber B u (receiverRoot B u).1 (relativeShape B u):=by
  intro key vals
  let origin:=host (B.frame.host.symm (receiverRoot B u).1)
  have back : names ⟨key.val,(dense u.1.2).isLt⟩=raw u.1.2:=by
    change raw ((dense).symm ((dense) u.1.2))=_
    simp
  have home : (names ⟨key.val,(dense u.1.2).isLt⟩).val/width=origin.val:=by
    rw [back]
    exact (compact_host_fields B old _).2
  have inside : (names ⟨key.val,(dense u.1.2).isLt⟩).val/width<O:=by
    rw [home];exact origin.isLt
  have own : (⟨_,inside⟩ : Fin O)=origin:=Fin.ext home
  have measured:=measured_halo (A) input.vertex host adj (fun _=>rfl) (old_roster old)
    (B.frame.host.symm (receiverRoot B u).1) (B.frame.host.symm (receiverRoot B u).1)
  have rank : before (closed adj) origin origin=haloNumber B u (receiverRoot B u).1:=
    measured.trans (halo_old_rank B u _).symm
  have shape : (names ⟨key.val,(dense u.1.2).isLt⟩).val%width=relativeShape B u:=by
    rw [back]
    let field := (Z).hostFields T vertex u.1.2
    change (field.2.val+width*field.1.val)%width=relativeShape B u
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt field.2.isLt]
    rfl
  have first:=DescentResetPeerJointPacked.Aux.self_halo width names adj near key (dense u.1.2).isLt inside (hostRotor_distinct (A) host)
  have second:=DescentResetPeerJointPacked.Aux.self_joint width names adj near key (dense u.1.2).isLt inside (hostRotor_distinct (A) host)
  dsimp only at first second
  rw [own,rank] at first second
  rw [shape] at second
  exact ⟨first.trans (Nat.add_comm ..),by simpa [jointNumber,DescentContactCoordinateJoint.number,radix,Nat.mul_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using second⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
