import OAI.Hierarchy.DescentResetOriginalScalarValues
import OAI.Hierarchy.DescentContactSelfRanks
import OAI.Hierarchy.DescentResetTrunkCompactSuffix

namespace OAI
/-! # The decoded self and palette digits at each occupied compact rack row -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentDenseHostOrder DescentSIMDLookup DescentSharedCableNames
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentResetPeerJointRAM
open DescentResetPeerJointPacked DescentResetStemCompactOrder DescentSortedRoster DescentResetOriginHaloRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
    {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) {H O haloBits shortBits : ℕ}
    (previous : Fintype.card input.V ≤ O) (next : Fintype.card B.next.V ≤ H)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "width" => (DescentDenseHostOrder.roster (Z).graph ((Z).k-(T).commonDepth) (GroupStage.depthBound D n f g)).card
local notation "hosts" => input.vertex.trans (Fin.castLEEmb previous)
local notation "old" => hostRotor hosts (hostRoster A ((hosts).trans Fin.valEmbedding))
local notation "names" => compactActorName B previous
local notation "dense" => compactActorOrder B previous
local notation "raw_" => (Z).rawHostRank T vertex
local notation "rear" => (Z).rawHostRank T ((vertex).trans (Fin.castLEEmb previous))

include next in
/-- Both projections use the original compact-to-raw directory and old host roster.
The old-root ordinal is the rank of the receiver in its closed predecessor neighborhood. -/
theorem original_number_self_shape (near : Fin (O*width)→Fin 3→Option (Fin (O*width)))
    (haloRoom : (A).degree < 2^haloBits) (shapeRoom : width ≤ 2^shortBits)
    (v : Fin H) (actor : B.next.V) (atRack : originalTrunkRack B v=some actor)
    (group : Fin (S.groupCount (i+1))) (x : Block k) :
    ((Aux.value width names old near v 0-1:ℕ):Cell haloBits).val=
      haloNumber B ((group,actor),x) (receiverRoot B ((group,actor),x)).1 ∧
    ((Aux.value width names old near v 1/radix (A).degree:ℕ):Cell shortBits).val=
      ((raw_) actor).val%width := by
  obtain rfl := (original_rack_order B previous next).2 v actor atRack
  let u := ((group,actor),x)
  let home:=B.frame.host.symm (receiverRoot B u).1
  have nameAt : names ((dense) actor)=(rear) actor := by
    change (rear) ((dense).symm ((dense) actor))=(rear) actor
    rw [Equiv.symm_apply_apply]
  have parent : (names ((dense) actor)).val/width=((hosts) home).val :=
    (congrArg (fun z : Fin (O*width)=>z.val/width) nameAt).trans (compact_host_fields B previous actor).2
  have inside : (names ((dense) actor)).val/width < O :=parent.trans_lt ((hosts) home).isLt
  have distinct:=hostRotor_distinct A hosts
  have logical := measured_halo A input.vertex hosts old (fun _=>rfl) (old_roster previous) home home
  have read:=Aux.original_halo_digit width names old near (((dense) actor).castLE next)
    ((dense) actor).isLt inside distinct haloBits haloRoom
  have projected:=Aux.original_shape_digit width names old near (((dense) actor).castLE next)
    ((dense) actor).isLt inside distinct shortBits
    ((Nat.zero_le _).trans_lt ((Z).hostFields T ((vertex).trans (Fin.castLEEmb previous)) actor).2.isLt) shapeRoom
  have same : (⟨_,inside⟩ : Fin O)=(hosts) home:=Fin.ext parent
  constructor
  · have move := congrArg (fun index : Fin O =>
      DescentSortedRoster.before (closed old) index index) same
    exact read.trans (move.trans (logical.trans (halo_old_rank B u _).symm))
  · exact projected.trans ((congrArg (fun z : Fin (O*width)=>z.val%width) nameAt).trans
      (compact_host_fields B previous actor).1)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
