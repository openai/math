import OAI.Hierarchy.DescentContactPeerAgreement
import OAI.Hierarchy.DescentResetJoinedClass
import OAI.Hierarchy.DescentPrivateCandidateShelf

namespace OAI
/-! # The joined five physical digits recover the rank of the actual local source -/
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
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "width" => (DescentDenseHostOrder.roster (Z).graph r Ht).card
local notation "Host" => DescentSharedCableNames.Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "used" => Fintype.card B.next.V
variable {H O ww b : ℕ} (old : Fintype.card input.V≤O) (live : used≤H)
local notation "host" => input.vertex.trans (Fin.castLEEmb old)
local notation "vertex" => B.frame.host.symm.toEmbedding.trans host
local notation "raw" => (Z).rawHostRank T vertex
local notation "dense" => compactActorOrder B old
local notation "names" => compactActorName B old
local notation "adj" => DescentPacking.PackedMatch.Local.Stage.hostRotor host (hostRoster A ((host).trans Fin.valEmbedding))
local notation "P₀" => O*width

private theorem joint_host (u p v : Host) (hp : (receiverRoot B p).1∈originDomain B u)
    (hv : (receiverRoot B v).1∈originDomain B u) :
    jointNumber B u (receiverRoot B p).1 (relativeShape B p)=jointNumber B u (receiverRoot B v).1 (relativeShape B v) ↔ p.1.2=v.1.2:=by
  rw [current_joint_eq B u _ _ _ _ hp hv]
  constructor
  · rintro ⟨roots,shapes⟩
    apply ((Z).hostFields T (B.frame.host.symm.toEmbedding.trans input.vertex)).injective
    exact Prod.ext (congrArg (B.frame.host.symm.toEmbedding.trans input.vertex) roots) (Fin.ext shapes)
  · intro same
    exact ⟨congrArg (fun t:B.next.V=>position (Z).graph t.val) same,
      congrArg (fun t:B.next.V=>((Z).hostFields T (B.frame.host.symm.toEmbedding.trans input.vertex) t).2.val) same⟩

include live in
theorem current_rank (u v : Host) (physical : Fin 5→Cell b) (small : 4≤2^b)
    (rows : Fin P₀→Fin 4→Option (Fin P₀)) (base : ℕ) (src : DescentResetPeerJointRAM.Sources) (m : Memory ww)
    (room : DescentResetPeerJointRAM.Room src base H P₀ O (A).degree ww)
    (stored : DescentResetPeerJointRAM.Reads src used names (indexed rows) adj m)
    (jointRoom : width*radix (A).degree≤2^ww)
    (peers : present rows (raw u.1.2)=(insert u.1.2 (B.next.placement.near u.1.2)).map raw)
    (member : v∈sources B.next.placement u) (reachable : (receiverRoot B v).1∈originDomain B u)
    (requested : (physical 4).val=jointNumber B u (receiverRoot B v).1 (relativeShape B v))
    (read : ∀j : Fin 4,(physical j.castSucc).val=
      ((DescentResetPeerJointRAM.phase ww base H P₀ O width (A).degree src).image m
        ((jointBank base H P₀ j).base+(dense u.1.2).val)).val) :
    (DescentResetJoinedRank.rank physical).val=localClass B u v:=by
  have valid : v.1.2∈insert u.1.2 (B.next.placement.near u.1.2):=by
    rw [sources_as_map] at member
    obtain ⟨x,hx,rfl⟩:=Finset.mem_map.mp member
    exact hx
  have yes : raw v.1.2∈present rows (raw u.1.2):=by rw [peers];exact Finset.mem_map.mpr ⟨_,valid,rfl⟩
  have pos : physical 4≠0:=by
    intro zero;rw [zero] at requested
    simp only [jointNumber,DescentContactCoordinateJoint.number, Fin.val_zero] at requested
    omega
  have lim (t : Host) (touched : (receiverRoot B t).1∈originDomain B u) :
      jointNumber B u (receiverRoot B t).1 (relativeShape B t)<2^ww:=by
    have shapeLt : relativeShape B t<width:=((Z).hostFields T (B.frame.host.symm.toEmbedding.trans input.vertex) t.1.2).2.isLt
    have digitLt:=halo_radix B u _ touched
    exact (Nat.add_lt_add_left digitLt _).trans_le (by
      rw [←Nat.mul_succ]
      exact (Nat.mul_le_mul_left _ shapeLt).trans (by simpa [DescentResetPeerJointRAM.radix,Nat.mul_comm] using jointRoom))
  have readAt (j : Fin 4) : physical j.castSucc=physical 4 ↔ indexed rows (raw u.1.2) j=some (raw v.1.2):=by
    cases expected : indexed rows (raw u.1.2) j with
    | none=>
      have atU : names ((dense u.1.2))=raw u.1.2:=by change raw ((dense).symm ((dense) u.1.2))=_;simp
      have empty:=DescentResetPeerJointRAM.read base width used src names (indexed rows) adj m live room stored ((dense u.1.2).castLE live) j
      have absent:=DescentResetPeerJointRAM.value_absent («width»:=width) adj names (indexed rows) ((dense u.1.2).castLE live) j
        (dense u.1.2).isLt ((congrArg (fun z => indexed rows z j) atU).trans expected)
      rw [absent] at empty
      have nil : physical j.castSucc=0:=Fin.ext ((read j).trans (congrArg Fin.val empty))
      simp [nil,Ne.symm pos]
    | some out=>
      have entered:=((indexed_iff rows _ j out).mp expected).1
      rw [peers] at entered
      obtain ⟨x,_,rfl⟩:=Finset.mem_map.mp entered
      let t:=hostAt u x
      have got:=current_peer_word B old live u t (indexed rows) j expected base src m room stored
      have readVal:=(read j).trans (congrArg Fin.val got)
      by_cases touches : (receiverRoot B t).1∈originDomain B u
      · rw [ite_eq_left touches,Fin.val_cast_of_lt (lim _ touches)] at readVal
        rw [←Fin.val_inj,readVal,requested,joint_host B u t v touches reachable,Option.some.injEq]
        exact (raw).injective.eq_iff.symm
      · rw [ite_eq_right touches] at readVal
        have nil : physical j.castSucc=0:=Fin.ext readVal
        have different : x≠v.1.2:=by
          intro same
          apply touches
          simpa only [show (receiverRoot B t).1=(receiverRoot B v).1 from congrArg (fun t:B.next.V=>position (Z).graph t.val) same] using reachable
        have diff : raw x ≠ raw v.1.2 := fun eqn => different ((raw).injective eqn)
        simp [nil,Ne.symm pos,diff]
  exact (DescentResetJoinedRank.rank_read rows _ _ physical small yes pos readAt).trans
    ((DescentResetSourceClassRAM.local_class raw _ v.1.2 rows (raw u.1.2) peers).trans (class_host B u v member).symm)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
