import OAI.Hierarchy.DescentContactJointGeometry
import OAI.Hierarchy.DescentPrivateCandidateShelf
import OAI.Hierarchy.DescentResetPeerActorChart
import OAI.Hierarchy.DescentResetPeerJointRead
import OAI.Hierarchy.DescentGenuineRosterDistinct

namespace OAI
/-! # The four current peer slots and the old signed endpoint use the same code -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup
open DescentResetOriginHaloRAM DescentGroupPeerOrder DescentSortedRoster DescentResetStemCompactOrder
open DescentContactCoordinateJoint DescentResetPeerJointRAM DescentCommonHost
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ} {input : Reached W G q ε S k i z D w hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "width" => (DescentDenseHostOrder.roster (Z).graph r Ht).card
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "used" => Fintype.card B.next.V
variable {H O bits_ : ℕ} (old : Fintype.card input.V≤O) (live : Fintype.card B.next.V ≤ H)
local notation "host" => input.vertex.trans (Fin.castLEEmb old)
local notation "vertex" => B.frame.host.symm.toEmbedding.trans host
local notation "raw" => (Z).rawHostRank T vertex
local notation "dense" => compactActorOrder B old
local notation "names" => compactActorName B old
local notation "adj" => DescentPacking.PackedMatch.Local.Stage.hostRotor host (hostRoster A ((host).trans Fin.valEmbedding))
local notation "rootAt" u => B.frame.host.symm (receiverRoot B u).1
local notation "rawSize" => O*width

include live in
theorem current_peer_word (u v : Host) (now : Fin rawSize→Fin 4→Option (Fin rawSize)) (j : Fin 4)
    (hit : now (raw u.1.2) j=some (raw v.1.2)) (base : ℕ) (src : DescentResetPeerJointRAM.Sources) (m : Memory bits_)
    (room : DescentResetPeerJointRAM.Room src base H rawSize O (A).degree bits_)
    (measured : DescentResetPeerJointRAM.Reads src used names now adj m) :
    (DescentResetPeerJointRAM.phase bits_ base H rawSize O width (A).degree src).image m
      ((jointBank base H rawSize j).base+(dense u.1.2).val)=
      ((if (receiverRoot B v).1∈originDomain B u then jointNumber B u (receiverRoot B v).1 (relativeShape B v) else 0:ℕ):Word bits_):=by
  let loc:=(dense u.1.2).castLE live
  have seen (P : Host) : (raw P.1.2).val/width=(host (rootAt P)).val:=(compact_host_fields B old P.1.2).2
  have sm (P : Host) : (raw P.1.2).val%width=relativeShape B P:=by
    rw [ResetInput.rawHostRank_read (Z) (T) vertex P.1.2]
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ((Z).hostFields T vertex P.1.2).2.isLt]
    rfl
  have back : names ⟨loc.val,(dense u.1.2).isLt⟩=raw u.1.2:=by
    change raw ((dense).symm ((dense) u.1.2))=_
    rw [Equiv.symm_apply_apply]
  have left : (names ⟨loc.val,(dense u.1.2).isLt⟩).val/width<O:=by rw [back,seen];exact (host (rootAt u)).isLt
  have right : (raw v.1.2).val/width<O:=by rw [seen];exact (host (rootAt v)).isLt
  have a : (⟨_,left⟩ : Fin O)=host (rootAt u):= Fin.ext ((congrArg (fun x : Fin rawSize => x.val/width) back).trans (seen u))
  have b : (⟨_,right⟩ : Fin O)=host (rootAt v):=Fin.ext (seen v)
  have compare : host (rootAt v)∈present (closed adj) (host (rootAt u)) ↔ (receiverRoot B v).1∈originDomain B u:=by
    have eqn:=closed_old_set (A) input.vertex host adj (fun _=>rfl) (old_roster old) (rootAt u)
    rw [←halo_old_set B u] at eqn
    have image_eq : (host (rootAt v)).val∈(present (closed adj) (host (rootAt u))).map Fin.valEmbedding ↔
        host (rootAt v)∈present (closed adj) (host (rootAt u)):=by
      constructor
      · intro entered
        obtain ⟨x,hx,eqn⟩:=Finset.mem_map.mp entered
        exact (show x=host (rootAt v) from Fin.ext eqn) ▸ hx
      · exact fun hx=>Finset.mem_map.mpr ⟨_,hx,rfl⟩
    rw [eqn] at image_eq
    rw [←image_eq,show (host (rootAt v)).val=(T).columns.host (receiverRoot B v).1 from (halo_host B _).symm]
    change (_∈(originDomain B u).image (T).columns.host) ↔ _
    constructor
    · intro x
      obtain ⟨y,mem,eqn⟩:=Finset.mem_image.mp x
      have inj : Function.Injective (T).columns.host:=by
        intro z y h
        apply B.frame.host.symm.injective
        apply input.vertex.injective
        exact Fin.ext (by rwa [halo_host B z,halo_host B y] at h)
      exact (inj eqn) ▸ mem
    · exact Finset.mem_image_of_mem _
  have ord := measured_halo (A) input.vertex host adj (fun _=>rfl) (old_roster old) (rootAt u) (rootAt v)
  rw [←halo_old_rank B u (receiverRoot B v).1] at ord
  have calc_:=DescentResetPeerJointRAM.value_named («width»:=width) adj names now loc j (dense u.1.2).isLt
      (raw v.1.2) (by simpa only [back] using hit) left right (hostRotor_distinct (A) host)
  simp only [a,b,sm,compare,ord] at calc_
  have real:=DescentResetPeerJointRAM.read base width used src names now adj m live room measured loc j
  apply real.trans
  congr 1
  simpa [jointNumber,number,DescentResetPeerJointRAM.radix,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm] using calc_

/-- Two nonempty codes select the same old root and the identical current shape. -/
theorem current_joint_eq (u : Host) (a b : (Z).V) (i j : ℕ) (ha : a∈originDomain B u) (hb : b∈originDomain B u) :
    jointNumber B u a i=jointNumber B u b j ↔ a=b ∧ i=j:=by
  rw [jointNumber,jointNumber,number_inj (halo_radix B u a ha) (halo_radix B u b hb)]
  have cmp:=compress_eq (haloNumbers B u) (Finset.mem_image_of_mem _ ha) (Finset.mem_image_of_mem _ hb)
  constructor
  · rintro ⟨rfl,h⟩
    have labels:=cmp.mp (Nat.add_right_cancel h)
    rw [halo_host B a,halo_host B b] at labels
    exact ⟨B.frame.host.symm.injective (input.vertex.injective (Fin.ext labels)),rfl⟩
  · rintro ⟨rfl,rfl⟩;exact ⟨rfl,rfl⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
