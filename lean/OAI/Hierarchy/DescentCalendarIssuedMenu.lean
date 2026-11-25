import OAI.Hierarchy.DescentCalendarCandidateCapture

namespace OAI
/-! Ascertain the joint registers of the actual candidate menu from the reached actor directory and original raw peer slots. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetNewActorDirectory DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option hygiene false
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "H" => S.hostSize i
local notation "J" => 2^(T).commonDepth
local notation "r" => (Z).k-(T).commonDepth
local notation "ht" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r ht).card
local notation "gs" => S.groupCount (i+1)
local notation "cap₀" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(ht+1))
local notation "oldWidth" => DescentPackedPrivateMenu.fieldBits (Z).graph r ht (2^r*(2*(A).cap))
    (DescentRecordedRotorLayers.width f (A).cap) C (Z).width
variable (oldBatch batch : ℕ) (calendar : List ℕ) (paid : (A).cap=(calendar.take i).prod*256)
local notation "cap" => (calendar.take i).prod*256
local notation "field₀" => ResetMiddle.fieldWidth D cap n k ht
local notation "table₀" => CandidateSheets.fromBoard S ctl.board k tail i D f g cap batch
local notation "meta₀" => (table₀).metaBits
local notation "month" => CandidateFront.menu S ctl.board k tail i D f g oldBatch batch C ctl.bitsR calendar
local notation "good" => contactOutputs B H oldBatch field₀ (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) gs (2^k)
    batch (month).contact.outputBits meta₀
local notation "deck" => privateProjection («H»:=H) (field:=oldWidth) B oldBatch batch meta₀
variable {date : PhysicalReset} {floor bw : ℕ} (I : date.DateInputs floor bw)
local notation "v₀" => date.successor
local notation "base₀" => date.rebased floor
local notation "phys₀" => (v₀).front
local notation "peer₀" => (phys₀).peer
local notation "pitch₀" => (phys₀).contactLayout ((v₀).actorEnd base₀)
local notation "Q₀" => (v₀).privateShape
local notation "K₀" => (v₀).contactShape
local notation "don₀" => (phys₀).donorStart ((v₀).actorEnd base₀)
local notation "used" => Fintype.card B.next.V
local notation "rawSize" => H*shelf
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "K" => 2*(A).cap
local notation "F₀" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r
variable (cal : MixedGeometry B oldBatch batch calendar v₀ base₀) (pad : Fintype.card input.V≤H)
local notation "portChart" => input.vertex.trans (Fin.castLEEmb pad)
local notation "adj_" => hostRotor portChart (hostRoster (A) ((portChart).trans Fin.valEmbedding))
variable {keyBits : ℕ} (prior : PriorPeerWords B H oldWidth keyBits)
    (xs : Fin H→Fin J→Fin F₀→Cell field₀) (raw : Fin L→Fin K→Fin H→Fin J→Cell field₀)
    (near : Fin rawSize→Fin 3→Option (Fin rawSize))

local notation "measured" => measured_menu B oldBatch batch calendar I cal pad prior xs raw near
local notation "oldScene" => (v₀).issuedScene base₀ I.earlier
local notation "start₀" => (v₀).actorEnd base₀
local notation "pre₀" m => (phys₀).preScalar start₀ oldScene I.sceneFits m
local notation "look₀" => (v₀).jointRegisters base₀ I.earlier
local notation "trunk₀" m => ((phys₀).trunkScene start₀ oldScene I.sceneFits).image m


variable (floor₀ : ℕ) (src : Bank) (before : Memory bw)
local notation "dir₀" => (⟨floor₀,H,shelf,chunks J oldBatch⟩ : DescentResetNewActorDirectory.Layout)
local notation "entered" => (dir₀).result src before
local notation "ports_" => I.earlier.oldRoster
local notation "name_" => (Z).rawHostRank (T) ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb pad))

/-- Reach the *same* measured sources used by `capture_menu` after the real preceding actor run.
The input old roster is the original old high-degree roster and the three raw current peers are the
socket probe's output, including ghost rows. -/
theorem capture_registers
    (grid : (v₀).actor.directory ((v₀).middle.stop base₀)=dir₀)
    (oldPos : 0<oldBatch) (oldBits : oldBatch≤bw)
    (actor : ∀l (p : Row H J oldBatch),before (src.base+l.val*(H*chunks J oldBatch)+(row H J oldBatch p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B pad) l) p).val:Word bw))
    (srcFits : src.Fits bw floor₀) (srcSize : rawSize*chunks J oldBatch≤ src.size)
    (chunksWide : chunks J oldBatch≤2^bw) (space : (dir₀).endAddress<2^bw)
    (oldFits : (ports_).Fits bw floor₀) (oldSize : H*(A).degree≤(ports_).size)
    (oldRead : ∀a j,before ((ports_).base+(a.val*(A).degree+j.val))=(DescentPackedColony.target (adj_ a j):Word bw))
    (found : ∀a j,(pre₀ entered) (((v₀).initialPeers base₀).base+j.val*rawSize+a.val)=(DescentPackedColony.target (near a j):Word bw)) :
    DescentResetPeerJointRAM.Reads look₀ used (measured).names (measured).now (measured).prior (pre₀ entered) ∧
      ∀h j,(pre₀ entered) (((v₀).initialPeers base₀).base+(j:Fin 3).val*(peer₀).hosts+(h:Fin (peer₀).hosts).val)=
        ((((measured).near h j).elim (peer₀).hosts Fin.val : ℕ) : Word bw) :=by
  have cutEq : start₀=(dir₀).endAddress:=congrArg DescentResetNewActorDirectory.Layout.endAddress grid
  have countBank : (look₀).count=(dir₀).count:=congrArg DescentResetNewActorDirectory.Layout.count grid
  have invBank : (look₀).inverse=(dir₀).inverse:=congrArg DescentResetNewActorDirectory.Layout.inverse grid
  obtain ⟨_,count,entries,_,_,held⟩:=paid_actor_result B pad floor₀ src before oldPos oldBits actor srcFits srcSize chunksWide space
  have occupied : used≤rawSize := by
    let names : B.next.V ↪ Fin rawSize := name_
    exact (Fintype.card_le_of_embedding names).trans_eq (Fintype.card_fin _)
  have «until» : floor₀≤ start₀:=by rw [cutEq];exact Nat.le_add_right ..
  have bounds:=(dir₀).fits space
  have clock : (peer₀).oldDegree=(A).degree:=cal.oldDegree
  have earlier : (peer₀).oldHosts*(peer₀).oldDegree≤(ports_).size:=by simpa only [cal.oldCount,clock] using oldSize
  apply (v₀).original_joint_reads base₀ I.earlier I.sceneFits entered (measured).names (measured).near (measured).prior
  · intro a j
    have hit:=found (a.cast cal.peerSlots) j
    change _=(DescentPackedColony.target ((near (a.cast cal.peerSlots) j).map (Fin.cast cal.peerSlots.symm)):Word bw)
    cases e:near (a.cast cal.peerSlots) j with
    | none=>simpa only [e,Option.map_none,DescentPackedColony.target,Option.elim_none,Fin.val_cast,cal.peerSlots] using hit
    | some v=>simpa only [e,Option.map_some,DescentPackedColony.target,Option.elim_some,Fin.val_cast,cal.peerSlots] using hit
  · rw [countBank];exact count
  · intro j
    have datum:=entries ((compactActorOrder B pad).symm j)
    change entered ((dir₀).inverse.base+((compactActorOrder B pad) ((compactActorOrder B pad).symm j)).val)=
      (((name_) ((compactActorOrder B pad).symm j)).val:Word bw) at datum
    rw [invBank]
    simpa only [measured_menu,compactActorName,Fin.val_cast,Equiv.apply_symm_apply] using datum
  · rw [invBank];exact occupied.trans (dir₀).ordered.1
  · intro a j
    have pos : a.val*(peer₀).oldDegree+j.val < (peer₀).oldHosts*(peer₀).oldDegree:=
      (Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ a.isLt)
    refine (held ((ports_).base + (a.val*(peer₀).oldDegree+j.val))
      (.inl ((Nat.add_lt_add_left (pos.trans_le earlier) _).trans_le oldFits.2.2))).trans ?_
    change before ((ports_).base+(a.val*(peer₀).oldDegree+j.val))=
      (DescentPackedColony.target ((adj_ (a.cast cal.oldCount) (j.cast clock)).map (Fin.cast cal.oldCount.symm)):Word bw)
    have old:=oldRead (a.cast cal.oldCount) (j.cast clock)
    cases e:adj_ (a.cast cal.oldCount) (j.cast clock) with
    | none=>simpa only [e,Option.map_none,DescentPackedColony.target,Option.elim_none,Fin.val_cast,cal.oldCount,clock] using old
    | some v=>simpa only [e,Option.map_some,DescentPackedColony.target,Option.elim_some,Fin.val_cast,cal.oldCount,clock] using old
  · rw [countBank,cutEq];exact bounds.2.2.2.1
  · rw [invBank,cutEq];exact bounds.2.2.2.2
  · exact ⟨oldFits.1,oldFits.2.1,oldFits.2.2.trans «until»⟩
  · exact earlier

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
