import OAI.Hierarchy.DescentResetStemCalendarJob
import OAI.Hierarchy.DescentPhysicalStemRead
import OAI.Hierarchy.DescentPhysicalStemBankFits

namespace OAI
/-! # The fixed dated front issues the genuine signed stem words on the incoming tape -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical
open scoped Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "groups" => S.groupCount (i+1)
local notation "height" => GroupStage.depthBound D n f g

local notation "A" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "c" => (T).commonDepth
local notation "depth₀" => S.groupWidth k tail i+k
local notation "before" => input.order.trans Fin.valEmbedding
local notation "fits" => B.frame.enough.trans (Nat.sub_le ..)

local notation "Slot" => Fin (2^(depth₀-c))×Fin (2*(A).cap)

open DescentResetFieldAssembler DescentResetWindowResidentSources

open DescentResetStemDecoder DescentRelativeContacts
local notation "Y" => 2^(Z).n
local notation "shapeBits" => (Z).k-c

local notation "shapeCount" => DescentFallbackShapeTable.rows shapeBits Y
local notation "K" => 2*shapeCount

open DescentResetStemPackedIssue DescentResetStemPackedIssue.Mixed
open DescentSIMDLookup DescentResetStemIncidence
local notation "pool" => DescentDenseHostOrder.roster (Z).graph shapeBits height
local notation "rows" => Fintype.card B.next.V

open DescentResetStemPackedIssue.Mixed DescentPackedZip DescentDyadicSpan ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
local notation "L" => 2^(depth₀-c)
local notation "Q" => DescentResetStemPackedIssue.count L (A).cap
local notation "sid" => DescentResetStemPackedIssue.side L (A).cap
local notation "ord" => DescentResetStemPackedIssue.ordinal L (A).cap
local notation "X" => 2^k
local notation "degree" => (A).degree

open DescentGroupPeerOrder DescentGL DescentTreePrefixIntervals DescentPacking.PackedMatch.Local.Stage
open DescentSharedBookScan DescentFallbackPeriod DescentPackedColony
local notation "OldHost" => DescentSharedCableNames.Stage.Host (Fin (S.groupCount i)) input.V k
local notation "beforeRank" => input.vertex.trans Fin.valEmbedding
local notation "groupKey" => Fin.valEmbedding (n:=S.groupCount i)
local notation "donors" => donor digitsIn B.frame.basis fits
local notation "oldNames" => cableNames k (groupRank groupKey beforeRank)
local notation "oldRoster" => hostRoster A beforeRank
local notation "signs" => signedPanel A before S input.valid oldNames

open DescentDatedAddressBook DescentDatedAddressBook.CandidateFront DescentResetStemDateSignature DescentSortedRoster DescentResetPeerUnionRAM
local notation "prev" => S.hostSize i
local notation "HP" => S.hostSize (i+1)
variable (M₀ M field b packet : ℕ) (calendar : List ℕ) (paid : input.placement.cap=(calendar.take i).prod*256)
local notation "cap₁" => (calendar.take i).prod*256
local notation "phys" => setupFront S ctl.board k tail i D f g M₀ M field b C packet calendar
variable (floor : ℕ) (older : EarlierBanks D k ((calendar.take i).prod*256) n) (flags number inverse : Bank)
local notation "oldCode" => calendarOriginals S ctl.board k tail i D f g M₀ M field b C packet calendar floor older
local notation "sc" => (phys).fromOriginals floor oldCode flags number inverse
local notation "reg" => (phys).stemRegisters floor sc older.oldHub
local notation "cut₀" => (phys).parentEnd floor
local notation "pointer" => ((phys).parent floor).base
local notation "window" => calendarWindow B calendar paid older
local notation "jobB" => reachedStemJob B M₀ M field b packet calendar paid floor older flags number inverse
local notation "previous" => input.valid.host
local notation "actorId" => input.vertex.trans (Fin.castLEEmb previous)
local notation "vr" => (vertexCode).trans (Fin.castLEEmb previous)
local notation "pitch" => prev*(pool).card
local notation "rawSeen" => (Z).rawHostRank T (vr)
local notation "compact" => (Z).denseHostRank T (vr)
local notation "hub" => fun z=>input.placement.hub (B.frame.host.symm z)
variable {w₀ t : ℕ}

private theorem accessible_later {D₀ h₀ g₀ M₁ bw lo hi : ℕ} {p : DescentPackedColony.Ports D₀} {x : Bank}
    (h : lo≤ hi) (src : Accessible p x h₀ g₀ M₁ bw lo) : Accessible p x h₀ g₀ M₁ bw hi :=by
  have up (bank : Bank) (fit : bank.Fits bw lo) : bank.Fits bw hi:=⟨fit.1,fit.2.1,fit.2.2.trans h⟩
  exact ⟨fun i=>up _ (src.ids i),src.idsRoom,up _ src.roster,src.rosterRoom,
    up _ src.offsets,src.offRoom,up _ src.chunks,src.chunkRoom,up _ src.source,src.srcRoom⟩

theorem calendar_stem (safe : (phys).SceneRoom floor sc w₀) (m₀ : Memory w₀)
    (value : OldHost→ℕ) (room : ∀u,value u+1<2^field)
    (signBits : DescentSignedCableCodec.width degree (A).cap≤ field)
    (onWire : ∀s (e : Grain A),value (home A (endSite A s e))=signedStemWord B s (home A (endSite A s e)))
    (values : Fin prev→Block c→Fin L→Cell t)
    (roster₀ : Fin prev→Fin degree→Option (Fin prev))
    (chips : Fin prev→Block c→Fin L→Fin (2*(A).cap)→Option (Live degree (A).cap))
    (own : ∀v hi lo,(values (actorId v) hi lo).val=value (donors v hi lo))
    (chart : ∀v j,roster₀ (actorId v) j=(oldRoster v j).map actorId)
    (saved : ∀v hi lo z,chips (actorId v) hi lo z=signs (donors v hi lo) z)
    (fits₀ : ∀j,((window).bank j).Fits w₀ floor) (size : ∀j,prev*chunks (2^c) M₀≤((window).bank j).size)
    (peer : ∀lo,Accessible (window).ports ((window).bank (.inl (1,lo))) prev (2^c) M₀ w₀ floor)
    (stored : Mounted (window).ports roster₀ m₀ (2^c) M₀)
    (local_ : ∀lo,DescentPackedColony.Reads ((window).bank (.inl (0,lo))) (fun v j=>((values v j lo).val:Cell field)) M₀ m₀)
    (tagged : ∀lo,DescentPackedColony.Reads ((window).bank (.inl (1,lo))) (fun v j=>((values v j lo).val+1:Cell field)) M₀ m₀)
    (signed : ∀z lo,DescentPackedColony.Reads ((window).bank (.inr (z,lo)))
      (fun v j=>((DescentSignedCableCodec.encode (chips v j lo z)).val:Cell field)) M₀ m₀)
    (network : Fin (pitch)→Fin 3→Option (Fin (pitch)))
    (counted : m₀ number.base=(rows:Word w₀))
    (inverseRead : ∀u,m₀ (inverse.base+((compact) u).val)=(((rawSeen) u).val:Word w₀))
    (bitmap : ∀j : Fin (pitch),m₀ (flags.base+j.val)=if ∃u,(rawSeen) u=j then 1 else 0)
    (hubRead : ∀u,m₀ (older.oldHub.base+((vr) u).val)=((hub u).toNat:Word w₀))
    (lowCount : number.base< floor) (lowInv : inverse.base+rows≤ floor)
    (lowMask : flags.base+pitch≤ floor) (lowHub : older.oldHub.base+prev≤ floor)
    (neighbors : ∀(i : Fin 3) (j : Fin (pitch)),
      let pt:=(phys).peers floor
      DescentResetPeerUnionRAM.Program.output pt prev (phys).peer.shapes D (phys).peer.bits (phys).peer.evidenceLanes
        (phys).peer.evidenceGroups (sc).peers.old (sc).peers.test (sc).peers.src ((phys).prePeers floor sc safe m₀)
        ((phys).peer.rawPeers pt+i.val*(phys).peer.hosts+j.val)=(target (network j i):Word w₀))
    (inverseSize : rows ≤ inverse.size) (hubSize : prev≤ older.oldHub.size)
    (ha : 0<M₀) (width : (b*7)*M≤ w₀)
    (endRoom : (phys).trunkEnd floor<2^w₀) {p : ℕ} (record : B.Recorded p)
    (four : ∀v,present (selfPeers network) ((rawSeen) v)=(insert v ((Z).emittedNear T v)).map (rawSeen))
    (absence : ∀v,(∀j,network ((rawSeen) v) j≠some ((rawSeen) v)) ↔ v∉(Z).emittedNear T v) :
    ((phys).received floor sc safe).Runs m₀ ∧
      (∀(x : Fin X) s (slot : Slot) (p : Row HP groups M),
        ((phys).received floor sc safe).image m₀ ((phys).stemOutput floor+
          (finProdFinEquiv (x,(ord) (s,slot))).val*(HP*chunks groups M)+(row HP groups M p).val)=
        ((data (fun r g₀=>(originalTrunkRack B r).elim 0 (fun v=>DescentResetFieldAssembler.raw b («meta» B ((g₀,v),x)
          (localOrigin B ((g₀,v),x) (stemIndex B s slot))))) p).val:Word w₀)) ∧
      ((phys).trunkScene floor sc safe).Runs m₀ ∧ ∀(x : Fin X) (j : Fin (stemsCount B)),
        ((phys).stemOperand floor x.val j.val).Fits w₀ ((phys).trunkEnd floor) ∧
          Source ((phys).stemOperand floor x.val j.val)
            (fun (r : Fin HP) g₀=>DescentResetFieldAssembler.raw b (actualMeta B (originalTrunkRack B) x (stemShelf B j) r g₀)) M
            (((phys).trunkScene floor sc safe).image m₀) :=by
  let start:=(phys).stemEntry floor sc safe m₀
  have dates:=calendar_job B M₀ M field b packet calendar paid floor older flags number inverse
  have capacity : rows≤HP:=B.next.valid.host
  obtain ⟨active,measured,blank⟩:=(phys).stem_registers_read floor sc safe (Z) T (vr) m₀ older.oldHub (hub)
    (calendar_palette B).symm capacity network counted inverseRead bitmap hubRead lowCount lowInv lowMask lowHub neighbors
  have prior : floor≤ cut₀:=((phys).floor_before floor sc safe).trans ((phys).front_order floor).1
  have hostFit : pitch<2^w₀:=(Nat.le_add_left (pitch) flags.base).trans_lt
    ((lowMask.trans (prior.trans ((phys).front_order floor).2.1)).trans_lt safe.stems.final)
  have lift (j) : ((window).bank j).Fits w₀ cut₀:=⟨(fits₀ j).1,(fits₀ j).2.1,(fits₀ j).2.2.trans prior⟩
  have beforePeer:= (phys).entry_mounted floor sc safe m₀ (window).ports ((window).bank (.inl (1,0)))
    roster₀ stored (peer 0)
  have limit : (jobB).extent cut₀ pointer<2^w₀:=by
    rw [←dates,(phys).job_extent floor (sc).stems]
    exact safe.stems.final
  have physical : 0<HP→0< pitch :=by
    intro live
    have nextHost : HP=prev*(2^S.hostGain*S.radix) :=by simp [AtomSchedule.hostSize,pow_succ,Nat.mul_assoc]
    have usable : 0< prev:=Nat.pos_of_ne_zero (by intro empty;rw [nextHost,empty,Nat.zero_mul] at live;omega)
    let seed : DescentCommonHost.Pool (Z).graph Unit shapeBits height :=
      (false,(),⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩,.inl none)
    have palette : 0< (pool).card:=Finset.card_pos.mpr
      ⟨_,Finset.mem_image.mpr ⟨seed,Finset.mem_univ _,rfl⟩⟩
    exact Nat.mul_pos usable palette
  have headCount : 0<2*(phys).oldTicketCount :=by
    change 0<2*(2*(((k+1)*2^k)*(2^n+1)))
    positivity
  obtain ⟨regFit,numFit⟩:=(phys).stem_room_active floor oldCode flags number inverse safe ⟨0,headCount⟩ capacity inverseSize hubSize
  have registers : DescentResetStemTemplatePorts.Room reg rows prev (pool).card w₀ cut₀:=by
    rw [←calendar_palette B]
    exact regFit
  have compiled:=issued_from_registers B pointer b M previous value room signBits onWire values roster₀ chips
    own chart saved cut₀ (window).ports (window).bank start lift size (fun lo=>accessible_later prior (peer lo))
    beforePeer (fun lo=>(phys).entry_reads floor sc safe m₀ _ _ (local_ lo) (fits₀ _) (size _))
    (fun lo=>(phys).entry_reads floor sc safe m₀ _ _ (tagged lo) (fits₀ _) (size _))
    (fun z lo=>(phys).entry_reads floor sc safe m₀ _ _ (signed z lo) (fits₀ _) (size _))
    number reg network physical measured registers numFit capacity active blank ha safe.stems.positive
    ((phys).front_order floor).2.2 hostFit width limit record four absence
  have stop : (phys).stemOutput floor=(jobB).outputBase cut₀ pointer :=
    ((phys).job_output floor (sc).stems).symm.trans (congrArg (fun s:StemJob=>s.outputBase cut₀ pointer) dates)
  have cpu : ((phys).received floor sc safe).image m₀=(jobB).image cut₀ pointer start :=
    ((phys).received_job floor sc safe m₀).trans (congrArg (fun s:StemJob=>s.image cut₀ pointer start) dates)
  have reading (x : Fin X) (s : Bool) (slot : Slot) (p : Row HP groups M) :=compiled.2 x s slot p
  have emitted (x : Fin X) (s : Bool) (slot : Slot) (p : Row HP groups M) :
      ((phys).received floor sc safe).image m₀ ((phys).stemOutput floor+
        (finProdFinEquiv (x,(ord) (s,slot))).val*(HP*chunks groups M)+(row HP groups M p).val)=
      ((data (fun r g₀=>(originalTrunkRack B r).elim 0 (fun v=>DescentResetFieldAssembler.raw b («meta» B ((g₀,v),x)
        (localOrigin B ((g₀,v),x) (stemIndex B s slot))))) p).val:Word w₀) :=by
    rw [cpu,stop]
    exact reading x s slot p
  refine ⟨((phys).received_any floor sc safe m₀).1,emitted,?_⟩
  have cnt : (phys).signedQueries=stemsCount B:=congrArg₂ DescentResetStemPackedIssue.count (calendar_low_count B) paid.symm
  exact physical_stem_operand B (phys) floor sc safe m₀ endRoom rfl cnt rfl emitted
end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
