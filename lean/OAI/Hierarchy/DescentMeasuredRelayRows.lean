import OAI.Hierarchy.DescentMeasuredOperandLeaf
import OAI.Hierarchy.DescentResetTrunkRelay

namespace OAI
/-! # Received old signed slots of the public fallback relay -/
namespace Hierarchy.DescentFallbackOperandBranch.Config

/-- Relay rank reads the same old cable key as the received positive socket. -/
theorem relayItems_key {n : ℕ} (C : DescentFallbackOperandBranch.Config) (x : C.Data n)
    (root : DescentResetLocalRoster.code C.residual × Option (Fin (2^n)))
    (addr : Fin (DescentFallbackShapeTable.rows C.residual (2^n))) (total : ℕ) (j : Fin C.count) :
    (C.relayItems x j).key=(C.rowsAt x true root addr total j).key := rfl

private theorem relay_member {n : ℕ} (C : DescentFallbackOperandBranch.Config) (x : C.Data n)
    (target : DescentContacts.Endpoint (2^n)) (lo : Fin C.donors) (slot : Fin (2*C.oldCap)) :
    finProdFinEquiv (lo,slot) ∈ C.relayRows x target ↔
      DescentFallbackPeriod.localWord (C.packet x) lo/2 = DescentFallbackShapeTable.cell C.residual target ∧
        (DescentFallbackPeriod.signed (C.packet x) lo slot).map (fun ch => ch.target) = some true := by
  classical
  let index : Fin C.count := finProdFinEquiv (lo,slot)
  change index ∈ C.relayRows x target ↔ _
  unfold relayRows
  rw [Finset.mem_filter]
  rw [and_iff_right (Finset.mem_univ index)]
  simp only [index,Equiv.symm_apply_apply]

end Hierarchy.DescentFallbackOperandBranch.Config
namespace Hierarchy.DescentSixParty.GroupStage
open DescentPacking.PackedMatch.Local.Stage
open DescentSharedCableNames DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentSIMDLookup DescentStageEdgeReceipt DescentFallbackShapeTable DescentRosterOrder DescentResetHostSize
open DescentPackedLeafSelector DescentPlainTerminal DescentPlainTerminal.Suffix DescentFallbackRankRAM
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ) (groups : J↪ℕ) (vertex : V↪Fin H)
variable {zz ww : ℕ} {ct : W.graph.Edge→ℕ} {cut : ∀e,W.graph.width e=ct e*(zz*G.b)}
    (Z : ResetInput (W.granular ct (zz*G.b) cut) (q*ww) ε h C Ht)
    (T : ResetInput.Terminals (F:=F) Z)
    (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site => (A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
    (snap : RootObservation A S ready digits native groups vertex Z T frm field)
set_option quotPrecheck false
local notation "stageCfg" sample => ({sample with
  oldDegree := A.degree
  oldCap := A.cap
  donors := 2^(m-T.commonDepth)
  fineBits := k
  fieldBits := field
  residual := Z.k-T.commonDepth
  maxDepth := Ht} : DescentFallbackOperandBranch.Config)
local notation "rank" => ranks (a:=Z.k-T.commonDepth) (Y:=2^Z.n) (D:=A.degree)
  snap.chart (2^Ht) (Ht+2) snap.memory

private theorem half_tag (a : ℕ) (tag : Bool) : (2*a+tag.toNat)/2=a := by
  cases tag
  · simp
  · change (2*a+1)/2=a
    omega

private theorem decode_stored {D cap field : ℕ} (label : Option (Live D cap))
    (bitsFit : DescentSignedCableCodec.width D cap ≤ field) :
    DescentSignedCableCodec.decode D cap
      (((DescentSignedCableCodec.encode label).val : Cell field).val : Cell (DescentSignedCableCodec.width D cap)) = label := by
  have bound := (DescentSignedCableCodec.encode label).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) bitsFit)
  rw [Fin.val_cast_of_lt bound, Fin.cast_val_eq_self, DescentSignedCableCodec.decode_encode]

private theorem incoming_slot (names : Stage.Host J V k↪ℕ) (u : Stage.Host J V k) (j : Fin (2*A.cap)) :
    ((Stage.signedPanel A native S ready names u j).map (fun ch=>ch.target))=some true ↔
      ∃e,atSlot A native S ready true u j=some e := by
  have seen : ((Stage.signedPanel A native S ready names u j).map (fun ch=>ch.target))=some true ↔
      (signedPeer A native S ready names true u j).isSome=true := by
    by_cases used : ∃p,Stage.signed A native S ready u.1 u.2 p=j
    · obtain ⟨p,rfl⟩:=used
      cases side : (Stage.live A native S ready names u p).target <;>
        simp [signedPeer,Stage.signed_read,side,physicalPeer_read]
    · have empty:=Stage.signed_empty A native S ready names u j (fun p hp=>used ⟨p,hp⟩)
      simp [signedPeer,empty]
  rw [seen,signedPeer_slot]
  cases found : atSlot A native S ready true u j <;> simp

/-- A marked row names exactly one original incoming grain of this terminal.
The row contains the actual old signed bit, stencil and local cable ordinal. -/
theorem relayRows_at (zEq : zz=A.z) (wireEq : ww=A.wire) (countEq : ct=A.grainCount)
    (sample : DescentFallbackOperandBranch.Config) (t : Z.Fallback) (x : (stageCfg sample).Data Z.n)
    (packet : (stageCfg sample).packet x=DescentFallbackPeriod.inputs (field:=field)
      snap.stencil snap.peers snap.marks (fun u j=>(rank u j).val)
      (vertex (frm.host.symm (T.code t).1)) (Z.rootBlock T (.inr t))) (j : Fin (2^(m-T.commonDepth)*(2*A.cap))) :
    j∈(stageCfg sample).relayRows x (shortName T.commonDepth (T.code t)).2 ↔
      ∃! e : Stage.Grain A,T.home (show W.graph.Site from endSite A true e)=t ∧
        finProdFinEquiv (localAddress (c:=T.commonDepth) A native S ready digits frm.basis true e)=j := by
  subst zz; subst ww; subst ct
  obtain ⟨⟨lo,slot⟩,rfl⟩:=finProdFinEquiv.surjective j
  let v:=frm.host.symm (T.code t).1
  let hi:=Z.rootBlock T (.inr t)
  let u:=oldCellAt A S ready digits Z T frm t lo
  let reachedConfig := ({sample with
    oldDegree := A.degree
    oldCap := A.cap
    donors := 2^(m-T.commonDepth)
    fineBits := k
    fieldBits := field
    residual := Z.k-T.commonDepth
    maxDepth := Ht} : DescentFallbackOperandBranch.Config)
  let pkt:=reachedConfig.packet x
  let names:=cableNames k (groupRank groups (vertex.trans Fin.valEmbedding))
  have mark : DescentFallbackPeriod.signed pkt lo slot=Stage.signedPanel A native S ready names u slot := by
    dsimp only [pkt]
    rw [packet]
    exact (decode_stored (snap.marks (vertex v) hi lo slot) snap.signedFits).trans (snap.markRead v hi lo slot)
  have own : DescentFallbackPeriod.localWord pkt lo=snap.word u := by
    have rd:=snap.stencilRead v hi lo
    have bound : snap.stencil (vertex v) hi lo<2^field:=by
      rw [rd]
      exact (Nat.lt_succ_self _).trans (snap.wordFits u)
    dsimp only [pkt]
    rw [packet]
    exact (DescentFallbackPeriod.own_read _ _ _ _ _ _ lo bound).trans rd
  have membership : finProdFinEquiv (lo,slot)∈reachedConfig.relayRows x (shortName T.commonDepth (T.code t)).2 ↔
      snap.word u/2=(chartShape A S ready Z T t).val ∧ ∃e,atSlot A native S ready true u slot=some e := by
    apply (DescentFallbackOperandBranch.Config.relay_member reachedConfig x _ lo slot).trans
    change DescentFallbackPeriod.localWord pkt lo / 2=_ ∧
      (DescentFallbackPeriod.signed pkt lo slot).map _=some true ↔ _
    rw [own,mark,incoming_slot A S ready native names u slot]
    rfl
  rw [membership]
  have identifies (e : Stage.Grain A) (atSlotE : atSlot A native S ready true u slot=some e) :
      snap.word u/2=(chartShape A S ready Z T t).val ↔ T.home (show W.graph.Site from endSite A true e)=t := by
    have code:=(atSlot_iff A native S ready true u slot e).mp atSlotE
    have atHome : Stage.home A (endSite A true e)=u:=(port_fst A true e).symm.trans (congrArg Prod.fst code)
    let t':=T.home (show W.graph.Site from endSite A true e)
    have hcell:=cell_home A S ready digits Z T frm true e
    rw [atHome] at hcell
    have wEq:=snap.onWire true e
    rw [atHome] at wEq
    change snap.word u=2*(chartShape A S ready Z T (fallbackCell A S ready digits Z T frm true u)).val+
      (exceptionalCell A S ready digits Z T frm u).toNat at wEq
    rw [hcell] at wEq
    have half : snap.word u/2=(chartShape A S ready Z T t').val := by
      exact (congrArg (fun w : ℕ => w/2) wEq).trans (half_tag _ _)
    rw [half]
    constructor
    · intro same
      have host : (T.code t').1=(T.code t).1 := by
        have pos := congrArg (fun point : Stage.Host J V k => point.1.2) atHome
        exact (frm.homeHost (DescentIssuedFallbackPanel.endSite (W:=W) A true e)).trans
          ((congrArg frm.host pos).trans (frm.host.apply_symm_apply _))
      have grd : coarseName T.commonDepth (T.code t')=coarseName T.commonDepth (T.code t) := by
        have move := congrArg (fun x : Stage.Host J V k =>
          group T.commonDepth (rearrange frm.basis (oldBlock digits x))) atHome
        refine (frm.homeHigh (DescentIssuedFallbackPanel.endSite (W:=W) A true e)).trans (move.trans ?_)
        change group T.commonDepth (rearrange frm.basis (digits.symm
          (digits ((rearrange frm.basis).symm (join _ hi lo))))) = hi.val
        rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
        exact congrArg Fin.val (DescentPlainTerminal.high_join _ hi lo)
      have label : (shortName T.commonDepth (T.code t')).2=(shortName T.commonDepth (T.code t)).2 := by
        rw [←chartShape_read A S ready Z T t',←chartShape_read A S ready Z T t,same]
      exact T.code.injective (relative_injective (k:=T.commonDepth) (r:=0)
        (T.codeLegal t').1 (T.codeLegal t).1 grd (Prod.ext host label))
    · intro eqn
      exact congrArg (fun b=>(chartShape A S ready Z T b).val) eqn
  have physical (e : Stage.Grain A) :
      stemRows A S ready digits native Z T frm true t (finProdFinEquiv (lo,slot))=some e ↔
        atSlot A native S ready true u slot=some e ∧ T.home (show W.graph.Site from endSite A true e)=t := by
    simp only [stemRows,Equiv.symm_apply_apply,panel]
    change (atSlot A native S ready true u slot).filter _=some e ↔ _
    cases hslot : atSlot A native S ready true u slot with
    | none=>simp
    | some a=>
      by_cases h : T.home (show W.graph.Site from endSite A true a)=t <;> simp
  constructor
  · rintro ⟨shape, e,hit⟩
    have terminal:=(identifies e hit).mp shape
    have found:=(physical e).mpr ⟨hit,terminal⟩
    have ordr:=panel_sound A native S ready digits frm.basis (frm.enough.trans (Nat.sub_le ..))
      true (frm.host.symm (T.code t).1) (selectedRoot A S ready Z T t)
      (fun z=>T.home (DescentIssuedFallbackPanel.endSite (W:=W) A true z)=t)
      (by simpa only [stemRows,Equiv.symm_apply_apply] using found)
    refine ⟨e,⟨terminal,congrArg finProdFinEquiv ordr.2.symm⟩,?_⟩
    rintro z ⟨live,eqn⟩
    have val:=stem_slot_read A S ready digits native Z T frm true t z live
    rw [eqn,found] at val
    exact (Option.some.inj val).symm
  · rintro ⟨e,⟨live,num⟩,_⟩
    have found:=stem_slot_read A S ready digits native Z T frm true t e live
    rw [num] at found
    have slotEq:=((physical e).mp found).1
    exact ⟨(identifies e slotEq).mpr live,e,slotEq⟩

end
end Hierarchy.DescentSixParty.GroupStage

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentRelativeContacts DescentSharedBookScan DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open DescentResetStemCompactOrder
open scoped Classical
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "A" => input.placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "m" => S.groupWidth k tail i+k

local notation "cfg" sample:arg field:arg => ({sample with
  oldDegree := (A).degree
  oldCap := (A).cap
  donors := 2^(m-(T).commonDepth)
  fineBits := k
  fieldBits := field
  residual := (Z).k-(T).commonDepth
  maxDepth := GroupStage.depthBound D n f g} : DescentFallbackOperandBranch.Config)

theorem relay_rows_at {H field : ℕ} (grp : Fin (S.groupCount i)↪ℕ) (vertex : input.V↪Fin H)
    (snap : GroupStage.RootObservation (A) S input.valid digitsIn (input.order.trans Fin.valEmbedding)
      grp vertex (Z) (T) B.frame field)
    (sample : DescentFallbackOperandBranch.Config) (t : (Z).Fallback) (x : (cfg sample field).Data (Z).n)
    (packet : (cfg sample field).packet x=DescentFallbackPeriod.inputs (field:=field) snap.stencil snap.peers snap.marks
      (fun u j=>(ranks (a:=(Z).k-(T).commonDepth) (Y:=2^(Z).n) (D:=(A).degree)
        snap.chart (2^(GroupStage.depthBound D n f g)) (GroupStage.depthBound D n f g+2) snap.memory u j).val)
      (vertex (B.frame.host.symm ((T).code t).1)) ((Z).rootBlock (T) (.inr t)))
    (j : Fin (2^(m-(T).commonDepth)*(2*(A).cap))) :
    j∈(cfg sample field).relayRows x (shortName (T).commonDepth ((T).code t)).2 ↔
      ∃! e : (old).graph.Edge,(T).home ((old).graph.dst e)=t ∧ incomingIndex B e=j := by
  have main:=GroupStage.relayRows_at (A) S input.valid digitsIn (input.order.trans Fin.valEmbedding) grp vertex
    (Z) (T) B.frame snap input.grain.symm input.edges.symm B.count_eq sample t x packet j
  rw [main]
  let equiv : (old).graph.Edge≃Stage.Grain (A) :=Equiv.sigmaCongrRight fun e=>finCongr (congrFun B.count_eq e)
  have law (e : (old).graph.Edge) : (T).home (show W.graph.Site from endSite (A) true (equiv e))=(T).home ((old).graph.dst e) :=
    congrArg (T).home (beforeStem_end B true e)
  constructor
  · rintro ⟨e,⟨resident,index⟩,unique⟩
    obtain ⟨a,rfl⟩:=equiv.surjective e
    refine ⟨a,⟨(law a).symm.trans resident,index⟩,?_⟩
    rintro b ⟨own,num⟩
    exact equiv.injective (unique (equiv b) ⟨(law b).trans own,num⟩)
  · rintro ⟨a,⟨resident,index⟩,unique⟩
    refine ⟨equiv a,⟨(law a).trans resident,index⟩,?_⟩
    rintro e ⟨own,num⟩
    obtain ⟨b,rfl⟩:=equiv.surjective e
    exact congrArg equiv (unique b ⟨(law b).symm.trans own,num⟩)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
