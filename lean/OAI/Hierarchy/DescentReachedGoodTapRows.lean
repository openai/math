import OAI.Hierarchy.DescentGoodTapIssuedWord
import OAI.Hierarchy.DescentMeasuredRotorDonors
import OAI.Hierarchy.DescentRecordedPublicBoard
import OAI.Hierarchy.DescentRecordedRotorLayers

namespace OAI
/-! # Measured public rotor operands on the reached reset date -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan
open DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt DescentRotorWindowArchive
open DescentGroupPeerOrder DescentPackedTicketChronology DescentPacking DescentResetStemCompactOrder
open DescentFallbackPeriod.Projected DescentResetHostSize DescentSIMDLookup DescentRotorWindowScore
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

/-- Reindex the existing operand tape when the recorded number of donor bits is
identified with the actual previous width. -/
def tapDataCast (cfg : DescentResetPublicOperandBook.Config) (degree cap c k field n : ℕ)
    {a b : ℕ} (eqn : a=b) :
    (matrixConfig cfg degree cap (2^(a-c)) k field).Data n →
    (matrixConfig cfg degree cap (2^(b-c)) k field).Data n :=by
  cases eqn
  exact id

variable {F P V : Type} [Field F] {groups : ℕ} [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε (Fin groups) V k) (S : AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m≃Fin groups×Block k) (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
local notation "native" => order.trans Fin.valEmbedding
local notation "old" => W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
    (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site => (A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
    (grp : Fin groups↪ℕ) (vertex : V↪Fin (Fintype.card V)) (padded : Fintype.card V≤H)
local notation "pad" => vertex.trans (Fin.castLEEmb padded)
local notation "ids" => (pad).trans Fin.valEmbedding
local notation "c" => T.commonDepth
local notation "r" => Z.k-c
local notation "fit" => frm.enough.trans (Nat.sub_le ..)
variable (snap : RootObservation A S ready digits (order.trans Fin.valEmbedding) grp (vertex.trans (Fin.castLEEmb padded)) Z T frm field)
variable (f bound wire K : ℕ) (traffic : V→V→Block m→ℕ) (weight : V→Block m→ℕ)
    (roster : ResetInput.SourceFrame.Roster Z T (fun u : W.graph.Site => (A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g frm ((vertex.trans (Fin.castLEEmb padded)).trans Fin.valEmbedding) A.near Z.n f bound wire K (fun v z j=>(traffic v z j:ℝ)) A.degree weight)
    (law : DonorOrder A digits) (sorted : SourceSorted W order)
    (tickets : Z.placement.OrderedTickets (DescentOrderedReset.grains W A.grainCount order))
    (wide : max (max (Z.k-T.commonDepth) (2^Z.n)) (2^(Z.k-T.commonDepth))<2^field)
variable (tag : DescentResetPublicOperandBook.Config) (effective : ℕ) (extent : effective=m)
local notation "sample" => ({tag with residual:=r,multiplicity:=C,packetWidth:=Z.width,gain:=f} :
    DescentResetPublicOperandBook.Config)
local notation "cfg" a:arg => matrixConfig sample A.degree A.cap (2^(a-c)) k field
local notation "rowsAt" => DescentSharedBookScan.ranks (a:=r) (Y:=2^Z.n) (D:=A.degree)
  (snap).chart (2^Ht) (Ht+2) (snap).memory
variable (side : Bool) (root : Z.placement.Good)
local notation "E" => Cells Z.placement side root
local notation "who" => frm.host.symm root.val.1
local notation "hi" => Z.rootBlock T (.inl root)
local notation "atRow" e:arg => localAddress A native S ready digits frm.basis («c»:=c) side (e).val
local notation "slot" e:arg => finProdFinEquiv (((atRow e).1.cast (congrArg (fun z=>2^(z-c)) extent.symm)),(atRow e).2)
local notation "key" => (Function.Embedding.subtype (fun e=>Z.placement.owner side (Z.placement.contact e)=.inl root)).trans
  (DescentOrderedReset.grains W A.grainCount order)
local notation "src" => source Z.placement side root
local notation "dst" => target Z.placement side root

include roster law sorted tickets wide in
theorem tap_support_cast (x : (cfg effective).Data Z.n)
    (neighbors : Fin H→Fin A.degree→Option (Fin H)) (reservation : Fin H→Fin A.degree→Fin A.degree→Fin 6→Cell field)
    (neighborRead : ∀v j,neighbors (pad v) j=(hostRoster A ids v j).map pad)
    (paidRead : ∀v j l s,reservation (pad v) j l s=peerData (a:=field) A S ready digits Z T frm pad v j l s)
    (gathered : ∀j,(cfg m).oldData (tapDataCast sample A.degree A.cap c k field Z.n extent x) j=
      RootSources.paddedRow snap.stencil neighbors snap.marks (fun u z=>(rowsAt u z).val)
        (fun _=>previousDigit frm.basis fit) reservation (pad who) hi (ix j))
    (hostWord : ((cfg effective).oldConfig.header ((cfg effective).basic x) 3).val=
      DescentResetStemWord.hostCode (compress (hostDomain A vertex who) (vertex who).val) (decide (who∉A.near who)))
    (groupWord : ∀e : E,((cfg effective).oldConfig.digit ((cfg effective).basic x) (slot e) 0).val=
      compress (groupDomain digits frm.basis fit who hi) (A.pos (W.graph.src e.val.1)).1.val)
    (fineWord : ∀e : E,((cfg effective).oldConfig.digit ((cfg effective).basic x) (slot e) 1).val=
      (A.block (W.graph.src e.val.1)).val)
    (indexed : ∀v,originalId W.graph.Site v=(A.site vertex ready.coordinates v).val) :
    (∀e : E,(cfg effective).endpoints side (Z.goodLabel T root) x (slot e)=some (src e,dst e)) ∧
    (∀j,(¬∃e : E,slot e=j)→(cfg effective).endpoints side (Z.goodLabel T root) x j=none) ∧
    (∀a b : E,DescentFallbackItemSelect.before ((cfg effective).oldItem x side) (slot a) (slot b)↔key a<key b) ∧
    (cfg effective).traffic x side (Z.goodLabel T root)=DescentBaseProfile.matrixOfBundles src dst :=by
  subst effective
  let grains:=Function.Embedding.subtype (fun e=>Z.placement.owner side (Z.placement.contact e)=.inl root)
  let obs : MeasuredPublicRows («r»:=r) A S ready digits frm.basis fit order grp vertex padded sample side who hi x grains :=
    { own := snap.stencil
      peers := neighbors
      marks := snap.marks
      ranks := fun u z=>(rowsAt u z).val
      comparison := fun _=>previousDigit frm.basis fit
      reserved := reservation
      reached := snap.markRead
      matrix := gathered
      signedFits := snap.signedFits
      host := hostWord
      located := fun e=>rotorCellsAt A S ready digits Z T frm side root e.val e.property
      groupWord := groupWord
      fineWord := fineWord }
  have snapBoard := measured_public_board A S ready digits order Z T frm grp vertex padded
    snap.word rowsAt f tag side root x obs snap.stencilRead neighborRead (fun _ _=>rfl) (fun _ _=>rfl) paidRead
  have nFit : Z.n<field := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
    (((le_max_right r (2^Z.n)).trans (le_max_left _ _)).trans_lt wide)
  exact observed_socket_support A S ready digits order Z T frm grp vertex padded snap.word rowsAt
    snap.wordFits snap.signedFits snap.onWire f bound wire K traffic weight roster law sorted tickets wide nFit
    tag side root x obs snapBoard indexed

/-- Decode both original coordinate words at a good root's occupied rows
from the same physical table that also contains its padded rows. -/
theorem tap_coordinates_cast (x : (cfg effective).Data Z.n)
    {ng : ℕ} (hosts lanes b : ℕ) (position : Block k) (band : Fin ng)
    (coarse : band.val*2^k+position.val=(hi).val)
    (digits_at : ∀y : Block m,(digits y).1.val=y.val/2^k ∧ (digits y).2.val=y.val%2^k)
    (coords : ∀(j : Fin (2^(effective-c)*(2*A.cap))) (axis : Fin 2),
      ((cfg effective).oldConfig.digit ((cfg effective).basic x) j ⟨axis.val,by omega⟩).val=
        (⟨m,k,m-c,hosts,ng,lanes,b⟩ : DescentStemCoordinateBook.Shape).value frm.basis
          ⟨axis.val,by omega⟩ position
          ((finProdFinEquiv.symm j : Fin (2^(effective-c))×Fin (2*A.cap)).1.cast
            (congrArg (fun z=>2^(z-c)) extent)) band) :
    (∀e : E,((cfg effective).oldConfig.digit ((cfg effective).basic x) (slot e) 0).val=
      compress (groupDomain digits frm.basis fit who hi) (A.pos (W.graph.src e.val.1)).1.val) ∧
    (∀e : E,((cfg effective).oldConfig.digit ((cfg effective).basic x) (slot e) 1).val=
      (A.block (W.graph.src e.val.1)).val) :=by
  subst effective
  have observed:=rotor_coordinate_values A S ready digits native Z T frm hosts lanes b side root position band
    coarse digits_at
  constructor
  · intro e
    have read := coords (finProdFinEquiv (atRow e)) 0
    rw [finProdFinEquiv.symm_apply_apply (atRow e)] at read
    exact read.trans (observed e).1
  · intro e
    have read := coords (finProdFinEquiv (atRow e)) 1
    rw [finProdFinEquiv.symm_apply_apply (atRow e)] at read
    exact read.trans (observed e).2

end
end Hierarchy.DescentSixParty.GroupStage

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentGL DescentResetHostSize DescentSIMDLookup DescentSharedBookScan
open DescentRotorWindowArchive DescentFallbackPeriod DescentFallbackPeriod.Projected DescentGroupPeerOrder
open DescentPaidResidentCount.Reset DescentOldContactSender DescentStageEdgeReceipt DescentRosterOrder
open DescentSharedCableNames.Stage DescentIssuedFallbackPanel DescentResetLocalRoster DescentPacking
open DescentResetStemCompactOrder DescentChosenRouter DescentPackedTicketChronology DescentPackedFlowPair
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d p : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z w hist D n h C f g cut tail field query lanes nodes args grain : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "c" => (T).commonDepth
local notation "r" => (Z).k-c
local notation "H" => S.hostSize i
local notation "dep" => GroupStage.depthBound D n f g
local notation "host" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "next_" => PackedFlow.Padded.roster (D:=(A).degree) (A) (Recorded.oldName input) input.valid.host
local notation "paid_" => Recorded.paddedValue (b:=field) c r next_ (Recorded.oldDepth B) (Recorded.oldWidth B)
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "small" => B.frame.enough.trans (Nat.sub_le ..)
local notation "full" => (A).wire*((A).z*G.b)*(A).cap
local notation "groups" => Fin.valEmbedding (n:=S.groupCount i)
local notation "unit" => (Z).unit/p
local notation "cfg" => publicOperandConfig B field query lanes unit unit nodes args grain
local notation "rank_" snap:arg => ranks (a:=r) (Y:=2^(Z).n) (D:=(A).degree) (snap).chart (2^dep) (dep+2) (snap).memory
local notation "priorData" x:arg => GroupStage.tapDataCast cfg (A).degree (A).cap c k field (Z).n B.keyWidth x

/-- The reached matrix page, comparison and reservation words and the three scalar
stem coordinates determine all six fields of the selected good rotor. -/
theorem reached_good_tap_rows (record : B.Recorded p) (age : 0< i) (sorted : SourceSorted W input.order)
    (snap : PaddedSnapshot B input.valid.host field) (wide : max (max r (2^(Z).n)) (2^r)<2^field)
    (side : Bool) (root : (Z).placement.Good) (x : (cfg).Data (Z).n)
    (gathered : ∀j,
      (GroupStage.matrixConfig cfg (A).degree (A).cap (2^((S.groupWidth k tail i+k)-c)) k field).oldData
        (priorData x) j=
      RootSources.paddedRow snap.stencil next_ snap.marks (fun v j=>((rank_ snap) v j).val)
        (fun _=>Receiver.matrixBefore B.frame.basis small) paid_
        (host (B.frame.host.symm root.val.1)) ((Z).rootBlock T (.inl root)) (ix j))
    (hostWord : ((cfg).oldConfig.header ((cfg).basic x) 3).val=
      DescentResetStemWord.hostCode
        (compress (hostDomain A input.vertex (B.frame.host.symm root.val.1)) (input.vertex (B.frame.host.symm root.val.1)).val)
        (decide (B.frame.host.symm root.val.1∉(A).near (B.frame.host.symm root.val.1))))
    (groupWord : ∀e : Cells (Z).placement side root,
      ((cfg).oldConfig.digit ((cfg).basic x) (publicRotorSlots B side root e) 0).val=
        compress (groupDomain digits B.frame.basis small (B.frame.host.symm root.val.1) ((Z).rootBlock T (.inl root)))
          ((A).pos (W.graph.src e.val.1)).1.val)
    (fineWord : ∀e : Cells (Z).placement side root,
      ((cfg).oldConfig.digit ((cfg).basic x) (publicRotorSlots B side root e) 1).val=((A).block (W.graph.src e.val.1)).val)
    (capacity : ((cfg).reg x 0).val=(A).cap) :
    GoodTapRows (p:=p) (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes) (args:=args) (grain:=grain)
      B side root x :=by
  have levels:=(DescentRecordedRotorLayers.from_prior_cap B record side root _ capacity).1.symm
  have support : (∀e : Cells (Z).placement side root,(cfg).endpoints side ((Z).goodLabel T root) x
      (publicRotorSlots B side root e)=some (source (Z).placement side root e,target (Z).placement side root e)) ∧
    (∀j,(¬∃e : Cells (Z).placement side root,publicRotorSlots B side root e=j)→
      (cfg).endpoints side ((Z).goodLabel T root) x j=none) ∧
    (∀a b : Cells (Z).placement side root,DescentFallbackItemSelect.before ((cfg).oldItem x side)
      (publicRotorSlots B side root a) (publicRotorSlots B side root b) ↔
      DescentOrderedReset.grains W B.count B.order a.val<DescentOrderedReset.grains W B.count B.order b.val) ∧
    (cfg).traffic x side ((Z).goodLabel T root)=
      DescentBaseProfile.matrixOfBundles (source (Z).placement side root) (target (Z).placement side root) :=by
    have roster := Recorded.old_roster (reset:=B)
    rw [PackedFlow.mutual_near (A)] at roster
    have relative (v : input.V) (j : Fin (A).degree) := Recorded.peer_at (input:=input) v j
    have reservation (v : input.V) (j l : Fin (A).degree) (s : Fin 6) :=
      Recorded.paddedValue_at (b:=field) (reset:=B) v j l s
    have indexed:=input.siteName age
    have law:=GroupStage.scheduledDonorOrder (S:=S) (A) ctl.base ctl.radix input.vertex input.valid.coordinates indexed
    let model:=cfg
    rcases input with @⟨V,vFin,vDec,phase,ready,rfl,rfl,history,degree,oldOrder,compact,edgeOrder,siteOrder⟩
    rcases B with ⟨ct,rfl,fit₀,order,eq_,Z₀,T₀,age₀,date,extent,tickets,unit₀,dimension,tape,board,
      frame,listed,raw,geometry,hubs,valid,grain₀,wire₀,atoms,branch,capacity₀⟩
    subst order
    refine GroupStage.tap_support_cast phase S ready _ oldOrder Z₀ T₀ frame _ compact ready.host snap f _
      phase.wire _ _ _ roster law sorted tickets wide model Z₀.k extent side root x _ _ relative ?_
      gathered hostWord groupWord fineWord indexed
    intro u j l axis
    refine (reservation u j l axis).trans ?_
    dsimp only
    unfold GroupStage.peerData
    have sameKey : (compact.trans (Fin.castLEEmb ready.host)).trans Fin.valEmbedding = compact.trans Fin.valEmbedding := by
      ext
      rfl
    rw [sameKey]
    cases hostRoster phase (compact.trans Fin.valEmbedding) u j <;>
      cases hostRoster phase (compact.trans Fin.valEmbedding) u l <;> rfl
  exact ⟨support.1,support.2.1,support.2.2.1,support.2.2.2,levels,capacity⟩

/-- At the actual coordinate sheet the group and fine assertions above both come
from the same two columns, for every donor on the mounted root. -/
theorem reached_good_tap_rows_at (record : B.Recorded p) (age : 0< i) (sorted : SourceSorted W input.order)
    (snap : PaddedSnapshot B input.valid.host field) (wide : max (max r (2^(Z).n)) (2^r)<2^field)
    (side : Bool) (root : (Z).placement.Good) (x : (cfg).Data (Z).n)
    (gathered : ∀j,
      (GroupStage.matrixConfig cfg (A).degree (A).cap (2^((S.groupWidth k tail i+k)-c)) k field).oldData
        (priorData x) j=
      RootSources.paddedRow snap.stencil next_ snap.marks (fun v j=>((rank_ snap) v j).val)
        (fun _=>Receiver.matrixBefore B.frame.basis small) paid_
        (host (B.frame.host.symm root.val.1)) ((Z).rootBlock T (.inl root)) (ix j))
    (hostWord : ((cfg).oldConfig.header ((cfg).basic x) 3).val=
      DescentResetStemWord.hostCode
        (compress (hostDomain A input.vertex (B.frame.host.symm root.val.1)) (input.vertex (B.frame.host.symm root.val.1)).val)
        (decide (B.frame.host.symm root.val.1∉(A).near (B.frame.host.symm root.val.1))))
    {ng : ℕ} (hosts lanes₀ b : ℕ) (position : Block k) (band : Fin ng)
    (coarse : band.val*2^k+position.val=((Z).rootBlock T (.inl root)).val)
    (coords : ∀(j : Fin (2^r*(2*(A).cap))) (axis : Fin 2),
      ((cfg).oldConfig.digit ((cfg).basic x) j ⟨axis.val,by omega⟩).val=
        (⟨S.groupWidth k tail i+k,k,(S.groupWidth k tail i+k)-c,hosts,ng,lanes₀,b⟩ : DescentStemCoordinateBook.Shape).value
          B.frame.basis ⟨axis.val,by omega⟩ position
          ((finProdFinEquiv.symm j : Fin (2^r)×Fin (2*(A).cap)).1.cast (congrArg (fun z=>2^(z-c)) B.keyWidth)) band)
    (capacity : ((cfg).reg x 0).val=(A).cap) :
    GoodTapRows (p:=p) (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes) (args:=args) (grain:=grain)
      B side root x :=by
  suffices decoded :
      (∀e : Cells (Z).placement side root,
        ((cfg).oldConfig.digit ((cfg).basic x) (publicRotorSlots B side root e) 0).val=
          compress (groupDomain digits B.frame.basis small (B.frame.host.symm root.val.1) ((Z).rootBlock T (.inl root)))
            ((A).pos (W.graph.src e.val.1)).1.val) ∧
      (∀e : Cells (Z).placement side root,
        ((cfg).oldConfig.digit ((cfg).basic x) (publicRotorSlots B side root e) 1).val=((A).block (W.graph.src e.val.1)).val) from
    reached_good_tap_rows B record age sorted snap wide side root x gathered hostWord decoded.1 decoded.2 capacity
  let model:=cfg
  rcases input with @⟨V,vFin,vDec,phase,ready,rfl,rfl,history,degree,oldOrder,compact,edgeOrder,siteOrder⟩
  rcases B with ⟨ct,rfl,fit₀,order,eq_,Z₀,T₀,age₀,date,extent,tickets,unit₀,dimension,tape,board,
    frame,listed,raw,geometry,hubs,valid,grain₀,wire₀,atoms,branch,capacity₀⟩
  subst order
  exact GroupStage.tap_coordinates_cast («H»:=S.hostSize i) (f:=f) (effective:=Z₀.k) (extent:=extent)
    («A»:=phase) (S:=S) (ready:=ready) («digits»:=S.resetInputDigits ctl.base ctl.radix i)
    (order:=oldOrder) («Z»:=Z₀) («T»:=T₀) (frm:=frame) (tag:=model) (side:=side) (root:=root)
    x hosts lanes₀ b position band coarse (fun _=>⟨rfl,rfl⟩) coords

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
