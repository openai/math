import OAI.Hierarchy.DescentCutAcquiredNumerals
import OAI.Hierarchy.DescentAcquiredPriorRange
import OAI.Hierarchy.DescentAcquiredRolePage
import OAI.Hierarchy.DescentSelectedAcquiredRows
import OAI.Hierarchy.DescentReachedPaidFundedReturn
import OAI.Hierarchy.DescentSelectedBirthWords
import OAI.Hierarchy.DescentArchivedDeclaredRange

namespace OAI
/-! # Reading the earlier signed operands and primitive labels on the selected compact host -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPacking.PackedMatch.Local.Stage
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ fee} {hu : 0 ≤ u} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=Ht) (t:=S.rounds) S.height
      (initial X S.copies s (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice} (br : Branch X G S radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 P bits} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G price fee S k i z D wire s} {T : StageInput W G rate fee}
    {nonneg : 0 ≤ fee} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' wire s}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement


variable (ports : DatePorts) (op : RotorSpec) (tailBits drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "books₀" => OrdinaryBooks.atDate G S op g k i p tailBits drift degree payload seats ports
local notation "base₀" => (books₀).onTicket ticket g tailBits p f payload seats ports.venue.lanes ports.io.roster ordinary
local notation "floor₀" => (base₀).stageStart root
local notation "v₀" => DatePorts.ordinaryModel ports ticket op g tailBits p f drift degree payload seats root ordinary
local notation "entry₀" => (base₀).registeredEntry ports floor₀
local notation "mat₀" => (base₀).registered_match ports floor₀ (Nat.le_max_left ports.argumentsPerNode (S.retainedArgumentsAt G drift))

open DescentDatedPriorOperand DescentOperandStateBanks DescentHaloWalkRAM DescentSharedCableNames
open PhysicalOrdinary.ArgumentEntry
open DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentOrdinaryOriginMask
open DescentRawCablePanel ProtocolRAM
open scoped Classical Fin.CommRing
local notation "sh₀" => (base₀).registered_geometry ports floor₀
local notation "rc₀" => (v₀).resolver
local notation "vx₀" => (v₀).vector
local notation "H₀" => (entry₀).clip.venue.hosts

variable (w shelfHeader headerBase : ℕ) (pos : 0<k)
    (code : DatePorts.OrdinaryCodeRoom ports ticket op g tailBits p f drift degree payload seats root ordinary w)
    (exec : DatePorts.OrdinaryExecutionRoom ports ticket op g tailBits p f drift degree payload seats root ordinary
      w shelfHeader headerBase code)
local notation "wired" m:arg => DatePorts.ordinarySignedMemory ports ticket op g tailBits p f drift degree
  payload seats root ordinary w shelfHeader headerBase pos code exec m


local notation "steps₀" => (v₀).issuedSteps root ports (entry₀) code.signed w (mat₀) (sh₀) code.blocks code.paths
  code.slots code.chip code.endFit code.packed code.radix code.funded
local notation "donors" m:arg => DatePorts.ordinaryDonorMemory ports ticket op g tailBits p f drift degree
  payload seats root ordinary w shelfHeader headerBase pos code exec m
open DescentGroupPeerOrder DescentStageEdgeReceipt DescentPacking.PackedMatch.Local

open DescentLocalArchiveOrder.PaddedOrigin DescentScalarVenueMask DescentPacking.PackedMatch.Local.Stage
open DescentGroupPeerOrder DescentOrdinaryAtomFieldRAM
local notation "deg₀" => prior.placement.degree
local notation "shelf" => DescentOrdinaryVenueReturn.shapeSlots deg₀
local notation "trueCap" => prior.placement.cap
local notation "GS" => S.groupCount (i+1)*2^k
local notation "OG" => S.groupCount i
local notation "mb" => (v₀).reference.countBits


variable {original:Memory w} (stores:CutStores X G S (f:=f) (g:=g) (p:=p) (radix:=radix) ticket ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec original)

open DescentLocalArchiveOrder DescentPrimitivePalette DescentKernelHistory DescentRetainedRangeDigits
variable (B : BitDescription W) (numbering : Local B) (places : DatePorts.RangeRoom ports prior B)
    (enough : Fintype.card prior.V≤ports.operandHosts)

open DescentScalarVenueMask DescentGroupPeerOrder DescentHaloWalkRAM DescentGL
open DescentLocalArchiveOrder.PaddedOrigin DescentSortedHaloRaster DescentPaidResidentCount
local notation "rr₀" => BitDescription.scannedRows nonneg T
local notation "ly₀" => bestLayout (branchWidth G (fun _:(rr₀).pairs=>T.z) ((rr₀).profile choice))
local notation "groups₀" => GadgetNetwork.newSite W.graph (rr₀).pick ly₀ (rr₀).pack
local notation "tall₀" => (entry₀).clip.core.values stores.parts stores.active
local notation "tokens₀" => fun block₁ slot₁ (host₁ : Fin (Fintype.card prior.V)) group₁ => (tall₀) block₁ slot₁ (host₁.castLE stores.oldFit) group₁
local notation "nativeRank" => groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)

section BoundSources
variable {X G S ticket ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec stores B numbering places enough}

set_option maxHeartbeats 650000 in
theorem cut_authentic_material (pose : stores.Canonical) :
    Descriptors shelf k (A).pos (A).block (ticketParent (he:=nonneg) (T:=T))
        (ticketSlot (c:=choice) ticket) (((activeChart ticket).key nonneg T choice)∘groups₀)
        prior.vertex (Function.Embedding.refl _) (rotor A nativeRank) tokens₀ ∧
    (∀x j (h₀:Fin H₀) g₀,Fintype.card prior.V≤h₀.val→(tall₀) x j h₀ g₀=none) ∧
    ∀h₀ g₀,stores.hubs (h₀.castLE stores.oldFit)=flags (cap:=prior) h₀ g₀:=by
  have profileAt : (entry₀).clip.core.profile = (v₀).profile := by rfl
  have slotsAt : (entry₀).clip.core.slots = shelf := by rfl
  have raw:=(v₀).selected_material_rows stores.oldFit stores.pick (donors original) (steps₀).parts
    stores.rotor pose.1 stores.board stores.selected
  obtain ⟨yes,ghost,hubs⟩:=raw
  refine ⟨?_,?_,?_⟩
  · simp only [DescentOrdinaryVenueIngress.Chart.values, stores.material, pose.2.1, profileAt, slotsAt]
    exact yes
  · simp only [DescentOrdinaryVenueIngress.Chart.values, stores.material, pose.2.1, profileAt, slotsAt]
    exact ghost
  · intro h₀ g₀
    rw [pose.2.2]
    exact (hubs h₀).trans (census_hub_flags (cap:=prior) h₀ g₀)

theorem cut_prior_range_inputs (precision : 2≤ports.operandBits)
    (packed : ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (j : Fin (vx₀).operands) (f₀ : Fin 3) (x : Block k) (h₀ : Fin (Fintype.card prior.V)) (g₀ : Fin OG) :
    ((entry₀).oldInput (v₀) stores.inputs floor₀ (mat₀) stores.old (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f₀) j)
        x (h₀.castLE stores.oldFit) g₀).val=
      (DatePorts.physicalRangeSource ports prior B places enough (wired original) j.val f₀ x h₀ g₀).val:=by
  have oldLayout : (entry₀).previous=ports.rangeLayout:=by
    change ports.argumentLayout (2^k)=ports.rangeLayout
    rw [places.radix]
    rfl
  have width : (entry₀).previous.size+2=ports.operandBits:=ports.argument_width _ precision
  refine acquired_prior_range_of_reads prior B ports places enough (wired original) (v₀) (entry₀) stores.inputs floor₀
    (mat₀) oldLayout width rfl rfl stores.oldFit stores.old rfl stores.oldRead ?_ h₀ g₀ x j f₀
  change ((entry₀).previous.size+2)*ports.nodes*ports.operandLanes≤w
  rwa [width]

private theorem extend_at_live {H K g w : ℕ} (value : Fin H → Fin g → Cell w) (h : Fin K) (j : Fin g)
    (inside : h.val < H) : DescentOrdinaryHostPad.extend K value h j = value ⟨h.val,inside⟩ j := by
  rw [DescentOrdinaryHostPad.extend, dite_eq_left inside]

include enough in
theorem cut_role_inputs (labels : NodeOrder.All B→Label G s (S.grainAt G.b p 0) op)
    (issued : ∀x h g,(stores.roles x h g).val=(encode (printedBits G s (S.grainAt G.b p 0) op) ports.nodes (fun j=>
        (DatePorts.slotAt ports prior B numbering places (x.cast (congrArg (2^·) places.radix)) j h (g.cast places.groups)).elim 0
          (fun y=>token G s (S.grainAt G.b p 0) op (labels y)))).val)
    (x : Block k) (h₀ : Fin (Fintype.card prior.V)) (g₀ : Fin OG) :
    (((entry₀).roleValues (v₀) stores.roles) x (h₀.castLE stores.oldFit) g₀).val=
      (Reached.NodeCells.rolePage (N:=ports.nodes) prior B numbering
        (fun y=>token G s (S.grainAt G.b p 0) op (labels y)) x h₀ g₀).val:=by
  let earlier x h (q:Fin ports.venue.groups):=stores.roles x h (q.cast places.groups.symm)
  have posted : ∀b h g,(earlier b h g).val=(encode (printedBits G s (S.grainAt G.b p 0) op) ports.nodes (fun n=>
      (DatePorts.slotAt ports prior B numbering places (b.cast (congrArg (2^·) places.radix)) n h g).elim 0
        (fun y=>token G s (S.grainAt G.b p 0) op (labels y)))).val:=by
    intro b h g
    exact issued b h (g.cast places.groups.symm)
  have read:=DatePorts.acquired_role_page prior B numbering ports places op labels enough stores.oldFit earlier posted x h₀ g₀
  have inside : (h₀.castLE stores.oldFit).val < ports.operandHosts := h₀.isLt.trans_le enough
  have liveHost : (h₀.castLE stores.oldFit).val < (entry₀).previous.hosts := inside
  have oldRead := extend_at_live (earlier x) (h₀.castLE stores.oldFit) (g₀.cast places.groups) inside
  have heldRead := extend_at_live (stores.roles x) (h₀.castLE stores.oldFit) g₀ liveHost
  have groupCast : (g₀.cast places.groups).cast places.groups.symm = g₀ := Fin.ext rfl
  have same := congrArg (fun idx => (stores.roles x ⟨h₀.val,inside⟩ idx).val) groupCast
  exact (congrArg Fin.val heldRead).trans (same.symm.trans ((congrArg Fin.val oldRead).symm.trans read))

end BoundSources

open DescentBundleHistory DescentScalarBookReshape
variable (history : Archive W) (localOrder : Local history.bit) (placed : DatePorts.RangeRoom ports prior history.bit)
    (previous : WorldShape p R history.bit) (hp : 0<p) (one : 1≤R)
    (pinsFit : ∀v,p∣bits v) (unit : p∣T.z)
local notation "nextShape" => WorldShape.follow hp T.unitPos unit norm (ticket.quantum.symm ▸ ticket.cuts)
  (WorldShape.scanned nonneg hp one pinsFit T previous unit choice)
local notation "newBits" => (ticket.advance history).bit
local notation "newOrder" => DescentLocalArchiveOrder.advance ticket history localOrder
local notation "newPorts" => DatePorts.ordinary (v₀) floor₀
local notation "spanPage" j:arg f:arg => DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) j
local notation "labelType" => Label G s (S.grainAt G.b p 0) op

include before tail cut enough in
/-- At any physical slot of the accepted ordinary return, each live operand's three
digits and every other operand count come from the same seven-word gather. All three
digits are zero when the physical node slot is empty. -/
theorem cut_span_values (age:i<S.length) (pose : stores.Canonical)
    (width : (rc₀).size+2=ports.operandBits) (precision : 2≤ports.operandBits)
    (packed : ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (newRoom : DatePorts.RangeRoom newPorts next newBits) (labels : NodeOrder.All history.bit→labelType)
    {ptr flags₀} (seen : DatePorts.ArchiveRead ports prior history.bit localOrder placed previous op labels ptr flags₀ (wired original))
    (slots : ∀y : NodeOrder.All history.bit,(occurrences (previous.sites y.1) y.2).length≤ports.argumentsPerNode)
    (registered : ∀x h g,(stores.roles x h g).val=(encode (printedBits G s (S.grainAt G.b p 0) op) ports.nodes (fun n=>
      (DatePorts.slotAt ports prior history.bit localOrder placed (x.cast (congrArg (2^·) placed.radix)) n h (g.cast placed.groups)).elim 0
        (fun y=>token G s (S.grainAt G.b p 0) op (labels y)))).val)
    (x : Fin (2^(newPorts).venue.k)) (n₀:Fin (rc₀).nodes) (h₀:Fin (rc₀).hosts)
    (g₀:Fin (newPorts).venue.groups) (j:Fin (rc₀).operands) (f₀:Fin 3) :
    let owner:=DatePorts.slotAt newPorts next newBits newOrder newRoom x n₀ h₀ g₀
    owner.elim True (fun y=>j.val<(occurrences ((nextShape).sites y.1) y.2).length ∨ f₀=2) →
      (take n₀ (((v₀).registeredOperandBooks (sh₀) stores.books) x (spanPage j f₀) h₀ g₀)).val=
        owner.elim 0 (fun y=>atSlot ((nextShape).sites y.1) y.2 j.val f₀):=by
  intro owner needed
  let axes:=selected_w_axes X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
  let pull:=fun y:Fin GS=>(S.groupDigits age radix).symm (finProdFinEquiv.symm y)
  let oldWords:=fun pg x h y=>((entry₀).oldInput (v₀) stores.inputs floor₀ (mat₀) stores.old pg x h (pull y)).cast
    (congrArg (fun a:ℕ=>2^(a*ports.nodes)) width)
  let fresh:=fun pg x (t:Fin trueCap) party h y=>((entry₀).bornInput (v₀) stores.inputs floor₀ (mat₀) stores.parts pg
    x (t.cast axes.1.symm) party h (pull y)).cast (congrArg (2^·) width)
  let birth:=selectedBirthSource stores axes.1 width
  let source:=acquiredReferences (cap:=prior) («mb»:=mb) age radix ports (v₀) stores.oldFit axes.2.1 rfl rfl width
    tall₀ (fun h _=>stores.hubs h) ((entry₀).roleValues (v₀) stores.roles) oldWords fresh
  let tokens:= (tokens₀)
  let tok:=fun y=>token G s (S.grainAt G.b p 0) op (labels y)
  obtain ⟨auth,noTicket,hub⟩:=cut_authentic_material (stores:=stores) pose
  have live : ∀y,tok y≠0:=fun y=>DatePorts.original_tokens_positive (G:=G) («s»:=s) (Z:=S.grainAt G.b p 0) (arch:=history.bit) (op:=op) (labels:=labels) y
  have counts : ports.nodes<2^mb:=Nat.lt_of_lt_of_le (Nat.lt_succ_self ports.nodes) (Nat.le_pow_clog (by decide : 1<2) _)
  have priorWords:=DatePorts.ArchiveRead.all_range_words seen packed slots
  have birthWords:=selected_birth_words X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
    (stores:=stores) age width
  have low:=acquired_range_prefix («mb»:=mb) (ticket:=ticket) (arch:=history) (tokens:=tokens) (age:=age) (radix:=radix)
    (ports:=ports) (mem:=wired original) (room:=placed) (population:=enough) (prior:=localOrder) (labels:=tok)
    (device:=v₀) (shape:=sh₀) (fits:=stores.oldFit) (low:=axes.2.1) (gs:=rfl) (rs:=rfl) («bits»:=width)
    (birthAt:=birth) (tall:=tall₀) (hubs:=fun h _=>stores.hubs h) (roles:=(entry₀).roleValues (v₀) stores.roles)
    (old:=oldWords) (fresh:=fresh) (fun _ _ _ _=>rfl) hub
    (fun b h g=>Fin.ext (cut_role_inputs (stores:=stores) (B:=history.bit) (numbering:=localOrder) (places:=placed)
      (enough:=enough) labels registered b h g))
    (fun a f b h y=>Fin.ext (cut_prior_range_inputs (stores:=stores) (B:=history.bit) (places:=placed)
      (enough:=enough) precision packed a f b h (pull y)))
    (selected_birth_source_at (stores:=stores) age axes.1 width)
  let values:=previousValues (rc₀) (vx₀) (sh₀).operands (sh₀).blocks (sh₀).hosts (sh₀).groups
    (References.returnedValue (vx₀) source (rc₀).nodes)
  have returned : (((v₀).registeredOperandBooks (sh₀) stores.books) x (spanPage j f₀) h₀ g₀)=
      values (spanPage j f₀) x h₀ g₀:=by
    apply Fin.ext
    exact cut_acquired_numeral X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
      (w:=w) (shelfHeader:=shelfHeader) (headerBase:=headerBase) (pos:=pos) (code:=code) (exec:=exec) (stores:=stores) age pose.1 width (spanPage j f₀) x h₀ g₀
  rw [returned]
  cases at_ : owner with
  | none =>
    exact slot_absent_column ticket history tokens age radix ports (wired original) placed enough localOrder tok (v₀)
      (sh₀) stores.oldFit axes.2.1 rfl rfl width birth source low floor₀ newRoom live counts auth
      tall₀ (fun h _=>stores.hubs h) ((entry₀).roleValues (v₀) stores.roles) oldWords fresh rfl noTicket
      x n₀ h₀ g₀ at_ j f₀
  | some y =>
    have need : j.val<(occurrences ((nextShape).sites y.1) y.2).length ∨ f₀=2:=by
      rw [at_] at needed
      exact needed
    exact slot_present_column ticket history tokens age radix ports (wired original) placed enough localOrder tok (v₀)
      (sh₀) stores.oldFit axes.2.1 rfl rfl width birth source low previous hp one pinsFit unit priorWords birthWords
      floor₀ newRoom live counts auth x n₀ h₀ g₀ y at_ j f₀ need

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
