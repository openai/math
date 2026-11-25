import OAI.Hierarchy.DescentCutRegisteredHeaderAxes
import OAI.Hierarchy.DescentSelectedStoredGeometry
import OAI.Hierarchy.DescentReachedOriginTransport

namespace OAI
/-! Acquired native W prefixes at the actual operand and mouth source pages. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPacking.PackedMatch.Local.Stage
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 3500

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
local notation "calendar" => capCalendar G.b S.rounds g S.height


set_option quotPrecheck false
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
local notation "bn₀" => (v₀).bornBook
local notation "g₀" => (v₀).ticketReadGeometry
local notation "M₀" => (rc₀).lanes
local notation "W₀" => (vx₀).lanes*(vx₀).radix
local notation "vecAt" => (v₀).vectorStart floor₀
local notation "mouthEnd₀" => (v₀).originMouthEnd floor₀
local notation "headerEnd" => (v₀).operandHeaderEnd floor₀
local notation "e₀" => (v₀).material
local notation "fmt₀" => (v₀).ticket.depotShape (v₀).short
local notation "ps₀" => (v₀).operandPathStart floor₀
local notation "refs₀" => ((entry₀).directory (v₀) floor₀ (mat₀)).refs
local notation "Val₀" => References.Rows (v₀).vector (v₀).reference.degree (v₀).reference.k (v₀).reference.oldNodes
  (v₀).reference.capacity ((rc₀).size+2)
local notation "dims₀" => DatePorts.ordinary_header_dimensions ports ticket op g tailBits p f drift degree payload seats root ordinary
local notation "H₀" => (entry₀).clip.venue.hosts
local notation "G₀" => (entry₀).clip.venue.groups
local notation "pop₀" => (entry₀).population (v₀) floor₀
local notation "Active" => Fin H₀→Fin G₀→Cell (1*(entry₀).clip.venue.socket.blocks)
local notation "RealPeers" => Fin H₀→Fin (entry₀).clip.venue.socket.degree→Option (Fin H₀)

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
local notation "phys₀" => (v₀).withIssuedSigned
local notation "room₀" => (v₀).signedReturn floor₀ ports.io ports.archive.count (steps₀).parts (steps₀).adjacency w
local notation "page₀" => (⟨0,Nat.mul_pos (by decide : 0<7) code.slots⟩:Fin (7*(vx₀).operands))
open DescentGroupPeerOrder DescentStageEdgeReceipt DescentPacking.PackedMatch.Local

open DescentLocalArchiveOrder.PaddedOrigin DescentScalarVenueMask DescentPacking.PackedMatch.Local.Stage
open DescentGroupPeerOrder DescentOrdinaryAtomFieldRAM
local notation "deg₀" => prior.placement.degree
local notation "shelf" => DescentOrdinaryVenueReturn.shapeSlots deg₀
local notation "pitch₀" => (2^(k+1)-1)*shelf
local notation "trueCap" => prior.placement.cap
local notation "GS" => S.groupCount (i+1)*2^k
local notation "OG" => S.groupCount i
local notation "roleWidth" => (pop₀).roleBits
local notation "nb" => (v₀).reference.nameBits
local notation "mb" => (v₀).reference.countBits


variable {original:Memory w} (stores:CutStores X G S (f:=f) (g:=g) (p:=p) (radix:=radix) ticket ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec original)
local notation "peer_" => hostRotor (prior.vertex.trans (Fin.castLEEmb stores.oldFit))
  (hostRoster prior.placement (prior.vertex.trans Fin.valEmbedding))
open DescentOrdinaryOriginMask
variable {w shelfHeader headerBase pos code exec}

local notation "axes" => selected_w_axes X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
local notation "tall" => (entry₀).clip.core.values stores.parts stores.active
local notation "compact" => Fin (Fintype.card prior.V)
local notation "tickets" => fun x j (hostIndex:compact) groupIndex=>tall x j (hostIndex.castLE stores.oldFit) groupIndex
local notation "counts" => fun x (hostIndex:compact) groupIndex=>DescentOrdinaryAtomFieldRAM.RoleCounts.count mb
   ((entry₀).roleValues (v₀) stores.roles x (hostIndex.castLE stores.oldFit) groupIndex)
local notation "col" j:arg f:arg => (DescentOperandStateBanks.page ((f:Fin 4).castLE (by decide : 4≤7)) j)
local notation "V" => fun pg l=>onSourceAxes (axes).1 (axes).2.2 id (stores.books pg l)

def header_birth_at (width:(rc₀).size+2=ports.operandBits) (j:ℕ) (fieldIndex:Fin 4)
    (x:Block k) (seat:Fin (A).cap) (party:Fin 6) (hostIndex:compact) (groupIndex:Fin OG) : Cell ports.operandBits :=
  if live:j<(vx₀).operands then
    ((entry₀).bornInput (v₀) stores.inputs floor₀ (mat₀) stores.parts (col ⟨j,live⟩ fieldIndex) x
      (seat.cast (axes).1.symm) party (hostIndex.castLE stores.oldFit) groupIndex).cast (congrArg (2^·) width)
  else 0

theorem header_birth_read (width:(rc₀).size+2=ports.operandBits) (j:Fin (vx₀).operands) (fieldIndex:Fin 4)
    (x:Block k) (seat:Fin (A).cap) (party:Fin 6) (hostIndex:compact) (groupIndex:Fin OG) :
    (header_birth_at X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
      stores width j.val fieldIndex x seat party hostIndex groupIndex).val=
    ((entry₀).bornInput (v₀) stores.inputs floor₀ (mat₀) stores.parts (col j fieldIndex) x
      (seat.cast (axes).1.symm) party (hostIndex.castLE stores.oldFit) groupIndex).val:=by
  unfold header_birth_at
  rw [dite_eq_left j.isLt]
  rfl

open DescentLocalArchiveOrder DescentKernelHistory DescentRetainedRangeDigits DescentScalarBookReshape
variable (arch:Archive W) (places:DatePorts.RangeRoom ports prior arch.bit)
    (enough:Fintype.card prior.V≤ports.operandHosts) (age:i<S.length)
    (width:(rc₀).size+2=ports.operandBits)
local notation "pull" y:arg => (S.groupDigits age radix).symm (finProdFinEquiv.symm y)
local notation "prev" j:arg f:arg => DatePorts.physicalHeaderSource ports prior arch.bit places enough (wired original) j f
local notation "born" j:arg f:arg => header_birth_at X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
      stores width j f

private theorem transport_at {D k K c H Q Q' J r a a' n b:ℕ} (lo:Q'=Q) (width:a'=a)
    (f:Fin Q→Values D k K c H (J*r) a n b) (l:Fin Q') :
    Values.transport lo rfl rfl width f l=(f (l.cast lo)).reindex rfl width.symm:=by
  cases lo;cases width;rfl

theorem cut_header_prefix (canon:stores.Canonical) (precision:2≤ports.operandBits)
    (packed:ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (j:Fin (vx₀).operands) (fieldIndex:Fin 4) (l:Fin (vx₀).lows):
    Values.Prefix stores.oldFit
      (Values.transport (axes).2.1 (rfl:(vx₀).groups=S.groupCount (i+1)) (rfl:(vx₀).radix=2^k) width
        (rangeValues ticket arch tickets age radix counts (prev j.val fieldIndex) (born j.val fieldIndex)) l)
      ((V) (col j fieldIndex) l):=by
  let oldWords:=fun pg x h (y:Fin GS)=>((entry₀).oldInput (v₀) stores.inputs floor₀ (mat₀) stores.old pg x h (pull y)).cast
      (congrArg (fun a:ℕ=>2^(a*ports.nodes)) width)
  let bornWords:=fun pg x (t:Fin trueCap) party h (y:Fin GS)=>((entry₀).bornInput (v₀) stores.inputs floor₀ (mat₀) stores.parts pg
      x (t.cast (axes).1.symm) party h (pull y)).cast (congrArg (2^·) width)
  have aligned:=congrFun (congrFun (cut_acquired_axes X G S br ticket before tail cut ports op tailBits drift degree
    payload seats root ordinary stores age canon.1 width) (col j fieldIndex)) l
  let observed := rangeValues ticket arch tickets age radix counts (prev j.val fieldIndex) (born j.val fieldIndex)
  apply (congrArg (Values.Prefix stores.oldFit
    (Values.transport (axes).2.1 (rfl:(vx₀).groups=S.groupCount (i+1)) (rfl:(vx₀).radix=2^k) width observed l)) aligned).mpr
  apply (congrArg (fun row => Values.Prefix stores.oldFit row _) (transport_at (axes).2.1 width observed l)).mpr
  apply Values.Prefix.reindex
  apply acquired_prefix ticket arch tickets age radix counts (prev j.val fieldIndex) (born j.val fieldIndex)
    stores.oldFit tall (fun h _=>stores.hubs h) ((entry₀).roleValues (v₀) stores.roles)
    oldWords bornWords (col j fieldIndex) (l.cast (axes).2.1)
  · intros; rfl
  · intro hostIndex groupIndex
    rw [canon.2.2]
    exact (DescentScalarVenueMask.Stage.hub_padded prior.vertex (Fin.castLEEmb stores.oldFit) A hostIndex).trans
      (DescentLocalArchiveOrder.census_hub_flags (cap:=prior) hostIndex groupIndex)
  · intros; rfl
  · intro x hostIndex y
    apply Fin.ext
    exact cut_prior_header_inputs (X:=X) (G:=G) (S:=S) (ticket:=ticket) (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (stores:=stores) (B:=arch.bit)
      (places:=places) (enough:=enough) precision packed j fieldIndex x hostIndex (pull y)
  · intro x seat party hostIndex y
    apply Fin.ext
    exact (header_birth_read X G S br ticket before tail cut ports op tailBits drift degree payload seats root
      ordinary stores width j fieldIndex x seat party hostIndex (pull y)).symm

private theorem source_axes_origin {D k₀ K c c' H H' Q Q' J r a a' n n' b:ℕ}
    (cap:c'=c) (label:n'=n) (lo:Q'=Q) (width:a'=a) (wide:H≤H')
    (small:Fin Q→Values D k₀ K c H (J*r) a n b) (large:Values D k₀ K c' H' (J*r) a' n' b)
    (l:Fin Q') (heard:Values.Prefix wide
      (Values.transport lo (rfl:J=J) (rfl:r=r) width small l) (onSourceAxes cap label id large)) :
    Values.Prefix wide (Values.originTransport rfl rfl rfl cap lo (rfl:J=J) (rfl:r=r) width small l)
      (onSourceAxes rfl label id large):=by
  cases cap;cases lo;cases width;exact heard

/-- The native origin and newborn readers consume the same W as the prior header
reader. The former retain the original signed chip capacity in their field type. -/
theorem cut_header_origin_prefix (canon:stores.Canonical) (precision:2≤ports.operandBits)
    (packed:ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (j:Fin (vx₀).operands) (fieldIndex:Fin 4) (l:Fin (vx₀).lows):
    Values.Prefix stores.oldFit
      (Values.originTransport rfl rfl rfl (axes).1 (axes).2.1
        (rfl:(vx₀).groups=S.groupCount (i+1)) (rfl:(vx₀).radix=2^k) width
        (rangeValues ticket arch tickets age radix counts (prev j.val fieldIndex) (born j.val fieldIndex)) l)
      (onSourceAxes rfl (axes).2.2 id (stores.books (col j fieldIndex) l)):=by
  apply source_axes_origin
  exact cut_header_prefix X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
    stores arch places enough age width canon precision packed j fieldIndex l

/-- Physical page zero is the origin register. The newborn lookup for argument
j uses field zero of that argument on the same book. -/
theorem cut_origin_mouth_pages (j:Fin (vx₀).operands) :
    (v₀).headerMouthPage floor₀ entry₀ mat₀ (j.cast (mat₀).newArgs.symm)=col j (0:Fin 4) ∧
      page₀=col (⟨0,code.slots⟩:Fin (vx₀).operands) (0:Fin 4):=by
  constructor
  · apply Fin.ext
    simp [PhysicalOrdinary.headerMouthPage,DescentOperandStateBanks.page]
    rfl
  · apply Fin.ext
    simp [DescentOperandStateBanks.page]

/-- The origin reader accepts the two old and newborn fields already cast to the
register width. These casts do not change the chronological origin chart. -/
private theorem align_stamp_width {a b:ℕ} (eqn:a=b)
    (old:Block k→compact→Fin OG→Cell (b*ports.nodes))
    (born_:Block k→Fin trueCap→Fin 6→compact→Fin OG→Cell b)
    (l:Fin (vx₀).lows):
    Values.originTransport rfl rfl rfl (axes).1 (axes).2.1
      (rfl:(vx₀).groups=S.groupCount (i+1)) (rfl:(vx₀).radix=2^k) rfl
      (rangeValues ticket arch tickets age radix counts
        (fun x h g=>(old x h g).cast (congrArg (fun t:ℕ=>2^(t*ports.nodes)) eqn.symm))
        (fun x t y h g=>(born_ x t y h g).cast (congrArg (2^·) eqn.symm))) l=
    Values.originTransport rfl rfl rfl (axes).1 (axes).2.1
      (rfl:(vx₀).groups=S.groupCount (i+1)) (rfl:(vx₀).radix=2^k) eqn
      (rangeValues ticket arch tickets age radix counts old born_) l:=by
  cases eqn
  rfl

theorem cut_header_stamp_prefix (canon:stores.Canonical) (precision:2≤ports.operandBits)
    (packed:ports.operandBits*ports.nodes*ports.operandLanes≤w) (l:Fin (vx₀).lows):
    Values.Prefix stores.oldFit
      (Values.originTransport rfl rfl rfl (axes).1 (axes).2.1
        (rfl:(vx₀).groups=S.groupCount (i+1)) (rfl:(vx₀).radix=2^k) rfl
        (rangeValues ticket arch tickets age radix counts
          (fun x hostIndex groupIndex=>((prev 0 (0:Fin 4)) x hostIndex groupIndex).cast (congrArg (fun t:ℕ=>2^(t*ports.nodes)) width.symm))
          (fun x t y hostIndex groupIndex=>((born 0 (0:Fin 4)) x t y hostIndex groupIndex).cast (congrArg (2^·) width.symm))) l)
      (onSourceAxes rfl (axes).2.2 id (stores.books page₀ l)):=by
  let j:Fin (vx₀).operands:=⟨0,code.slots⟩
  have pageZero : page₀=col j (0:Fin 4) := by
    apply Fin.ext
    simp [DescentOperandStateBanks.page,j]
  have shift := align_stamp_width (X:=X) (G:=G) (S:=S) (br:=br) (ticket:=ticket) (before:=before)
    (tail:=tail) (cut:=cut) (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift)
    (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary)
    (stores:=stores) (arch:=arch) (age:=age) (eqn:=width)
    (old:=prev 0 (0:Fin 4)) (born_:=born 0 (0:Fin 4)) (l:=l)
  apply (congrArg (fun row => Values.Prefix stores.oldFit row
    (onSourceAxes rfl (axes).2.2 id (stores.books page₀ l))) shift).mpr
  apply (congrArg (fun pg => Values.Prefix stores.oldFit _
    (onSourceAxes rfl (axes).2.2 id (stores.books pg l))) pageZero).mpr
  exact cut_header_origin_prefix X G S br ticket before tail cut ports op tailBits drift degree
    payload seats root ordinary stores arch places enough age width canon precision packed j 0 l

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
