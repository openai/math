import OAI.Hierarchy.DescentNamedCutResolverKeys
import OAI.Hierarchy.DescentSelectedBoardPaletteStock

namespace OAI
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPacking.PackedMatch.Local.Stage
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 7000
set_option cleanup.letToHave false

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
    {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
      (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=GroupStage.depthBound (atRound S.rounds) n f g)
      (t:=S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice}
    (br : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))) (fun _ => S.firstWidth G.b p*1)} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)}
    {nonneg : 0 ≤ (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
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
local notation "bn₀" => (v₀).bornBook
local notation "fmt₀" => (v₀).ticket.depotShape (v₀).short

variable (w shelfHeader headerBase : ℕ) (pos : 0<k)
    (code : DatePorts.OrdinaryCodeRoom ports ticket op g tailBits p f drift degree payload seats root ordinary w)
    (exec : DatePorts.OrdinaryExecutionRoom ports ticket op g tailBits p f drift degree payload seats root ordinary
      w shelfHeader headerBase code)
local notation "steps₀" => (v₀).issuedSteps root ports (entry₀) code.signed w (mat₀) (sh₀) code.blocks code.paths
  code.slots code.chip code.endFit code.packed code.radix code.funded
local notation "donors" m:arg => DatePorts.ordinaryDonorMemory ports ticket op g tailBits p f drift degree
  payload seats root ordinary w shelfHeader headerBase pos code exec m
open DescentOrdinaryBorn DescentOrdinaryPaletteBirth DescentPrimitivePalette DescentKernelHistory
local notation "date" => DonorDate.atDate G S g k i p
local notation "L" => (v₀).paletteShape
local notation "rows" => BitDescription.scannedRows nonneg T
local notation "first" j:arg => W.graph.src ((rows).pick (j,0))
local notation "slot" j:arg => DescentSharedCableNames.Stage.outgoing A (prior.order.trans Fin.valEmbedding) S prior.valid
  ⟨(rows).pick (j,0), (A).quantum_positive _ ((rows).picked (j,0))⟩

include ticket before tail cut in
theorem cut_palette_limit : T.z≤S.grainAt G.b p 0:=by
  rw [ticket.grain_on_cut before tail cut br.issuedGrains,S.grain_initial]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right G.base_pos (Nat.sub_le _ _))

include ticket before tail cut in
theorem cut_palette_capacity : (A).cap=(date).cap:=
  congrArg DonorDate.cap (donor_date_eq X G S br ticket before tail cut)

include ticket before tail cut in
private theorem cut_palette_format : (fmt₀)=(date).format:=by
  have chosen:=donor_date_eq X G S br ticket before tail cut
  have degreeEq : (A).degree=(date).degree:=congrArg DonorDate.degree chosen
  have short : (v₀).short=max (k+3) (Nat.clog 2 ((A).degree+1)):=by
    change max (k+3) (Nat.clog 2 ((date).degree+1))=_
    rw [degreeEq]
  change ticket.depotShape (v₀).short=(date).format
  rw [short,←chosen]
  rfl

variable (age : i<S.length) {original : Memory w}
    (stores : CutStores X G S (radix:=radix) (f:=f) (g:=g) (p:=p) ticket ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec original)
local notation "capEq" => cut_palette_capacity X G S br ticket before tail cut
local notation "limit" => cut_palette_limit X G S br ticket before tail cut
local notation "shape" => stores.inputs.toBirthShape
local notation "rowH" j:arg => (prior.vertex ((A).pos (first j)).2).castLE stores.oldFit
local notation "rowG" j:arg => finProdFinEquiv (S.groupDigits age radix ((A).pos (first j)).1)
local notation "chip" => (entry₀).nativeChips (v₀) shape stores.parts

/-- Each selected original outgoing grain identifies the host, group, site
and seat at which the six coefficient tokens have actually been published. -/
theorem cut_newborn_token
    (past : Fin (L).blocks→Fin (L).hosts→Fin (L).oldGroups→Cell ((L).primitiveBits*(L).oldNodes))
    (origin : Fin (L).blocks→Fin (L).successors→Fin (L).groups→Cell ((L).originBits*(L).newNodes))
    (near : Fin (L).hosts→Fin (L).ports→Option (Fin (L).hosts))
    (j : (rows).pairs) (party : Fin 6) :
    let hostGrid : (L).hosts=(bn₀).hosts:=rfl
    let groupGrid : (L).oldGroups=(bn₀).groups:=stores.groups.symm
    let stock:=(v₀).paletteStock floor₀ entry₀ mat₀ past chip hostGrid groupGrid origin near
    stock.newborn ((L).bornIndex ((A).block (first j)) ((slot j).cast capEq) party)
      ((rowH j).cast (hostGrid.trans (shape).hosts).symm) (rowG j)=
      token G s (S.grainAt G.b p 0) op (bornLabel («s»:=s) op (c:=choice) limit j party) :=by
  intro hostGrid groupGrid stock
  have fmtEq:=cut_palette_format X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
  have capField : (bn₀).cap=(fmt₀).cap:=(congrArg DepotRAM.Shape.cap fmtEq).symm
  have orig : (bn₀).scale=T.z:=(ticket.grain_on_cut before tail cut br.issuedGrains).symm
  have cohort : (rowG j).val=((A).pos (first j)).1.val:=by
    simp only [AtomSchedule.groupDigits,Equiv.trans_apply,Equiv.apply_symm_apply]
    rfl
  have geometrySlots : (entry₀).clip.venue.slots=(v₀).withIssuedSigned.materialFormat.slots :=by
    change 2^DescentHostDegree.packExponent 20 (A).degree+2 = 2^DescentHostDegree.packExponent 20 T.Δ+2
    rw [(Dated.Meter.ticket_shape ticket).2]
  apply PhysicalOrdinary.SelectedBoard.registered_palette_birth
    (v:=v₀) (oldFit:=stores.oldFit) (R:=stores.rotor) (selected:=stores.pick) (m:=donors original)
    (parts:=(steps₀).parts) (B:=stores.board) (choiceEq:=stores.selected)
    (floor:=floor₀) (entry:=entry₀) («matching»:=mat₀) (birth:=shape) (parts₀:=stores.parts)
    (socket:=rfl) (profileEq:=rfl) (slotsEq:=geometrySlots) (blocks:=rfl) (cap:=capField)
    (names:=(congrArg DepotRAM.Shape.names fmtEq).symm) (widths:=(congrArg DepotRAM.Shape.widths fmtEq).symm)
    (past:=past) (hostGrid:=hostGrid) (groupGrid:=groupGrid) (origin:=origin) (next:=near)
    (scale:=orig) (under:=limit) (i:=j) (party:=party)
    (h:=(rowH j).cast (hostGrid.trans (shape).hosts).symm) (g:=rowG j)
  dsimp only
  rw [stores.material]
  have gr : ((rowG j).cast groupGrid).cast (shape).groups=((A).pos (first j)).1:=Fin.ext cohort
  exact heq_of_eq (congrArg (fun idx => stores.board.material (rowH j) idx) gr)

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
