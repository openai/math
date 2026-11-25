import OAI.Computability.BorderVNP.DiagonalSelectedLookupSites
import OAI.Computability.BorderVNP.DiagonalCandidateOwnedReadback
import OAI.Computability.BorderVNP.DiagonalReferenceDeclaredGroup
import OAI.Computability.BorderVNP.DiagonalPositiveHeaderClaims

/-! # Native lookup and header at the calendar's attained signed sites -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA RoutingISA.Evaluator RoutingISA.Transmission RoutingISA.Evaluator.SignedPrep
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment JointHeader PackedHistoryCircuit LocalRow Crossing
open DiagonalTallyPacketEmit FiniteEvaluator
open scoped BigOperators

variable {R r t d link inner n w volume : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (skeleton : WireLayout (R+1) r link) (header : List Bool) (task : SignedTaskArena.Layout)
    (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (pin : Fin d → Bool) (guess : Fin (R+1) → ℕ → Bool) (dst ib hb sb : Fin (R+1) → ℕ)
    (frame receivingBase : ℕ) (owner : ℕ → Fin (R+1)) (word : Broadcast task.cube.n task.cube.header.d task.cube.header.cap)
    (pub : HeaderExterior skeleton header → Fin (R+1) → Arg → Word w)
    (mac : HeaderExterior skeleton header → Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : HeaderExterior skeleton header → Fin (R+1) → Bank w) (mem : HeaderExterior skeleton header → Fin (R+1) → Memory w)
    {I : Type*} [Fintype I] (host : I → Fin task.cube.cells) (key : I ↪ ℕ) (sizes : I → ℕ)
    {dim : ℕ} {P A : Type*} {bits : P → ℕ} [Fintype A] (N : Network dim P bits) (cell : N.Site → Fin task.cube.cells)
    (label : Fin task.cube.cells → Label (task.cube.n+1) task.cube.header.d) (recv : A → Fin task.cube.cells) (amount : A → ℕ)

set_option quotPrecheck false
local notation "ar" => task.cube
local notation3 (prettyPrint := false) "decl" => Prod.mk (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) word.1))
  (fun (p : Sym2 (Fin task.cube.header.d)) (j : Fin (task.cube.n+1)) => readCode (task.cube.header.cap+1) (word.2 p j))
local notation3 (prettyPrint := false) "grp" => declaredTeam ar decl label recv amount R
local notation3 (prettyPrint := false) "own" => greedyOwner R task.cube.b task.cube.s label recv amount
local notation "count" => (D.directory pp lp).length
local notation "total" => count+task.cube.header.d.choose 2
local notation "X" => HeaderExterior skeleton header
local notation3 (prettyPrint := false) "PL" u => G.pinLayout u (ib u) (hb u) (sb u)
local notation3 (prettyPrint := false) "BF" u => G.transferFrame u skeleton.header (dst u)

variable (wire : WireLayout (R+1) r link) (same : wire.header=skeleton.header)
local notation3 (prettyPrint := false) "back" => (HeaderExterior.changeLayout skeleton wire same header).symm


set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

local notation3 (prettyPrint := false) "atSite(" x "," u ")" => CandidateSite («X»:=volume) ar D pp lp word owner decl grp frame receivingBase
    (PL u) (G.processorFields u pin (Subtype.val x) (ib u) (hb u) (sb u)) (BF u) (guess u) (pub x u) (mac x u)
    (reg x u) (mem x u) host key sizes N cell recv amount

open RoutingISA.SignedTaskArena Physical.NativeLedger RoutingISA.Evaluator.SignedPrep
open DiagonalTallyCellReports

variable {res : ℕ} (arena : ProcessorSlots.StartupArena)
    (packet : PositiveFields res task.cube.n task.cube.header.d task.cube.header.cap task.cube.teams task.dim w)
    (previous : Fin 81 → VPVNP.BurstRAM.Word w) (origin fresh gates outputs field off ell ctl : ℕ)
    (fixed : Routing.Block (R+1))
    (source : SourceReports task.cube (greedyOwner R task.cube.b task.cube.s label recv amount))
    (F : PreparationFrame G wire task.cube (Prod.mk (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) word.1)) (fun (p : Sym2 (Fin task.cube.header.d)) (j : Fin (task.cube.n+1)) => readCode (task.cube.header.cap+1) (word.2 p j))) header pin (pub ∘ (HeaderExterior.changeLayout skeleton wire same header).symm) (mac ∘ (HeaderExterior.changeLayout skeleton wire same header).symm) (reg ∘ (HeaderExterior.changeLayout skeleton wire same header).symm) (mem ∘ (HeaderExterior.changeLayout skeleton wire same header).symm))
    (B : F.Builders fixed task.id (greedyOwner R task.cube.b task.cube.s label recv amount)) (agree : F.SourceAgreement fixed source B)
    (q : {v : Declared task.cube (greedyOwner R task.cube.b task.cube.s label recv amount) (Prod.mk (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) word.1)) (fun (p : Sym2 (Fin task.cube.header.d)) (j : Fin (task.cube.n+1)) => readCode (task.cube.header.cap+1) (word.2 p j))) // source.pins v.val}) (reports : source.actual q.val.val)

local notation3 (prettyPrint := false) "rawBase" => rawAddress arena res task.cube.n task.cube.header.d task.cube.header.cap
local notation3 (prettyPrint := false) "old(" u ")" => routingExtension (task.extension rawBase (Fin.val u) w previous)
  D origin task.cube.cables task.cube.cells
local notation3 (prettyPrint := false) "payload" => declaredWords ar own decl q.val
local notation3 (prettyPrint := false) "replayed" => F.replay fixed payload
local notation3 (prettyPrint := false) "full" => (F.sourceEquiv fixed source B agree).symm ⟨q,reports⟩
local notation3 (prettyPrint := false) "visited" u => (visitsEquiv task.id ((pub ∘ back) full.1 u)
  ((mac ∘ back) full.1 u) ((reg ∘ back) full.1 u) ((mem ∘ back) full.1 u)).symm (full.2 u)
local notation3 (prettyPrint := false) "banks" => bankData q.val.val.2 task.cube.header.packetBase task.cube.singleBank
local notation3 (prettyPrint := false) "numbers" => Fin.valEmbedding ∘ own q.val.val.1

/-- On the actually attained signed site, decode the raw copied header and the native
lookup without introducing a separate execution of the geometry interpreter. The
extra observations on the returned trace can include its 37 signed control fields. -/
theorem PreparationFrame.SelectedLookupSites.signedOwnedReadback
    {Trace : HeaderExterior skeleton header → Fin (R+1) → Type}
    (state : ∀ x u, Trace x u → RoutingISA.Bank w × VPVNP.BurstRAM.Memory w)
    (charge : ∀ x u, Trace x u → ℕ × ℕ)
    (tail : ∀ (x : HeaderExterior skeleton header) (u : Fin (R+1)), atSite(x,u) → Trace x u → Prop)
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase
      owner word pub mac reg mem host key sizes N cell label recv amount wire same (fun x u site =>
        ∃ trace : Trace x u,
          site.OnReturn old(u) fresh gates outputs field off ell ctl (List.ofFn packet.profile)
              (DiagonalTallyRAM.broadcast w packet.rawCounts) 0 (state x u trace).1 (state x u trace).2
              (charge x u trace).1 (charge x u trace).2 ∧ tail x u site trace))
    (cube : word=packet.cube) (valid : declarationInRange word) (axes : task.cube.header.a=task.cube.n+1)
    (base : frame=arena.frame) (size : arena.header=PositiveFields.width res task.cube.n task.cube.header.d
      task.cube.header.cap task.cube.teams task.dim w)
    (secondary : arena.next ≤ task.cube.header.header) {query guesses reader : ℕ}
    (endFit : task.endAddress w query guesses reader<2^w) (space : task.after.packed≤2^w)
    (teamCount : task.cube.teams=R+1) (teamsFit : task.cube.teams<2^w) (wordPos : 0<w)
    (values : CubeConstants.valueBound task.id<2^w) (room : task.cube.ReplayRoom w frame)
    (u : Fin (R+1)) (destination : dst u=arena.broadcastBase)
    (demand : ℕ)
    (capacity : (CubeVisits.teamList (banks).axis task.cube.header.blocks numbers u.val).length≤task.p.report.vertices)
    (digits : Tally.argumentWidth task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s≤task.p.report.cubeWidth) :
    (((pub ∘ back) full.1 u) 0).val=arena.frame ∧
      CubePacket.WordPrepared (gadgetLookup task ((pub ∘ back) full.1 u) numbers u.val demand banks)
        task.id ((pub ∘ back) full.1 u) (visited u).owned.val.2.2 ∧
      HeaderSeed task packet ((pub ∘ back) full.1 u) rawBase u.val (visited u).owned.val.2.2 := by
  let x := back (replayed).1
  let candidate := chosen.site x u
  obtain ⟨r,attained,_⟩ := chosen.attained x u
  have headerRead : padded (spelling (candidate.profile++DeclarationBits.spelling word) candidate.claims)
      candidate.pad=packet.bits := by
    rw [show candidate.profile=List.ofFn packet.profile from attained.copiedProfile,
      show candidate.claims=DiagonalTallyRAM.broadcast w packet.rawCounts from attained.copiedClaims,
      show candidate.pad=0 from attained.padding,cube]
    exact packet.bits_eq_emitted.symm
  have fields := chosen.sharedCubeWords (fun y j => by
    obtain ⟨r,assigned,_⟩ := chosen.attained y j
    exact ⟨previous,origin,task.cube.cables,task.cube.cells,rawBase,w,assigned.oldWords⟩) valid axes space
  have groups := F.groupMap ar label recv amount chosen.projection.groupNumber q.val
  exact F.sourceEquiv_candidateOwnedReadback task fixed source B agree q reports chosen.publication (task.lookupFrame 0)
    u candidate (chosen.projection.image (replayed).1 u) arena packet previous origin attained.oldWords headerRead
    (candidate.origin.trans base) destination size secondary endFit teamCount teamsFit le_rfl wordPos
    (chosen.commonFrame (replayed).1) space values room (fields (replayed).1) groups demand capacity digits

end TeamContraction

end BorderVNP
end Computability
end OAI
