import OAI.Hierarchy.DescentRecordedRootSnapshot

namespace OAI
/-! # Retained exceptional operands from the original reset root run -/
namespace Hierarchy.DescentPaidResidentCount.Reset
open DescentSixParty DescentCompiler DescentSIMDLookup DescentGL DescentColonies DescentFallbackPeriod.Projected
open DescentPacking.PackedMatch.Local.Stage DescentIssuedFallbackPanel DescentSharedCableNames.Stage
open DescentSixParty.Chronology DescentResetHostSize DescentResetGates DescentPackedWalsh
open DescentSharedBookScan DescentPlainTerminal DescentPlainTerminal.Suffix DescentRelativeContacts
open DescentGroupPeerOrder DescentStageEdgeReceipt DescentRosterOrder DescentFallbackShapeTable
open DescentFallbackRankRAM DescentMixedRouter DescentPackedZip DescentPackedColony
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
private theorem packet_preserved {D cap L L' H G n r field : ℕ} (same : L'=L)
    (own : Fin H→Fin G→Fin L→ℕ) (neighbors : Fin H→Fin D→Option (Fin H))
    (signed : Fin H→Fin G→Fin L→Fin (2*cap)→Option (Live D cap))
    (rank : Fin H→Fin (DescentSharedBookScan.width r (2^n) D)→ℕ) (v : Fin H) (g : Fin G) :
    (DescentFallbackPeriod.encodePacket (DescentFallbackPeriod.inputs (field:=field) own neighbors signed rank v g)).val =
      (DescentFallbackPeriod.encodePacket (DescentFallbackPeriod.inputs (field:=field)
        (fun v g i=>own v g (Fin.cast same i)) neighbors (fun v g i=>signed v g (Fin.cast same i)) rank v g)).val :=by
  cases same
  rfl

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail H field p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset cap ctl) (pad : Fintype.card cap.V≤H)
set_option quotPrecheck false
set_option maxHeartbeats 360000
local notation "A" => cap.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "dep" => GroupStage.depthBound D n f g
local notation "cc" => (T).commonDepth
local notation "dim" => S.groupWidth k tail i+k
local notation "r" => ((Z).k-cc)
local notation "L" => 2^(dim-cc)
local notation "Y" => 2^(Z).n
variable {N K Rep M hm lowBits tiny w : ℕ}
variable (a : Receiver (cap.placement).degree (cap.placement).cap N (B.reset).n (B.reset.k-B.terminals.commonDepth) B.terminals.commonDepth H (S.groupCount i) K Rep M hm lowBits tiny field (GroupStage.depthBound D n f g) w)

variable {tagBits : ℕ} (E : EstimatorArena) (stencil : StencilBook) (old : StencilBook.Sources)
    (stencilBase splitBank hubWidth : ℕ) (peer : Ports (cap.placement).degree) (oldId : Bank) (priorCapacity : Expr)
    (load fee full total portPitch : ℕ) {graphDegree : ℕ} (board : NonlinearExpanders.Graph (B.reset).n graphDegree)
    (packet tools groupDigits batches layerBits cost : ℕ)
    (primitive : CanonicalTag (2^(B.reset).n)→Cell tagBits) (bookPage : RootPage (B.reset.k-B.terminals.commonDepth) (2^(B.reset).n))
local notation "book" => a.issuedBook E stencil old stencilBase splitBank hubWidth peer oldId priorCapacity
  load fee full total portPitch board packet tools groupDigits batches layerBits cost primitive bookPage
local notation "previous" => a.issuedSources E stencil old stencilBase splitBank hubWidth peer oldId priorCapacity
  load fee full total portPitch
variable (space : a.PreparedFits (a.issuedBook E stencil old stencilBase splitBank hubWidth peer oldId priorCapacity load fee full total portPitch board packet tools groupDigits batches layerBits cost primitive bookPage)) (mem : Memory w) (hdr : OriginalHeader B pad a (a.issuedBook E stencil old stencilBase splitBank hubWidth peer oldId priorCapacity load fee full total portPitch board packet tools groupDigits batches layerBits cost primitive bookPage) mem)
    (x : OriginalArrays B pad field)
local notation "src" => a.preparedMid book space mem
local notation "groups" => 2^cc
local notation "rank₀" => fun v j=>(ranks (a:=r) («Y»:=Y) (D:=(A).degree) ((book).common a.projectionEnd H)
  (2^dep) (dep+2) src v j).val
local notation "eql" => congrArg (fun m => 2^(m-cc)) B.keyWidth
local notation "local₀" => fun v hi (l:Fin (2^r))=>x.stencil v hi (Fin.cast eql l)
local notation "signed₀" => fun v hi (l:Fin (2^r))=>x.marks v hi (Fin.cast eql l)
local notation:max "page" s:arg t:arg => ((s,.inr t):RootPage r Y)
local notation "arena" => RootTemplates.arena (a.headerEnd book) H groups M r (Z).n (A).degree
local notation:max "bank" s:arg t:arg => (book).exceptional s t

/-- The genuine predecessor inputs determine the exceptional root cells in
both signed books. The same receipt remains valid after every protected pass
between the root publication and the funded bank. -/
theorem issued_funded_roots (observed : Memory w)
    (keep : ∀a₀,a₀<a.preparedEnd book→ observed a₀=a.preparedImage book space mem a₀)
    (low : dep+2<w)
    (reachable : ∀i,Accessible peer ((previous).tagged i) H groups M w (a.headerEnd book))
    (roster : Mounted peer x.peers src groups M)
    (localFit : ∀i,((previous).here i).Fits w (a.headerEnd book) ∧ H*chunks groups M≤((previous).here i).size)
    (signedFit : ∀i j,((previous).signed i j).Fits w (a.headerEnd book) ∧ H*chunks groups M≤((previous).signed i j).size)
    (own : ∀i,Reads ((previous).here i) (fun v g=>(local₀ v g i:Cell field)) M src)
    (tagged : ∀i,Reads ((previous).tagged i) (fun v g=>((local₀ v g i+1:ℕ):Cell field)) M src)
    (signs : ∀i j,Reads ((previous).signed i j) (fun v g=>((DescentSignedCableCodec.encode (signed₀ v g i j)).val:Cell field)) M src)
    (prior : ∀s t k,((bank s t).reads k).Fits w ((arena).middle (rootIndex r Y (page s t)).val))
    (packed : ∀s t,M*max ((bank s t).field*DescentFallbackPeriod.inputCount (A).degree (2^r) (A).cap (Z).n r)
      (bank s t).outputBits ≤ w/2) :
    ∀s t,Source (a.gatheredOperand book (page s t)) (savedInput B pad (root_snapshot B pad a book space mem hdr x)) M observed :=by
  intro s t
  have read:=a.issued_fallback_word E stencil old stencilBase splitBank hubWidth peer oldId priorCapacity load fee
    full total portPitch board packet tools groupDigits batches layerBits cost primitive bookPage space mem s t
    local₀ x.peers signed₀ low hdr.rankBits reachable roster localFit signedFit own tagged signs (prior s t) (packed s t)
  have same : savedInput B pad (root_snapshot B pad a book space mem hdr x) =
      fun v g=>DescentFallbackPeriod.encodePacket (DescentFallbackPeriod.inputs (field:=field) local₀ x.peers signed₀ rank₀ v g) :=by
    funext v g
    apply Fin.ext
    rw [saved_input_eq,root_snapshot_input]
    exact packet_preserved eql x.stencil x.peers x.marks rank₀ v g
  rw [same]
  intro pos
  exact (eval_below _ _ _ _ (a.gathered_fits book space (page s t)) keep).trans (read pos)

end
end Hierarchy.DescentPaidResidentCount.Reset

end OAI
