import OAI.Computability.BorderVNP.DiagonalSignedSharedCandidate
import OAI.Computability.BorderVNP.DiagonalSignedPublishedWriter

/-! # Bare-header signed sites and the common physical frame of an admitted declaration -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM TeamContraction JointHeader Packing BorderVNP.Cube Physical LocalRow
open PackedHistoryCircuit Crossing

/-- The public information of an individual physical team on one bare header.
The retained row image, raw guard, and both executions refer to this same pin.
An admitted declaration can therefore be replayed before a joint-preparation
tuple has been selected. -/
structure CandidateSite {w R X : ℕ} (ar : CubeArena.Layout) (D : Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (word : Broadcast ar.n ar.header.d ar.header.cap) (owner : ℕ → Fin (R+1))
    (decl : LengthDeclaration ar.n ar.header.d) (group : Fin ar.header.d → Fin (R+1))
    (frame receivingBase : ℕ) (pins : Pins.Layout) (fields : Pins.ProcessorFields pins) (f : BroadcastFrame)
    (guess : ℕ → Bool) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (reg : Bank w) (mem : Memory w)
    {I : Type*} [Fintype I] (host : I → Fin ar.cells) (key : I ↪ ℕ) (sizes : I → ℕ)
    {D₀ : ℕ} {P A : Type*} {bits : P → ℕ} (N : Network D₀ P bits) (cell : N.Site → Fin ar.cells)
    (recv : A → Fin ar.cells) (amount : A → ℕ) where
  /-- Epoch and private placement on the actual chosen pin memory. -/
  epoch : Returns epochPlacement pub mac reg mem
  /-- Next header and seven-word demand-directory publication. -/
  published : Returns Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2
  /-- RAM among the two native passes, before the public table is written. -/
  middle : Memory w
  epochMemory : epoch.val.2.2=middle
  actual : published.val.2.2=Directory.ISA.publish middle (pub 0).val receivingBase (D.directory pp lp)
  empty : epoch.val.1.flatMap TeamRAM.Event.choices=[]
  /-- Cost at the pinned entry, including its returned boot and pin. -/
  used : ℕ
  /-- Measured cost of the complete frozen geometry interpreter. -/
  profileCost : ℕ
  cost : used+traceCost epoch.val.1+traceCost published.val.1 ≤ profileCost+deliveryScanTicks D.entries D.teams D.sites
  origin : (pub 0).val=frame
  sources : ProfileRouteInputs fields f pub guess published.val.2.2
  fieldLength : fields.header.length=(pub 0).val
  pointers : ∀ count, TablePointers (ar.table frame count) (readings published.val.2.2)
  space : f.Fits w (pub 0).val
  /-- The occupied rows use the common actual keys, including live zero-width entries. -/
  placement : SlottedWriter ar D pp lp pins pub middle receivingBase host key sizes
  /-- Prior machine fields and budget of this site's physical frame. -/
  old : Fin 81 → Word w
  /-- Beginning of the geometry's scratch region. -/
  fresh : ℕ
  /-- Actual number of native gates in the profile. -/
  gates : ℕ
  /-- Actual geometry output count. -/
  outputs : ℕ
  /-- Number of bits in each emitted field. -/
  width : ℕ
  /-- Offset of the striped input. -/
  off : ℕ
  /-- Length of the striped input. -/
  ell : ℕ
  /-- Base of the signed physical controls. -/
  control : ℕ
  /-- Copied geometry history. -/
  profile : List Bool
  /-- Copied report claims of the selected header. -/
  claims : List (List Bool)
  /-- Trailing header padding length. -/
  pad : ℕ
  input : PinnedRawInput (ar:=ar) (D:=D) (pp:=pp) (lp:=lp) (pub:=pub) (slotted:=middle) (base:=receivingBase)
    f old fresh gates outputs width off ell control profile claims pad word R X
  rows : PublishedRowPlacement N cell recv amount (pub 0).val published.val.2.2
  /-- Registers at the end of geometry, before private placements. -/
  geometryRegs : Bank w
  /-- The terminal frozen geometry's actual RAM. -/
  geometry : Memory w
  /-- The chronological return of the two publication passes on the terminal frozen memory. -/
  scan : Returns (.seq PrivatePlacement.program Directory.ISA.program) pub mac geometryRegs geometry
  scanState : scan.val.2=published.val.2
  scanCost : traceCost scan.val.1≤deliveryScanTicks D.entries D.teams D.sites
  dimensions : let l := LabelIndex.layout frame (readings published.val.2.2)
    l.cells=ar.cells ∧ l.cableCount=ar.cables ∧ l.deliveryCount=(D.directory pp lp).length ∧ l.labels=ar.alphabet
  /-- The real native scheduler of this admitted declaration at this own team. -/
  receipt : HeaderWriterReceipt ar D pp lp owner decl group pins f pub mac published.val.2.1 published.val.2.2

end RoutingISA.Evaluator.SignedPrep

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout Routing RoutingISA RoutingISA.Evaluator RoutingISA.Transmission
open BorderVNP.Cube Physical Tally JointHeader PackedHistoryCircuit LocalRow Crossing

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (skeleton : WireLayout (R+1) r link) (header : List Bool) (len : header.length=skeleton.header)
    (ar : CubeArena.Layout) (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (pin : Fin d → Bool) (guess : Fin (R+1) → ℕ → Bool) (dst ib hb sb : Fin (R+1) → ℕ)
    (frame receivingBase : ℕ) (owner : ℕ → Fin (R+1)) (group : Fin ar.header.d → Fin (R+1))
    (word : Broadcast ar.n ar.header.d ar.header.cap)
    (pub : HeaderExterior skeleton header → Fin (R+1) → Arg → Word w)
    (mac : HeaderExterior skeleton header → Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : HeaderExterior skeleton header → Fin (R+1) → Bank w) (mem : HeaderExterior skeleton header → Fin (R+1) → Memory w)

local notation3 (prettyPrint := false) "X" => HeaderExterior skeleton header
local notation3 (prettyPrint := false) "decl" => Prod.mk (Fin.ofNat (ar.n+1) (readCode (ar.n+1) word.1))
  (fun (p : Sym2 (Fin ar.header.d)) (j : Fin (ar.n+1)) => readCode (ar.header.cap+1) (word.2 p j))
local notation3 (prettyPrint := false) "PL" u => G.pinLayout u (ib u) (hb u) (sb u)
local notation3 (prettyPrint := false) "BF" u => G.transferFrame u skeleton.header (dst u)

set_option maxHeartbeats 3200000
set_option maxRecDepth 6000

include len in
/-- Choose the checked header's layout from its bare physical sites. Every exterior
and team is represented by a site at the actual epoch and directory memories,
independently of whether a joint-preparation prefix has previously been supplied.
All public data and paid report inputs on those sites remain accessible after relayout. -/
theorem signed_candidate_frame {α ξ : ℝ} {scale : ℕ} (fit : Diagonal.RouteTableInputs ar D α ξ scale w frame link)
    {I : Type*} [Fintype I] (host : I → Fin ar.cells) (key : I ↪ ℕ) (sizes : I → ℕ)
    {D₀ : ℕ} {P A : Type*} {bits : P → ℕ} (N : Network D₀ P bits) (cell : N.Site → Fin ar.cells)
    (recv : A → Fin ar.cells) (amount : A → ℕ)
    (site : ∀ (x : X) u, SignedPrep.CandidateSite («X»:=TeamScales.exterior ξ r scale) ar D pp lp word owner decl group
      frame receivingBase (PL u) (G.processorFields u pin x.val (ib u) (hb u) (sb u)) (BF u) (guess u) (pub x u) (mac x u) (reg x u) (mem x u)
      host key sizes N cell recv amount)
    (subRoom : ∀ u, frame+13 < ib u ∧ ib u+(PL u).count≤ar.header.header)
    (copied : ∀ x : X,ReturnedHeaders G pin x.val skeleton w) (x₀ : X)
    (processors : D.processors=r) (literal : D.literal=G.program.length+t) (teams : D.teams=R+1)
    (literalRoom : D.literal ≤ TeamScales.literal α scale) (headRoom : (skeleton.header:ℝ) ≤ r*(scale:ℝ)^(24/25:ℝ))
    (valid : declarationInRange word) :
    ∃ (wire : WireLayout (R+1) r link) (same : wire.header=skeleton.header),
      let back := (HeaderExterior.changeLayout skeleton wire same header).symm
      let W := fun (x : HeaderExterior wire header) u => (site (back x) u).receipt
      ∃ F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back),
        PreparationFrame.WriterProjection G wire ar D pp lp owner decl group frame header pin guess dst ib hb sb
          (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back) (fun x u => (site (back x) u).epoch)
          (fun x u => (site (back x) u).published) (fun x u => (W x u).endReg)
          (fun x u => (W x u).out) (fun x u => (W x u).events) (fun x u => (W x u).history) F := by
  let first := site x₀ 0
  exact signed_shared_candidate G skeleton header len ar D pp lp pin guess dst ib hb sb frame owner group word pub mac reg mem
    (fun x u => (site x u).epoch) (fun x u => (site x u).published) (fun x u => (site x u).receipt)
    (fun x u => (site x u).empty) fit (fun x u => (site x u).origin) (fun x u => (site x u).pointers _)
    (fun x u => (site x u).sources) (fun x u => (site x u).fieldLength.le.trans_eq (site x u).origin)
    subRoom (fun x u => (site x u).space) copied x₀ host key sizes first.middle receivingBase first.placement
    first.actual processors literal teams literalRoom headRoom first.old first.fresh first.gates first.outputs
    first.width first.off first.ell first.control first.profile first.claims first.pad first.input valid

end TeamContraction

end BorderVNP
end Computability
end OAI
