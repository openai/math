import OAI.Computability.BorderVNP.DiagonalCommonHeaderExtent
import OAI.Computability.BorderVNP.DiagonalSignedReferenceCalibration
import OAI.Computability.BorderVNP.DiagonalSignedReferenceFrame
import OAI.Computability.BorderVNP.DiagonalSignedWriterReceipt

/-! # Preparing the true physical rows of one admissible signed declaration -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open BorderVNP.Cube Physical Tally JointHeader PackedHistoryCircuit LocalRow

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (skeleton : WireLayout (R+1) r link) (header : List Bool) (len : header.length=skeleton.header)
    (ar : CubeArena.Layout) (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (pin : Fin d → Bool) (guess : Fin (R+1) → ℕ → Bool) (dst ib hb sb : Fin (R+1) → ℕ)
    (frame : ℕ) (owner : ℕ → Fin (R+1)) (group : Fin ar.header.d → Fin (R+1))
    (word : Broadcast ar.n ar.header.d ar.header.cap)

local notation3 (prettyPrint := false) "X" => HeaderExterior skeleton header
local notation3 (prettyPrint := false) "decl" => Prod.mk (Fin.ofNat (ar.n+1) (readCode (ar.n+1) word.1))
  (fun (p : Sym2 (Fin ar.header.d)) (j : Fin (ar.n+1)) => readCode (ar.header.cap+1) (word.2 p j))
local notation3 (prettyPrint := false) "tab" => ar.table frame ((D.directory pp lp).length+ar.header.d.choose 2)
local notation3 (prettyPrint := false) "PL" u => G.pinLayout u (ib u) (hb u) (sb u)
local notation3 (prettyPrint := false) "BF" u => G.transferFrame u skeleton.header (dst u)

variable (pub : HeaderExterior skeleton header → Fin (R+1) → Arg → Word w)
    (mac : HeaderExterior skeleton header → Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : HeaderExterior skeleton header → Fin (R+1) → Bank w) (mem : HeaderExterior skeleton header → Fin (R+1) → Memory w)
    (epoch : ∀ x u, Returns epochPlacement (pub x u) (mac x u) (reg x u) (mem x u))
    (published : ∀ x u, Returns Packing.Directory.ISA.program (pub x u) (mac x u)
      (epoch x u).val.2.1 (epoch x u).val.2.2)

/-- Widening the two route legs preserves the exact preceding header-copy
returns, including their original stream and final RAM. -/
def ReturnedHeaders.relayout {a b : WireLayout (R+1) r link} (eqn : b.header=a.header)
    {ext : Exterior R r link → Bool} (h : ReturnedHeaders G pin ext a w) : ReturnedHeaders G pin ext b w :=
  { h with resident := by simpa only [eqn] using h.resident
           room := by simpa only [eqn] using h.room }

set_option maxHeartbeats 3500000
set_option maxRecDepth 6000

include len in
/-- A single static allocation computed from the reference return serves every
exterior reading the same raw header. Each attached physical receipt is the
one executed at that exterior and team by the native directory and writer. -/
theorem signed_shared_candidate
    (received : ∀ (x : X) u, SignedPrep.HeaderWriterReceipt ar D pp lp owner decl group (PL u) (BF u)
      (pub x u) (mac x u) (published x u).val.2.1 (published x u).val.2.2)
    (empty : ∀ x u, (epoch x u).val.1.flatMap TeamRAM.Event.choices=[])
    {α ξ : ℝ} {scale : ℕ} (fit : Diagonal.RouteTableInputs ar D α ξ scale w frame link)
    (base : ∀ x u,(pub x u 0).val=frame) (pointers : ∀ x u, TablePointers tab (readings (published x u).val.2.2))
    (sources : ∀ (x : X) u, ProfileRouteInputs (G.processorFields u pin x.val (ib u) (hb u) (sb u))
      (BF u) (pub x u) (guess u) (published x u).val.2.2)
    (inputRoom : ∀ (x : X) u, (G.processorFields u pin x.val (ib u) (hb u) (sb u)).header.length ≤ frame)
    (subRoom : ∀ u, frame+13 < ib u ∧ ib u+(PL u).count ≤ ar.header.header)
    (frameFit : ∀ x u, (BF u).Fits w (pub x u 0).val)
    (copied : ∀ x : X,ReturnedHeaders G pin x.val skeleton w)
    (x₀ : X) {I : Type*} [Fintype I] (cell : I → Fin ar.cells) (id : I ↪ ℕ) (widths : I → ℕ)
    (slotted : Memory w) (dest : ℕ) (P : SlottedWriter ar D pp lp (PL 0) (pub x₀ 0) slotted dest cell id widths)
    (start : (published x₀ 0).val.2.2 = Packing.Directory.ISA.publish slotted (pub x₀ 0 0).val dest (D.directory pp lp))
    (processors : D.processors=r) (literal : D.literal=G.program.length+t) (sourceTeams : D.teams=R+1)
    (literalRoom : D.literal ≤ TeamScales.literal α scale) (headerRoom : (skeleton.header:ℝ) ≤ r*(scale:ℝ)^(24/25:ℝ))
    (old : Fin 81 → Word w) (fresh gates outputs bitWidth off ell controls : ℕ) (profile : List Bool)
    (claims : List (List Bool)) (pad : ℕ)
    (room : SignedPrep.PinnedRawInput (ar:=ar) (D:=D) (pp:=pp) (lp:=lp) (pub:=pub x₀ 0) (slotted:=slotted)
      (base:=dest) (BF 0) old fresh gates outputs bitWidth off ell controls profile claims pad word R (TeamScales.exterior ξ r scale))
    (valid : declarationInRange word) :
    ∃ (wire : WireLayout (R+1) r link) (same : wire.header=skeleton.header),
      let back := (HeaderExterior.changeLayout skeleton wire same header).symm
      ∃ F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back),
        PreparationFrame.WriterProjection G wire ar D pp lp owner decl group frame header pin guess dst ib hb sb
          (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back) (fun x u => epoch (back x) u)
          (fun x u => published (back x) u) (fun x u => (received (back x) u).endReg)
          (fun x u => (received (back x) u).out) (fun x u => (received (back x) u).events)
          (fun x u => (received (back x) u).history) F := by
  let H := fun u => (received x₀ u).history
  let label := (received x₀ 0).labeling
  obtain ⟨wire,same,calibrated⟩ := signed_reference_writer_layout fit H (base x₀) (pointers x₀)
    (sources x₀) (inputRoom x₀) subRoom (frameFit x₀) cell id widths slotted dest P start processors literal sourceTeams
    literalRoom headerRoom old fresh gates outputs bitWidth off ell controls profile claims pad word room owner group
    valid label.val.2.2 label.property (fun c => by rw [←base x₀ 0]; exact (received x₀ 0).owners c)
    (by funext j; rw [←base x₀ 0]; exact (received x₀ 0).groups j) (fun u => (received x₀ u).done)
  refine ⟨wire,same,?_⟩
  let back := (HeaderExterior.changeLayout skeleton wire same header).symm
  let e := fun (x : HeaderExterior wire header) u => epoch (back x) u
  let p := fun (x : HeaderExterior wire header) u => published (back x) u
  let A := fun (x : HeaderExterior wire header) u => received (back x) u
  have source (x : HeaderExterior wire header) u : ProfileRouteInputs
      (G.processorFields u pin x.val (ib u) (hb u) (sb u)) (G.transferFrame u wire.header (dst u))
      (pub (back x) u) (guess u) (p x u).val.2.2 := by rw [same]; exact sources (back x) u
  have room' (x : HeaderExterior wire header) u : (G.transferFrame u wire.header (dst u)).Fits w (pub (back x) u 0).val := by
    rw [same]; exact frameFit (back x) u
  let hdrs := fun x : HeaderExterior wire header => (copied (back x)).relayout G pin same
  let F := PreparationFrame.ofReferenceWriters G wire ar D pp lp owner decl group frame header (len.trans same.symm)
    pin guess dst ib hb sb (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back) e p (fun x u => (A x u).endReg)
    (fun x u => (A x u).out) (fun x u => (A x u).events) (fun x u => (A x u).history)
    (fun x => empty (back x)) (fun x u => (A x u).done) fit room.teamArena.symm calibrated (fun x => base (back x))
    (fun x => pointers (back x)) source (fun x => inputRoom (back x)) subRoom room' cell id widths P.placement
    P.destinations P.slabs processors literal hdrs
  exact ⟨F, PreparationFrame.reference_sources G wire ar D pp lp owner decl group frame header (len.trans same.symm)
    pin guess dst ib hb sb (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back) e p (fun x u => (A x u).endReg)
    (fun x u => (A x u).out) (fun x u => (A x u).events) (fun x u => (A x u).history)
    (fun x => empty (back x)) (fun x u => (A x u).done) fit room.teamArena.symm calibrated (fun x => base (back x))
    (fun x => pointers (back x)) source (fun x => inputRoom (back x)) subRoom room' cell id widths P.placement
    P.destinations P.slabs processors literal hdrs⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
