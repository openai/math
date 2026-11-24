import OAI.Computability.VPVNP.PairVertexSiteReport
import OAI.Computability.VPVNP.PairTreeEmissions

/-! # One native report per occurrence, from the local row proofs -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM DFS LocalHistory NetworkKernel NodeArguments TreeDecode
open CompressorRecords.SourceTransport (Reads)
open scoped Fin.CommRing

variable {geometry rootFields leaf shrink refresh : Segment} {p regs W endAddr g : ℕ}
    (A : Placement (segments geometry rootFields leaf shrink refresh) p regs)
    (M : Machine W p regs 11)
    {R : Type*} [CommRing R] {L : Type} [Fintype L] {f : L → R} {N Y : Network}

/-- The rows of each role return to the DFS header and preserve external
data. Their public read footprints and cost facts can depend on their
recorded addresses. -/
def JobGuard (m : Memory W) (allow : ℕ → Prop) (cost : VisitPath W endAddr → Prop)
    (j : VisitPath W endAddr) : Prop :=
  j.Linked M (A.core (.roleBase 0)) (A.dfsPC 3) A.dfs m ∧ after m j.trace = m ∧
    Reads allow j.trace ∧ cost j

/-- Only the individual kernel and leaf effects are inputs here. The native
preorder, monomial multiplicities, final private histogram, scratch frame,
external read footprint and physical burst result are assembled from them. -/
theorem occurrence_report (linked : Contains A M) (m : Memory W) (allow : ℕ → Prop)
    (cost : VisitPath W endAddr → Prop) (valid : List Packet → Scratch W endAddr → Prop)
    (order : Fin g ≃ L) (base grammar src : ℕ) (G offset : Word W)
    (c : TermChain R N Y) (r : ChainParsers f c) (ptr : RowPointers c) (layers : PacketLayers c)
    (P : SiteParsers f N) (input : Packets N) (leaves : N.Site → ℕ × ℕ)
    (initial : Emits valid (privateHistogram order src) (JobGuard A M m allow cost) P input (leafJobs P leaves))
    (localEffects : EmissionLayers valid (privateHistogram order src) (JobGuard A M m allow cost) c r ptr layers input)
    (v : Y.Site) (z : Y.Half v) (x : ((finalParsers c r P).witnesses v z).Choice)
    (cfg : Config W p regs) (here : cfg.pc = A.dfsPC 0) (top : ℕ) (root : Word W)
    (stack : Represents cfg.privateMem top [root]) (length : top+1=endAddr)
    (sp : cfg.reg (A.dfs 5) = (top : Word W)) (endReg : cfg.reg (A.dfs 6) = (endAddr : Word W))
    (one : cfg.reg (A.dfs 3) = 1) (control : List (Event W))
    (visits : Visits m endAddr [root]
      (((chainTrees c r ptr (fun u => leafTree (leaves u))) v).preorder.map (fun n : ℕ => (n : Word W))) control)
    (prepared : valid [finalPackets c layers input v z] (scratch endAddr cfg.privateMem))
    (geometryEnd : ∀ s, valid [] s → ResidentGeometry s G offset (src : Word W))
    (zero : ∀ l, privateHistogram order src (scratch endAddr cfg.privateMem) l = 0)
    (ctrl : Reads allow control) (cells : ∀ i : Fin g, allow (base+grammar+i.val))
    (above : endAddr ≤ src) (hsrc : src+g < 2^W) (hdst : base+grammar+g < 2^W)
    (hbase : M.publicData 4 = (base : Word W)) (hgrammar : M.publicData 5 = (grammar : Word W))
    (hg : M.publicData 9 = (g : Word W)) :
    let final := finalParsers c r P
    let semantic := vertexJobs c r ptr P leaves v z x
    let powers := fun i : Fin g => (final.witnesses v z).exponents x (order i)
    ∃ (native : List (VisitPath W endAddr)) (rep : Report W),
      Effects valid (privateHistogram order src) (JobGuard A M m allow cost)
        (scratch endAddr cfg.privateMem) [] semantic native ∧
      rep.result = some (cfg.persistent+1) ∧ choiceBits rep.events = (final.read v z).encode x ∧
      after m rep.events = Counters.addHistogram base grammar powers m ∧
      rep.events.length = control.length + (native.map fun j => j.trace.length).sum + 7*g+14 ∧
      countProbes rep.events = countProbes control + (native.map fun j => countProbes j.trace).sum + 2*g ∧
      Reads allow rep.events ∧
      ∀ extra, execute M.program (extra+rep.events.length+1) cfg m ((final.read v z).encode x) = some rep := by
  intro final semantic powers
  obtain ⟨native,paths⟩ := chain_emits valid (privateHistogram order src) (JobGuard A M m allow cost) c r ptr
    layers P input (leafJobs P leaves) initial localEffects v z x [] _ prepared
  obtain ⟨rep,result,bits,after,time,probes,reads,run⟩ :=
    vertex_report_supported A M linked final (chainTrees c r ptr (fun u => leafTree (leaves u)))
      (vertexJobs c r ptr P leaves) (vertexJobs_spec c r ptr P leaves) v z x order base grammar src G offset m
      visits native paths.realized (fun j hj => (paths.framed j hj).1) (fun j hj => (paths.framed j hj).2.1)
      cfg here top stack length sp endReg one paths.ready (geometryEnd _ paths.remaining) zero above hsrc hdst
      hbase hgrammar hg
  exact ⟨native,rep,paths,result,bits,after,time,probes,
    reads allow ctrl (fun j hj => (paths.framed j hj).2.2.1) cells,run⟩

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
