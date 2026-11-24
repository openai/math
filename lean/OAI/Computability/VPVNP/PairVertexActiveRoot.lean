import OAI.Computability.VPVNP.PairVertexRootFieldsReady
import OAI.Computability.VPVNP.PairVertexActiveGeometry
import OAI.Computability.VPVNP.PairTerminalGatherReadSafety
import OAI.Computability.VPVNP.PairTerminalFootprint

/-!
# The active vertex call reaches DFS with the terminal root

This prefix uses the concrete bootstrap, geometry/cache initializer and
root gather in a single installed table. The wire bits are supplied by the
shared scan. All external actions of this prefix read memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM LiveProgram PrimedInputRAM NativeOperands Compression
open TerminalSiteStart TerminalRootGather LeafSourceLoad CompressorRecords.SourceTransport
open scoped Fin.CommRing

variable (c : Constants) (degree a b : ℕ) {p r : ℕ} {leaf shrink refresh : Segment}
  (A : Placement (segments (VertexGeometry.segment c degree a b) TerminalRootGather.segment leaf shrink refresh) p r)
  {prog : UniversalMachine.Program} {B n H : ℕ} {i : Fin (2^(n^c.chainPower-1))}

local notation "W₀" => CursorBounds.wordBits B n
local notation "D₀" => CursorBounds.virtualBits B n
local notation "E₀" => roundedUp 1 4 n
local notation "g₀" => AssemblerPublic.geometry B n H

variable (Q : PrimedInputRAM.Layout (CounterPublic.spec prog c |>.lengths n i)
  n (addressWidth B n) H (CursorBounds.wordBits B n))
  (D : PrimedCounter.Data Q (n^(c.circuitExponent+5))) (M : Machine (CursorBounds.wordBits B n) p r 11)
  (m : Memory (CursorBounds.wordBits B n)) (start : Config (CursorBounds.wordBits B n) p r) {ex lanes : ℕ} (X : State ex lanes) (u : X.network.Site)
  (f : Fin (∑ j, TerminalPrefix.width X j) → Bool)

local notation "hdr" => headerWord M.publicData
local notation "N" => Fin.val (M.publicData 6)
local notation "area" => NativeFrame.fromHeader degree M.publicData hdr m
local notation "lay" => TerminalRootGather.Layout.ofHeader degree M.publicData hdr start.persistent m
local notation "packet" => VertexRootPacket.packet X lay u f
local notation "role" => m (Fin.val (hdr+14))
local notation "cache" => LeafVisit.cacheWords D D₀ E₀

/-- The linked register bank, typed root argument and private resident fields
at the first DFS instruction. Its specification uses the physical word width
and operand values directly. -/
structure ActiveRootState {S : Part → Segment} {W p r : ℕ} (A : Placement S p r) (out : Config W p r)
    (ordinal endWord roleWord : Word W) (R : LeafArena.Regions) (q : NodeArguments.Packet)
    (leafWords : Fin 10 → Word W) (fields : Fin 12 → Word W) (vals : LeafSourceLoad.Static 34 → Word W) : Prop where
  pc : out.pc = A.dfsPC 0
  persistent : out.persistent = ordinal
  one : out.reg (A.dfs 3) = 1
  top : out.reg (A.dfs 5) = endWord-1
  endReg : out.reg (A.dfs 6) = endWord
  roleOffset : out.reg (A.saved VertexImage.roleOffset) = roleWord
  histogram : out.reg (A.saved histBase) = (R.histBase : Word W)
  fits : q.Fits R.arguments W endWord.val
  stored : q.Stored R.arguments (DFS.scratch endWord.val out.privateMem)
  resident : VertexRootFields.Resident R endWord.val (endWord.val-1) [(q.node : Word W)]
    leafWords fields vals out.privateMem

attribute [local irreducible] NativeOperands.capacity NativeOperands.saved VertexGeometry.segment
  CursorBounds.wordBits CursorBounds.virtualBits TerminalRootGather.segment

theorem active_root (hb : 0 < b) (hB : 1 ≤ B) (hn : 3 ≤ n) (hH : H = 2^roundedUp a b n)
    (fit : PairNativeGeometry.Fits a b n W₀) (hp : Q.program = prog) (hbase : Q.scratchBase = 2^D₀)
    (hf : D.Fits) (hroot : D.root.val = 0) (hw : 2 ≤ W₀) (hc : 2^D₀*2^E₀ < 2^W₀)
    (pub : M.publicData = Pieces.word g₀ (CounterPublic.actualPrefix prog) ∘ StageOperands.pair c)
    (link : Contains A M) (here : start.pc = A.entry .bootstrap) (fresh : start.privateMem = fun _ => 0)
    (active : start.persistent < m (hdr+7).val) (rootPos : 0 < (lay).root)
    (rootBound : (lay).root < (area).nodes) (room : (area).cacheBase+38 ≤ 2^W₀)
    (num : TerminalGatherGeometry.Numbering X lay u) (rows : TerminalGatherGeometry.Rows X lay m)
    (bits : ∀ j, m ((lay).wires+j.val) = PrivateFields.bitValue W₀ (f j))
    (gatherFit : (lay).Fits m) (deg : 2^ex ≤ degree) (width : X.maxWireWidth ≤ N)
    (headerFit : (headerWord M.publicData).val + 31 < 2^W₀)
    (heads : ∀ h ∈ [(lay).incomingHead,(lay).widthHead,(lay).prefixHead], h+TerminalPrefix.arcCount X ≤ (hdr).val)
    (wires : (lay).wires+X.totalWidth ≤ (hdr).val) :
    ∃ t ≤ work (NativeCache.args c) a b g₀+76, ∃ out : Config W₀ p r, ∃ es : List (Event W₀),
      ActiveRootState A out start.persistent (M.publicData 6) role area packet
        (NativeFrame.leafWords degree M.publicData hdr role m) (NativeFrame.fields degree M.publicData hdr role m) cache ∧
      es.length = t+degree+187+(15+21*(2^ex)+5*(packet).bits.length) ∧
      countProbes es = 15+(5*(2^ex)+(packet).bits.length) ∧
      choiceBits es = [] ∧ after m es = m ∧ Reads (TerminalLink.workerCell hdr) es ∧
      Prefix M m start es out := by
  have hnval : N = n := by rw [pub]; exact Nat.mod_eq_of_lt (PrimedInputRAM.Opcodes.pubNat_lt Q hf.assembler 1)
  have hnpos : 0 < N := by rw [hnval]; omega
  have before : N < NativeFrame.frameBase area := by
    have h₁ : N < (lay).dest := Nat.lt_add_of_pos_right (Nat.mul_pos rootPos (Nat.succ_pos _))
    have h₂ := (area).node_before rootBound
    change (lay).dest+(area).arguments.stride ≤ (area).histBase at h₂
    change N < (area).histBase+(area).histWords; omega
  obtain ⟨t,ht,boot,geo,persist,booted,bootMem,prepared,headRun⟩ :=
    active_geometry c degree a b A Q D hb hB hn hH fit hp hbase hf hroot hw hc M pub link m start here active before room
  have support := TerminalGatherGeometry.worker_readable num rows hdr headerFit heads wires
  obtain ⟨out,tail,done,st,dfs,saved,_,placed,cost,readTail,runTail⟩ :=
    image_run_reads A rfl M link lay m gatherFit geo prepared.pc (VertexRootFields.saved booted prepared)
      (Fin.cast_val_eq_self _).symm (VertexRootFields.stride booted prepared) _ support
  obtain ⟨packetFit,stored,resident⟩ := VertexRootFields.ready_of_placed f booted prepared (fresh ▸ bootMem)
    num rows bits gatherFit hnpos rootPos rootBound deg width room out placed
  have hrole : boot.reg (A.saved VertexImage.roleOffset) = role := booted.roleOffset
  have hhead : boot.reg (A.saved header) = hdr := booted.header
  rw [hrole] at resident
  have readyState : ActiveRootState A out start.persistent (M.publicData 6) role area packet
        (NativeFrame.leafWords degree M.publicData hdr role m) (NativeFrame.fields degree M.publicData hdr role m) cache := by
    refine ⟨done,st.trans (prepared.persistent.trans persist),(dfs 3).trans ((prepared.dfs 3).trans booted.one),
      (dfs 5).trans ((prepared.dfs 5).trans booted.top),(dfs 6).trans ((prepared.dfs 6).trans booted.stackEnd),
      (saved _).trans ((prepared.saved _ (by decide)).trans hrole),?_,packetFit,stored,resident⟩
    exact (saved histBase).trans (hhead ▸ prepared.hist)
  let pre := startTrace m hdr ++ (NativeFrame.events degree hdr m ++ List.replicate (t+2) .tick)
  obtain ⟨hTime,hProbe,hBits,hMem⟩ := active_geometry_cost degree t m hdr
  have hread := active_geometry_reads m hdr degree t headerFit
  have len : ((lay).packet m).length = (packet).bits.length := by
    rw [TerminalGatherGeometry.packet_eq num rows f bits,List.length_map]; rfl
  have head : Prefix M m start pre geo := headRun
  refine ⟨t,ht,out,pre++tail,readyState,?_,?_,?_,?_,TerminalFootprint.reads_append hread readTail,head.trans runTail⟩
  · rw [List.length_append,hTime,cost.time,num.degree,len]
  · rw [countProbes_append,hProbe,cost.probes,num.degree,len]
  · rw [Flow.choiceBits_append,hBits,cost.bits]; rfl
  · rw [after,List.foldl_append]
    change after (after m pre) tail = m
    rw [hMem,cost.after_eq]

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
