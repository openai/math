import OAI.Hierarchy.DescentPackedCanvasStaging
import OAI.Hierarchy.DescentPackedCanvasIssued

namespace OAI
/-! # The public-dimension reset consumes the previous census and signed port fields in situ -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas.Setup
open DescentGL DescentColonies DescentCompiler DescentSIMDLookup DescentPackedExchange DescentMeasuredWeights
open DescentPackedColony DescentBaseProfile DescentPackedWalsh DescentWalshPhysical
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i H HP D R M short u l b w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : AtomSchedule) (ready : A.StateBounds S i)
  (groups : J≃Fin R) (name : V≃Fin H) (size : 2^(u+l)=R*2^k)
  (tokens : Tokens k (2*A.cap)) (roster src count : Bank) (hosts : H≤HP) (ports : A.degree≤D)
  (floor f K : ℕ)
local notation "m" => u+l
local notation "N" => HP*(m+1)+HP*D
local notation "xy" => PackedFlow.digits groups size
local notation "hdr" => A.mixerHeader xy name
local notation "rank" => name.toEmbedding.trans (Fin.castLEEmb hosts)
local notation "grain" => A.wire*(A.z*G.b)
local notation "B" => grain*A.cap
local notation "n" => HP*chunks R M
local notation "C" => core tokens roster HP D u l b short M floor f B K grain
local notation "p" => plan tokens roster HP D u l b short M floor f B K grain
local notation "srcRows" => (fun v g=>encode b (2^k) (fun z=>(A.censusValue rank groups false v g z:Cell b)))

theorem emitted (out : ℕ) (mem : Memory w) (lanes : 2^l=M*2^k) (hm : 0<M) (valid : A.degree<2^short)
    (safe : src.base+src.size≤floor) (capacity : n≤ src.size) (raw : Reads src srcRows M mem)
    (old : ∀t,(tokens t).base+(tokens t).size≤floor ∧ n≤(tokens t).size)
    (inputs : ∀t, Reads (tokens t) (fun (v:Fin HP) g=>Padded.tokens A native S ready groups name short v g t) M mem)
    (prior : roster.base+roster.size≤floor) (slots : HP*D≤roster.size)
    (ranks : ∀v:Fin HP,∀j:Fin D,mem (roster.base+(v.val*D+j.val))=(DescentPackedColony.target (Padded.roster A name hosts v j):Word w))
    (lowCount : count.base+count.size≤floor) (observed : mem count.base=(H:Word w))
    (full : ∀v,Native.totalWeight (hdr).loads v<2^b) (packed : smallKey l b≤w) (depth : ∀v,(hdr).depth A f v≤ m)
    (wide : HP<2^w) (dim : 2*m+1<2^w) (smooth : decayExponent A.degree<2^w) (bitsFit : b≤w)
    (reached : (p).endAddress≤out) (word : out+N*2^u<2^w) :
    ∃dst,((prep tokens roster HP D u l b short M floor f B K grain src R w).seq
      ((p).prepare C count k A.degree R M w out)).Exec mem dst
      (ticks HP D u l b short M floor f B K k R+(p).prepareTicks C k A.degree R M w) ∧
      Loaded (b:=b) A name xy f K (loc A name xy f hosts ports) (p).depthPage (p).gainPage out dst ∧
      Originals (HP:=HP) (D:=D) (b:=b) A name xy (p).first (C).middle (C).pitch dst ∧
      ∀z<floor,dst z=mem z := by
  have areas_ := areas tokens roster HP D u l b short M floor f B K grain
  obtain ⟨mid,staged,h,lo⟩:=stage tokens roster src count floor f B K grain H (Padded.roster A name hosts)
    srcRows (Padded.tokens A native S ready groups name short) mem size lanes hm safe capacity raw old inputs prior slots
    ranks lowCount observed (reached.trans_lt ((Nat.le_add_right ..).trans_lt word))
  obtain ⟨dst,ran,loaded,originals,«protected»⟩:=installed A native S ready groups name size C hosts ports floor f K
    out count mid h.room lanes hm valid h.tokens h.insert h.ports h.range h.added h.census full packed h.retained
    areas_.2.1 ((lowCount.trans areas_.1).trans areas_.2.1) h.countRead depth wide dim smooth bitsFit reached word
  exact ⟨dst,Procedure.Exec.then staged ran,loaded,originals,fun a ha=>
    («protected» _ ((ha.trans_le areas_.1).trans_le areas_.2.1)).trans (lo _ ha)⟩

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas.Setup

end OAI
