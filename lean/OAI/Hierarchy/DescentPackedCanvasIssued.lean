import OAI.Hierarchy.DescentPackedCanvasRun
import OAI.Hierarchy.DescentPackedCanvasProgram
import OAI.Hierarchy.DescentPackedCanvasCopy

namespace OAI
/-! # Discharge every address aperture of the chosen reset producer at its concrete dates -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas
open DescentGL DescentColonies DescentCompiler DescentSIMDLookup DescentPackedExchange DescentMeasuredWeights
open DescentBaseProfile DescentPackedWalsh DescentWalshPhysical DescentPackedRectangle DescentPackedSingletonDepth
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i H HP D R M short u l b w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : AtomSchedule) (ready : A.StateBounds S i)
  (groups : J≃Fin R) (name : V≃Fin H) (size : 2^(u+l)=R*2^k)
  (C : DescentPackedFlowPublication.Layout D (2^k) (2*A.cap)) (hosts : H≤HP) (ports : A.degree≤D)
local notation "m" => u+l
local notation "N" => HP*(m+1)+HP*D
local notation "xy" => PackedFlow.digits groups size
local notation "hdr" => A.mixerHeader xy name
local notation "rank" => name.toEmbedding.trans (Fin.castLEEmb hosts)
local notation "B" => A.wire*(A.z*G.b)*A.cap

def atWorld (floor f K : ℕ) : Placement :=
  ⟨⟨HP,D,u,l,b,floor,C.pitch,f,B,K⟩,C.middle⟩

variable (floor f K : ℕ)
local notation "p" => atWorld (HP:=HP) (u:=u) (l:=l) (b:=b) A C floor f K

theorem installed (out : ℕ) (count : Bank) (mem : Memory w)
    (room : DescentPackedFlowPublication.Room C HP R M short b w)
    (lanes : 2^l=M*2^k) (hm : 0<M) (valid : A.degree<2^short)
    (tokens : ∀s,DescentPackedColony.Reads (C.tokens s)
      (fun (v:Fin HP) g=>Padded.tokens A native S ready groups name short v g s) M mem)
    (rom : ∀(j : Fin D) x,DescentPackedZip.Static (C.inserts j x)
      (DescentPackedFlowRAM.insert (b:=b) (d:=short) (A.wire*(A.z*G.b)) j.val x) M mem)
    (links : DescentPackedColony.Mounted C.peers (Padded.roster A name hosts) mem R M)
    (idx : DescentPackedFlowReturn.Header C.header C.middle mem D HP R M)
    (table : DescentPackedZip.Static C.add (DescentPackedFlowPair.add (b:=b) (r:=2^k)) M mem)
    (census : ∀x : Row HP R M,mem ((p).first+(row HP R M x).val)=
      ((data (fun v g=>encode b (2^k) (fun z=>(A.censusValue rank groups false v g z:Cell b))) x).val:Word w))
    (full : ∀v,Native.totalWeight (hdr).loads v<2^b) (packed : smallKey l b≤w)
    (stat : (p).geo.Resident mem) (early : (p).geo.stop≤C.first)
    (oldcount : count.base+count.size≤C.first) (readCount : mem count.base=(H:Word w))
    (depth : ∀v,(hdr).depth A f v≤ m)
    (wide : HP<2^w) (dim : 2*m+1<2^w) (smooth : decayExponent A.degree<2^w) (bitsFit : b≤w)
    (reached : (p).endAddress≤out) (word : out+N*2^u<2^w) :
    ∃dst,((p).prepare C count k A.degree R M w out).Exec mem dst ((p).prepareTicks C k A.degree R M w) ∧
      Loaded (b:=b) A name xy f K (loc A name xy f hosts ports) (p).depthPage (p).gainPage out dst ∧
      Originals (b:=b) (HP:=HP) (D:=D) A name xy (p).first C.middle C.pitch dst ∧
      ∀a<C.first,dst a=mem a := by
  have cuts : C.middle+D*C.pitch≤(p).first ∧ (p).first+(m+1)*page HP u≤(p).totals ∧
      (p).totals+HP≤(p).scratch ∧ (p).scratch+(m+2)*Placement.pad HP≤(p).headerBase ∧
      (p).headerBase+3*N≤(p).depthPage ∧ (p).depthPage+N≤(p).gainPage ∧
      (p).gainPage+N≤(p).endAddress := (p).stops
  have final_ : (p).endAddress<2^w:=reached.trans_lt ((Nat.le_add_right ..).trans_lt word)
  have now:C.first≤C.middle:=Nat.le_add_right ..
  have placed : (p).geo.stop≤(p).middle:=early.trans now
  have mid : C.middle≤(p).first:=Nat.le_add_right ..
  have prev : C.first≤(p).first:=now.trans mid
  have guarded : (p).first+page HP u≤(p).headerBase:=by
    have pp:page HP u≤(m+1)*page HP u:=by rw [Nat.succ_mul];omega
    omega
  have prior : count.base+count.size≤(p).headerBase:=oldcount.trans (prev.trans (by omega))
  have positive:0<count.size:=Nat.two_pow_pos _
  have rowCount:=original_chunks size lanes hm
  have laneWidth:HP*2^u≤C.pitch:=by simpa only [rowCount] using room.pitch
  obtain ⟨ptr,data_,rows⟩:=(p).tap_rooms placed final_
  have hf:=(p).header_room placed C.peers.roster.base (by have:=room.nearBelow;omega) final_
  have stage_:=(p).measured_room C.peers.roster.base A.degree k (room.nearBelow.trans prev) final_ smooth (by change u+l<2^w; omega)
  have runner:=from_chips A native S ready groups name size C hosts ports f K floor (p).first C.peers.roster.base
    (p).scratch (p).totals (p).geo.meta (p).headerBase out (p).depthPage (p).gainPage (p).zeroPtr (p).peers count
    mem mem (fun _=>0) room lanes hm valid rfl tokens rom links idx table census full packed
    (show floor+m*span HP u l b≤C.first from (show (p).geo.meta≤(p).geo.stop from
      (Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans early)
    cuts.2.1 (by omega) (fun a _=>stat.walsh a) (fun a lo hi=>stat.sparse a lo hi)
    ((show (p).geo.pointers≤(p).geo.stop from Nat.le_add_right ..).trans early) early room.nearBelow stat.keys rfl
    ptr data_ rows bitsFit wide dim (by omega) depth cuts.1 prev guarded stage_
    (Nat.clog 2 HP) (Nat.clog 2 (HP*D)) (Nat.clog 2 N) hf
    ((p).gather_room placed laneWidth out reached word) ((p).predecessors placed) cuts.2.2.2.2.1
    cuts.2.2.2.2.2.1 (cuts.2.2.2.2.2.2.trans reached) (by omega) (by omega) readCount
    ((p).masks_room placed count prior final_ _ _)
  exact runner

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas

end OAI
