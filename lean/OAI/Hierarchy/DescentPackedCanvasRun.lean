import OAI.Hierarchy.DescentPackedCanvasSources

namespace OAI
/-! # From the old signed rows through the native reset canvas in one execution -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas
open DescentGL DescentColonies DescentSIMDLookup DescentPackedExchange DescentMeasuredWeights DescentMeasuredHeader
open DescentBaseProfile DescentPackedWalsh DescentWalshPhysical DescentPackedRectangle DescentPackedSingletonDepth
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i H HP D R M short u l b w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
  (groups : J≃Fin R) (name : V≃Fin H) (size : 2^(u+l)=R*2^k)
  (C₀ : DescentPackedFlowPublication.Layout D (2^k) (2*A.cap))
  (hosts : H≤HP) (ports : A.degree≤D)
local notation "m" => u+l
local notation "N" => HP*(m+1)+HP*D
local notation "digits0" => PackedFlow.digits groups size
local notation "pitch" => C₀.pitch
local notation "rank" => name.toEmbedding.trans (Fin.castLEEmb hosts)
local notation "header" => A.mixerHeader digits0 name
local notation "bound" => A.wire*(A.z*G.b)*A.cap
local notation "pageSize" => DescentPackedWalsh.page HP u

local notation "ns" => DescentPackedSingletonDepth.Canvas.peers hosts (header).neighbors
local notation "raw" => DescentPackedSingletonDepth.Canvas.weights hosts (header).loads
local notation "ex" => DescentPackedRectangle.Canvas.extendedPort (D:=D) hosts (neighborSlot (degree:=A.degree) name A.mutual)
local notation "realDepth" => measuredDepth ns raw A.degree k
local notation "mx" => Nat.clog 2 N

theorem from_chips (f K root first edges scratch totals lo base out dPage gPage : ℕ) (ptr flow count : Bank)
    (src mem prior : Memory w)
    (oldRoom : DescentPackedFlowPublication.Room C₀ HP R M short b w)
    (lanes : 2^l=M*2^k) (hm : 0<M) (valid : A.degree<2^short) (flowBase : flow.base=C₀.middle)
    (tokens : ∀s,DescentPackedColony.Reads (C₀.tokens s)
      (fun (v : Fin HP) g=>Padded.tokens A native S ready groups name short v g s) M mem)
    (rom : ∀(j : Fin D) x,DescentPackedZip.Static (C₀.inserts j x)
      (DescentPackedFlowRAM.insert (b:=b) (d:=short) (A.wire*(A.z*G.b)) j.val x) M mem)
    (links : DescentPackedColony.Mounted C₀.peers (Padded.roster A name hosts) mem R M)
    (idx : DescentPackedFlowReturn.Header C₀.header C₀.middle mem D HP R M)
    (table : DescentPackedZip.Static C₀.add (DescentPackedFlowPair.add (b:=b) (r:=2^k)) M mem)
    (census : ∀p : DescentSIMDLookup.Row HP R M,mem (first+(DescentSIMDLookup.row HP R M p).val)=
      ((DescentSIMDLookup.data (fun v g=>encode b (2^k) (fun x=>(A.censusValue rank groups false v g x:Cell b))) p).val:Word w))
    (fullMode : ∀v,Native.totalWeight (header).loads v<2^b) (packed : smallKey l b≤w)
    (roomTiny : root+m*span HP u l b≤C₀.first) (stages : first+(m+1)*pageSize≤totals) (endAddr : totals+HP<2^w)
    (stamped : ∀a<first,mem a=mounted HP b root ((axesList u l).map axis) src a)
    (fixed : ∀a,lo≤a→a<lo+words HP u l D→mem a=mount lo pitch f bound K HP u l D prior a)
    (geometry : lo+words HP u l D≤C₀.first) (ptrLow : ptr.base+HP≤C₀.first) (edgeLow : edges+HP*D≤C₀.first)
    (ptrRead : ∀v:Fin HP,mem (ptr.base+v.val)=((row v (fun _ : Fin u=>false)).val:Word w))
    (edgeBase : edges=C₀.peers.roster.base)
    (ptrFit : ptr.Fits w totals) (dataFit : (transformBank first HP u l).Fits w totals) (pn : HP≤ptr.size)
    (scalar : b≤w) (hRoom : HP<2^w) (dimRoom : 2*m+1<2^w) (one : 1<2^w)
    (smoothed : ∀v,(header).depth A f v≤ m)
    (oldPorts : C₀.middle+D*pitch≤first) (arena : C₀.first≤first) (prefixSpace : first+pageSize≤base)
    (safe : (layout HP D m k f bound totals edges scratch A.degree).Fits w)
    (depthBits peerBits flagBits : ℕ)
    (hs : let L:=layout HP D m k f bound totals edges scratch A.degree
      let T:=metadata (H:=HP) (u:=u) (l:=l) (D:=D) lo ⟨L.base (L.M+1),depthBits⟩ ⟨edges,peerBits⟩
      DescentMeasuredHeader.Fits T w HP m D base)
    (gs : let T:=gather (H:=HP) (u:=u) (l:=l) (D:=D) lo ⟨base,flagBits⟩ (siteBank first HP u) flow
      Room T pitch HP u l D w out)
    (priorBanks : let T:=gather (H:=HP) (u:=u) (l:=l) (D:=D) lo ⟨base,flagBits⟩ (siteBank first HP u) flow
      ∀B∈[T.kind,T.owner,T.pointer,T.sites,T.flows],B.base+B.size≤base)
    (gap : base+3*N≤dPage) (separate : dPage+N≤gPage) (extent : gPage+N≤out)
    (countLow : count.base<C₀.first) (before : count.base<base) (counted : mem count.base=(H:Word w))
    (masksFit : let T:=metadata (H:=HP) (u:=u) (l:=l) (D:=D) lo (⟨scratch,depthBits⟩:Bank) ⟨edges,peerBits⟩
      ∀B∈[T.owner,count,(⟨base+N,mx⟩:Bank),⟨base+2*N,mx⟩],B.Fits w dPage) :
    let data:=transformBank first HP u l
    let L:=layout HP D m k f bound totals edges scratch A.degree
    let T:=metadata (H:=HP) (u:=u) (l:=l) (D:=D) lo ⟨L.base (L.M+1),depthBits⟩ ⟨edges,peerBits⟩
    let C:=gather (H:=HP) (u:=u) (l:=l) (D:=D) lo ⟨base,flagBits⟩ (siteBank first HP u) flow
    let run:=(DescentPackedWalsh.code w root first HP u l b 0 (axesList u l)).seq ((tap data ptr b totals HP w).seq (L.cpu w L.M))
    let mask:=DescentPackedRectangle.Canvas.masks T.owner count ⟨base+N,mx⟩ ⟨base+2*N,mx⟩ dPage gPage HP m D w
    let right:=run.seq ((DescentPackedRectangle.code T C w base out HP u l D).seq mask)
    ∃dst : Memory w,((DescentPackedFlowPublication.procedure C₀ HP R M w).seq right).Exec mem dst
      (DescentPackedFlowPublication.duration C₀ HP R M+(DescentPackedSingletonDepth.clocks HP u l D k f bound totals edges scratch w A.degree+
        ((headerTime T HP m D+(4+100*(N*2^u)))+((4+48*N)+(4+48*N))))) ∧
       Loaded (b:=b) A name digits0 f K (loc A name digits0 f hosts ports) dPage gPage out dst ∧
       Originals (HP:=HP) (D:=D) (b:=b) A name digits0 first C₀.middle pitch dst ∧
       ∀a<C₀.first,dst a=mem a := by
  intro data L T C run mask right
  obtain ⟨priorImage,traffic,orig,held⟩:=original_sources A native S ready groups name hosts ports C₀ oldRoom
    size lanes hm valid first mem oldPorts tokens rom links idx table census
  obtain ⟨siteRow,flowRows⟩:=Originals.walsh A name digits0 first C₀.middle pitch priorImage orig
  have fixedRoot:=mounted_resident HP b root first ((axesList u l).map axis) src mem priorImage stamped
    (fun a lo hi=>held a (.inl (hi.trans_le (by simpa [axesList] using roomTiny))))
  have fr (a:ℕ) (aa:lo≤a) (ab:a<lo+words HP u l D) :=
    (held a (.inl (ab.trans_le geometry))).trans (fixed a aa ab)
  have ptrs (v:Fin HP) := (held (ptr.base+v.val) (.inl ((Nat.add_lt_add_left v.isLt _).trans_le ptrLow))).trans (ptrRead v)
  have ed (v:Fin HP) (j:Fin D) : priorImage (edges+v.val*D+j.val)=(target (Padded.roster A name hosts v j):Word w):=by
    have lt:=Nat.mul_le_mul_right D v.isLt;rw [Nat.succ_mul] at lt
    exact (held _ (.inl (by have:=j.isLt;omega))).trans (by simpa only [edgeBase,Nat.add_assoc,DescentPackedColony.target,target] using links.roster v j)
  obtain ⟨dst,stage,rect,low⟩:=prime A name digits0 hosts ports f K root first edges scratch totals lo pitch
    base out dPage gPage ptr flow count priorImage priorImage prior fullMode packed (roomTiny.trans arena)
    stages endAddr fixedRoot fr (geometry.trans arena) (ptrLow.trans arena) (edgeLow.trans arena)
    ptrs ed ptrFit dataFit pn scalar hRoom dimRoom one smoothed siteRow (by simpa only [flowBase] using flowRows)
    (by simpa only [flowBase] using oldPorts) safe depthBits peerBits flagBits hs gs priorBanks
    gap separate extent (countLow.trans_le arena) before ((held _ (.inl countLow)).trans counted) masksFit
  have measure : HP*2^u≤pageSize:=rows_le HP u
  have trueOld:=Originals.keep A name digits0 first C₀.middle pitch priorImage dst orig (fun a within=>by
    apply low
    apply lt_min
    · rcases within with h|h <;> omega
    · rcases within with h|h <;> omega) gs.width
  refine ⟨dst,Procedure.Exec.then traffic stage,rect,trueOld,?_⟩
  intro a ha
  exact (low _ (lt_min (by omega) (by omega))).trans (held _ (.inl ha))

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas

end OAI
