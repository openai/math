import OAI.Hierarchy.DescentPackedCanvasProfile
import OAI.Hierarchy.DescentPackedResetPriming
import OAI.Hierarchy.DescentPackedCanvasPublication

namespace OAI
/-! # The authentic measured estimator emitter on one fixed public RAM canvas -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas
open DescentGL DescentColonies DescentSIMDLookup DescentPackedExchange DescentMeasuredWeights DescentMeasuredHeader
open DescentBaseProfile DescentPackedWalsh DescentWalshPhysical DescentPackedRectangle DescentPackedSingletonDepth
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k H HP D u l b w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W G q ε J V k) (name : V≃Fin H) (digits : Block (u+l)≃J×Block k)
  (hosts : H≤HP) (ports : A.degree≤D)
local notation "m" => u+l
local notation "N" => HP*(m+1)+HP*D
local notation "header" => A.mixerHeader digits name
local notation "bound" => A.wire*(A.z*G.b)*A.cap
local notation "pageSize" => DescentPackedWalsh.page HP u

local notation "ns" => DescentPackedSingletonDepth.Canvas.peers hosts (GroupStage.MixerHeader.neighbors (A.mixerHeader digits name))
local notation "raw" => DescentPackedSingletonDepth.Canvas.weights hosts (GroupStage.MixerHeader.loads (A.mixerHeader digits name))
local notation "ex" => DescentPackedRectangle.Canvas.extendedPort (D:=D) hosts (neighborSlot (degree:=A.degree) name A.mutual)
local notation "realDepth" => measuredDepth ns raw A.degree k
local notation "mx" => Nat.clog 2 N

theorem prime (f K root first edges scratch totals lo pitch base out dPage gPage : ℕ) (ptr flow count : Bank)
    (src mem prior : Memory w)
    (fullMode : ∀v,Native.totalWeight (header).loads v<2^b) (packed : smallKey l b≤w)
    (roomTiny : root+m*span HP u l b≤first) (stages : first+(m+1)*pageSize≤totals) (endAddr : totals+HP<2^w)
    (stamped : ∀a<first,mem a=mounted HP b root ((axesList u l).map axis) src a)
    (fixed : ∀a,lo≤a→a<lo+words HP u l D→mem a=mount lo pitch f bound K HP u l D prior a)
    (geometry : lo+words HP u l D≤first) (ptrLow : ptr.base+HP≤first) (edgeLow : edges+HP*D≤first)
    (ptrRead : ∀v:Fin HP,mem (ptr.base+v.val)=((row v (fun _ : Fin u=>false)).val:Word w))
    (edgeRead : ∀v:Fin HP,∀j:Fin D,mem (edges+v.val*D+j.val)=
      (target (Padded.roster A name hosts v j):Word w))
    (ptrFit : ptr.Fits w totals) (dataFit : (transformBank first HP u l).Fits w totals) (pn : HP≤ptr.size)
    (scalar : b≤w) (hRoom : HP<2^w) (dimRoom : 2*m+1<2^w) (one : 1<2^w)
    (smoothed : ∀v,(header).depth A f v≤ m)
    (site : Installed (H:=HP) first (fun v=>shaped (fun z=>(Padded.load A name digits v
      (address m ((coordinates _).symm z)):Cell b))) mem)
    (traffic : ∀j:Fin D,Installed (H:=HP) (flow.base+j.val*pitch) (fun v=>shaped (fun z=>
      (Padded.flow A name digits j v (address m ((coordinates _).symm z)):Cell b))) mem)
    (oldPorts : flow.base+D*pitch≤first)
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
    (countLow : count.base<first) (before : count.base<base) (counted : mem count.base=(H:Word w))
    (masksFit : let T:=metadata (H:=HP) (u:=u) (l:=l) (D:=D) lo (⟨scratch,depthBits⟩:Bank) ⟨edges,peerBits⟩
      ∀B∈[T.owner,count,(⟨base+N,mx⟩:Bank),⟨base+2*N,mx⟩],B.Fits w dPage) :
    let data:=transformBank first HP u l
    let L:=layout HP D m k f bound totals edges scratch A.degree
    let T:=metadata (H:=HP) (u:=u) (l:=l) (D:=D) lo ⟨L.base (L.M+1),depthBits⟩ ⟨edges,peerBits⟩
    let C:=gather (H:=HP) (u:=u) (l:=l) (D:=D) lo ⟨base,flagBits⟩ (siteBank first HP u) flow
    let run:=(DescentPackedWalsh.code w root first HP u l b 0 (axesList u l)).seq ((tap data ptr b totals HP w).seq (L.cpu w L.M))
    let mask:=DescentPackedRectangle.Canvas.masks T.owner count ⟨base+N,mx⟩ ⟨base+2*N,mx⟩ dPage gPage HP m D w
    ∃dst : Memory w,(run.seq ((DescentPackedRectangle.code T C w base out HP u l D).seq mask)).Exec mem dst
      (DescentPackedSingletonDepth.clocks HP u l D k f bound totals edges scratch w A.degree+
        ((headerTime T HP m D+(4+100*(N*2^u)))+((4+48*N)+(4+48*N)))) ∧
       Loaded (b:=b) A name digits f K (loc A name digits f hosts ports) dPage gPage out dst ∧
       ∀a< min (first+pageSize) base,dst a=mem a := by
  intro data L T C run mask
  have readEdges (v:Fin HP) (j:Fin D) :
      mem (edges+v.val*D+j.val)=(DepthRAM.number ((ns[v.val])[j.val]?):Word w) := by
    rw [edgeRead,roster_eq,roster_row A name digits hosts]
    rfl
  have old : Installed (H:=HP) first (fun v=>shaped (fun z=>((raw[v.val])[(address m ((coordinates _).symm z)).val]:Cell b))) mem := by
    simpa only [old_weight A name digits hosts] using site
  obtain ⟨mid,ran,actual,retain⟩:=depths_at root first ptr D A.degree k f bound totals edges scratch src mem raw ns
    (DescentPackedSingletonDepth.Canvas.room hosts (header).loads fullMode) packed roomTiny stages endAddr stamped old
    safe ptrFit dataFit pn scalar ptrLow edgeLow ptrRead readEdges
    (DescentPackedSingletonDepth.Canvas.degree hosts (header).neighbors (header).degree ports)
  have static (a : ℕ) (ha : lo≤a) (hb : a<lo+words HP u l D) := (retain a
    ((hb.trans_le geometry).trans_le (Nat.le_add_right ..))).trans (fixed a ha hb)
  have dr (v:Fin HP):mid (L.base (L.M+1)+v.val)=(realDepth f bound v:Word w):=actual v
  have nr (p:Port HP D):mid (edges+(slot HP D p).val)=(target (ex p):Word w):=by
    rcases p with ⟨v,j⟩
    have lim:=Nat.mul_le_mul_right D v.isLt;rw [Nat.succ_mul] at lim
    have addr : (slot HP D (v,j)).val=v.val*D+j.val := by simp [slot,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
    rw [addr,←Nat.add_assoc,retain _ (by have:=j.isLt;omega),edgeRead,roster_eq]
  obtain ⟨lit,«public»⟩:=DescentPackedRectangle.retained lo pitch f bound K (⟨base,flagBits⟩:Bank) (siteBank first HP u) flow
    ⟨L.base (L.M+1),depthBits⟩ ⟨edges,peerBits⟩ prior mid (realDepth f bound) _ static dr nr
  have sRead : Installed (H:=HP) C.sites.base (fun v=>shaped (fun z=>(Padded.load A name digits v
      (address m ((coordinates _).symm z)):Cell b))) mid := by
    intro v p;exact (retain _ (Nat.add_lt_add_left ((row v p).isLt.trans_le (rows_le HP u)) _)).trans (site v p)
  have fRead (j:Fin D) : Installed (H:=HP) (C.flows.base+j.val*pitch) (fun v=>shaped (fun z=>
      (Padded.flow A name digits j v (address m ((coordinates _).symm z)):Cell b))) mid := by
    intro v p
    have small:=(row v p).isLt.trans_le gs.width
    have end_:=Nat.mul_le_mul_right pitch j.isLt;rw [Nat.succ_mul] at end_
    exact (retain _ (by change flow.base+j.val*pitch+_ <first+_;omega)).trans (traffic j v p)
  change DescentMeasuredHeader.Fits T w HP m D base at hs
  have just (z:Bank) (hit:z∈[T.owner,(⟨base+N,mx⟩:Bank),⟨base+2*N,mx⟩]) : N≤z.size:=by
    rcases List.mem_cons.mp hit with rfl|tail
    · exact hs.fixed _ (by simp [Tape.fixed])
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at tail
      rcases tail with rfl|rfl <;> exact Nat.le_pow_clog (by decide) _
  have present : mid count.base=(H:Word w):=(retain _ (countLow.trans_le (Nat.le_add_right ..))).trans counted
  obtain ⟨dst,write,rect,frame⟩:=publish A name digits hosts ports f K T C count ⟨base+N,mx⟩ ⟨base+2*N,mx⟩
    base pitch out dPage gPage mid gs hs rfl rfl rfl priorBanks gap separate extent masksFit just before present
    hRoom dimRoom one (realDepth f bound) (fun v => DescentPackedSingletonDepth.Canvas.depth_le ns raw A.degree k f bound v)
    (original_depth A name digits hosts f) smoothed «public» lit sRead fRead
  refine ⟨dst,Procedure.Exec.then ran write,rect,?_⟩
  intro a ha
  exact (frame _ (lt_min_iff.mp ha).2).trans (retain _ (lt_min_iff.mp ha).1)

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas

end OAI
