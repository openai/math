import OAI.Hierarchy.DescentPackedResetRectangle
import OAI.Hierarchy.DescentPackedSiteZero
import OAI.Hierarchy.DescentPackedRectanglePins
import OAI.Hierarchy.DescentIssuedResidentReset

namespace OAI
/-! # One native execution from the old packed graph to the original reset estimator bank -/
namespace Hierarchy.DescentSixParty.PackedFlow
open DescentGL DescentColonies DescentSIMDLookup DescentPackedExchange DescentMeasuredWeights DescentMeasuredHeader
open DescentBaseProfile DescentPackedWalsh DescentWalshPhysical DescentPackedRectangle DescentPackedSingletonDepth
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k H u l b w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W G q ε J V k) (name : V≃Fin H) (digits : Block (u+l)≃J×Block k)
local notation "m" => u+l
local notation "N" => H*(m+1)+H*A.degree
local notation "header" => A.mixerHeader digits name
local notation "bound" => A.wire*(A.z*G.b)*A.cap
local notation "P" => DescentPackedWalsh.page H u

def ptrBank (at_ H : ℕ) : Bank := ⟨at_,Nat.clog 2 H⟩
def siteBank (first H u : ℕ) : Bank := ⟨first,rowBits H u⟩

theorem prime (f K root first edges scratch totals lo pitch base out : ℕ) (ptr flow : Bank)
    (src mem prior : Memory w)
    (fullMode : ∀v,Native.totalWeight (header).loads v<2^b) (packed : smallKey l b≤w)
    (roomTiny : root+m*span H u l b≤first) (stages : first+(m+1)*P≤totals) (endAddr : totals+H<2^w)
    (stamped : ∀a<first,mem a=mounted H b root ((axesList u l).map axis) src a)
    (fixed : ∀a,lo≤a→a<lo+words H u l A.degree→mem a=mount lo pitch f bound K H u l A.degree prior a)
    (geometry : lo+words H u l A.degree≤first) (ptrLow : ptr.base+H≤first) (edgeLow : edges+H*A.degree≤first)
    (ptrRead : ∀v:Fin H,mem (ptr.base+v.val)=((row v (fun _ : Fin u=>false)).val:Word w))
    (edgeRead : ∀v:Fin H,∀j:Fin A.degree,mem (edges+v.val*A.degree+j.val)=
      (target (next A name v j):Word w))
    (ptrFit : ptr.Fits w totals) (dataFit : (transformBank first H u l).Fits w totals) (pn : H≤ptr.size)
    (scalar : b≤w) (hRoom : H<2^w) (dimRoom : 2*m+1<2^w) (one : 1<2^w)
    (smoothed : ∀v,(header).depth A f v≤ m)
    (site : Installed first (fun v=>shaped (fun z=>(A.resetLoad digits (name.symm v)
      (address m ((coordinates _).symm z)):Cell b))) mem)
    (traffic : ∀j:Fin A.degree,Installed (flow.base+j.val*pitch) (fun v=>shaped (fun z=>
      (raw A name digits j v (address m ((coordinates _).symm z)):Cell b))) mem)
    (oldPorts : flow.base+A.degree*pitch≤first)
    (safe : (layout H A.degree m k f bound totals edges scratch).Fits w)
    (depthBits peerBits flagBits : ℕ)
    (hs : let L:=layout H A.degree m k f bound totals edges scratch
      let T:=metadata (H:=H) (u:=u) (l:=l) (D:=A.degree) lo ⟨L.base (L.M+1),depthBits⟩ ⟨edges,peerBits⟩
      DescentMeasuredHeader.Fits T w H m A.degree base)
    (gs : let T:=gather (H:=H) (u:=u) (l:=l) (D:=A.degree) lo ⟨base,flagBits⟩ (siteBank first H u) flow
      Room T pitch H u l A.degree w out)
    (priorBanks : let T:=gather (H:=H) (u:=u) (l:=l) (D:=A.degree) lo ⟨base,flagBits⟩ (siteBank first H u) flow
      ∀B∈[T.kind,T.owner,T.pointer,T.sites,T.flows],B.base+B.size≤base)
    (gap : base+3*N≤out) :
    let D:=transformBank first H u l
    let L:=layout H A.degree m k f bound totals edges scratch
    let T:=metadata (H:=H) (u:=u) (l:=l) (D:=A.degree) lo ⟨L.base (L.M+1),depthBits⟩ ⟨edges,peerBits⟩
    let C:=gather (H:=H) (u:=u) (l:=l) (D:=A.degree) lo ⟨base,flagBits⟩ (siteBank first H u) flow
    let run:=(DescentPackedWalsh.code w root first H u l b 0 (axesList u l)).seq ((tap D ptr b totals H w).seq (L.cpu w L.M))
    ∃dst : Memory w,(run.seq (DescentPackedRectangle.code T C w base out H u l A.degree)).Exec mem dst
      (DescentPackedSingletonDepth.clocks H u l A.degree k f bound totals edges scratch w+
        (headerTime T H m A.degree+(4+100*(N*2^u)))) ∧
       InstalledRectangle (b:=b) A name digits f K base out dst ∧ ∀a< min first base,dst a=mem a := by
  intro D L T C run
  have edges_ (v:Fin H) (j:Fin A.degree) :
      mem (edges+v.val*A.degree+j.val)=(DepthRAM.number (((header).neighbors[v.val])[j.val]?):Word w) := by
    have readEdge := edgeRead v j
    rw [next_numbered,A.slot_matches digits name] at readEdge
    exact readEdge
  have old : Installed first (fun v=>shaped (fun z=>(((header).loads[v.val])[(address m ((coordinates _).symm z)).val]:Cell b))) mem := by
    simpa [GroupStage.mixerHeader] using site
  obtain ⟨mid,ran,baseDepth,retain⟩:=depths root first ptr A.degree k f bound totals edges scratch src mem
    (header).loads (header).neighbors fullMode packed roomTiny stages endAddr stamped old safe ptrFit dataFit pn scalar
    ptrLow edgeLow ptrRead edges_ (header).degree
  have static (a : ℕ) (ha : lo≤a) (hb : a<lo+words H u l A.degree) := (retain a
    ((hb.trans_le geometry).trans_le (Nat.le_add_right ..))).trans (fixed a ha hb)
  have dr (v:Fin H):mid (L.base (L.M+1)+v.val)=((header).depth A f (name.symm v):Word w):=by
    change _ = (measuredDepth (header).neighbors (header).loads A.degree k f bound (name (name.symm v)):Word w)
    rw [name.apply_symm_apply]
    exact baseDepth v
  have nr (p:Port H A.degree):
      mid (edges+(slot H A.degree p).val)=(target (neighborSlot name A.mutual p):Word w):=by
    rcases p with ⟨v,j⟩
    have lim:=Nat.mul_le_mul_right A.degree v.isLt;rw [Nat.succ_mul] at lim
    have addr : (slot H A.degree (v,j)).val=v.val*A.degree+j.val := by simp [slot,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
    rw [addr,←Nat.add_assoc,retain _ (by have:=j.isLt;omega),edgeRead,next_numbered]
  obtain ⟨lit,«public»⟩:=DescentPackedRectangle.retained lo pitch f bound K (⟨base,flagBits⟩:Bank) (siteBank first H u) flow
    ⟨L.base (L.M+1),depthBits⟩ ⟨edges,peerBits⟩ prior mid ((header).depth A f ∘name.symm) _ static dr nr
  have sRead : Installed C.sites.base (fun v=>shaped (fun z=>(A.resetLoad digits (name.symm v)
      (address m ((coordinates _).symm z)):Cell b))) mid := by
    intro v p;exact (retain _ (Nat.add_lt_add_left ((row v p).isLt.trans_le (rows_le H u)) _)).trans (site v p)
  have fRead (j:Fin A.degree) : Installed (C.flows.base+j.val*pitch) (fun v=>shaped (fun z=>
      (raw A name digits j v (address m ((coordinates _).symm z)):Cell b))) mid := by
    intro v p
    have small:=(row v p).isLt.trans_le gs.width
    have end_:=Nat.mul_le_mul_right pitch j.isLt;rw [Nat.succ_mul] at end_
    exact (retain _ (by change flow.base+j.val*pitch+_ <first+_;omega)).trans (traffic j v p)
  obtain ⟨dst,rect,rectangleFields,low⟩:=rectangle A name digits T C f K base pitch out gs hs rfl gap priorBanks mid hRoom dimRoom
    one smoothed «public» lit sRead fRead
  refine ⟨dst,Procedure.Exec.then ran rect,rectangleFields,?_⟩
  intro a ha
  have ab:=lt_min_iff.mp ha
  exact (low _ ab.2).trans (retain _ (ab.1.trans_le (Nat.le_add_right ..)))

end
end Hierarchy.DescentSixParty.PackedFlow

end OAI
