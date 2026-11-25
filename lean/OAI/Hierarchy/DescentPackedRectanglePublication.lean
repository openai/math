import OAI.Hierarchy.DescentPackedRectangle
import OAI.Hierarchy.DescentMeasuredPortProof

namespace OAI
/-! # Combine the true sparse header and the packed emitted estimator rectangle -/
namespace Hierarchy.DescentPackedRectangle
open DescentSIMDLookup DescentGL DescentPackedExchange DescentMeasuredWeights DescentMeasuredHeader DescentPackedWalsh
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H u l D b w : ℕ}
local notation "k" => u+l
local notation "N" => H*(k+1)+H*D
local notation "R" => Rows H k D
local notation "ord" => rowOrd H k D
local notation "coords" => DescentWalshPhysical.coordinates

def code (L : Tape) (A : Gather) (w base dest H u l D : ℕ) :=
  (headerProgram L w base H (u+l) D).seq (scan w dest ((H*((u+l)+1)+H*D)*2^u) (expression A))

theorem issued (L : Tape) (A : Gather) (base pitch out : ℕ) (S : Room A pitch H u l D w out)
    (safe : Fits L w H k D base) (liveBase : A.live.base=base) (disjoint : base+3*N≤out)
    (before : ∀B∈[A.kind,A.owner,A.pointer,A.sites,A.flows],B.base+B.size≤base)
    (mem : Memory w) (depth : Fin H→ℕ) (next : Port H D→Option (Fin H)) (f B K : ℕ)
    (site : Fin H→Bits k→ℕ) (traffic : Port H D→Bits k→ℕ)
    (fixed : contents («k» := u+l) L depth next f B K mem) (hRoom : H<2^w) (wide : 2*k+1<2^w)
    (one : 1<2^w) (bounded : ∀v,depth v≤k) («public» : Public A pitch H u l D mem)
    (sites : Installed A.sites.base (fun v=>shaped (u:=u) (l:=l) (fun z=>(site v ((coords _).symm z):Cell b))) mem)
    (flows : ∀j : Fin D,Installed (A.flows.base+j.val*pitch)
      (fun v=>shaped (u:=u) (l:=l) (fun z=>(traffic (v,j) ((coords _).symm z):Cell b))) mem) :
    ∃dst : Memory w,(code L A w base out H u l D).Exec mem dst (headerTime L H k D+(4+100*(N*2^u))) ∧
      Installed out (fun t=>shaped (u:=u) (l:=l) (fun z=>(realLoad depth next site traffic ((rowOrd H (u+l) D).symm t) ((coords _).symm z):Cell b))) dst ∧
      (∀t : R,dst (base+N+(ord t).val)=(realDepth depth next t:Word w)) ∧
      (∀t : R,dst (base+2*N+(ord t).val)=(realGain depth next f B K t:Word w)) ∧
      ∀a<base,dst a=mem a := by
  let mid:=headerMem L base H k D mem
  have top : base+3*N<2^w:=disjoint.trans_lt ((Nat.le_add_right _ _).trans_lt S.output)
  obtain ⟨head,cheap⟩:=header_exec L mem safe top
  have same (a : ℕ) (lo : a<base) : mid a=mem a:=header_frame L mem lo
  have word (z : Bank) (inRun : z∈[A.kind,A.owner,A.pointer,A.sites,A.flows]) (j : ℕ) (ok : j<z.size) :
      mid (z.base+j)=mem (z.base+j):=same _ ((Nat.add_lt_add_left ok _).trans_le (before z inRun))
  have stat : Public A pitch H u l D mid :=
    ⟨fun t p=>(word A.owner (by simp) _ ((DescentPackedWalsh.row (ord t) p).isLt.trans_le S.owner)).trans («public».owner t p),
     fun t p=>(word A.kind (by simp) _ ((DescentPackedWalsh.row (ord t) p).isLt.trans_le S.kind)).trans («public».kind t p),
     fun t p=>(word A.pointer (by simp) _ ((DescentPackedWalsh.row (ord t) p).isLt.trans_le S.pointer)).trans («public».pointer t p)⟩
  have siteNow : Installed A.sites.base (fun v=>shaped (u:=u) (l:=l) (fun z=>(site v ((coords _).symm z):Cell b))) mid :=
    fun v p=>(word A.sites (by simp) _ ((DescentPackedWalsh.row v p).isLt.trans_le S.sites)).trans (sites v p)
  have flowNow (j : Fin D) : Installed (A.flows.base+j.val*pitch)
      (fun v=>shaped (u:=u) (l:=l) (fun z=>(traffic (v,j) ((coords _).symm z):Cell b))) mid := by
    intro v p
    have gap:=Nat.mul_le_mul_right pitch j.isLt;rw [Nat.succ_mul] at gap
    have slot:=(DescentPackedWalsh.row v p).isLt.trans_le S.width
    rw [Nat.add_assoc,word A.flows (by simp) _ ((by omega : j.val*pitch+(DescentPackedWalsh.row v p).val<D*pitch).trans_le S.traffic),←Nat.add_assoc]
    exact flows j v p
  have flag (t : R) : mid (A.live.base+(ord t).val)=(isLive depth next t:Word w) := by
    simpa only [mid,liveBase,fieldNumber,Nat.zero_mul,Nat.add_zero,DescentMeasuredHeader.value] using
      header_read L safe depth next f B K mem fixed hRoom wide bounded .live t
  obtain ⟨emit,words,_⟩:=native A pitch out S mid depth next site traffic one stat flag siteNow flowNow
  refine ⟨image out (N*2^u) (expression A) mid, ?_, words, ?_, ?_, ?_⟩
  · intro labels regs slots machine
    exact Procedure.Exec.then head emit machine
  · intro t
    have lt := (ord t).isLt
    rw [image_frame _ _ (by omega : base+N+(ord t).val<out)]
    simpa only [mid,fieldNumber,Nat.one_mul,DescentMeasuredHeader.value] using header_read L safe depth next f B K mem fixed hRoom wide bounded .depth t
  · intro t
    have lt := (ord t).isLt
    rw [image_frame _ _ (by omega : base+2*N+(ord t).val<out)]
    simpa only [mid,fieldNumber,DescentMeasuredHeader.value] using header_read L safe depth next f B K mem fixed hRoom wide bounded .gain t
  · intro a ha
    have low : a<out := ha.trans_le ((Nat.le_add_right base (3*N)).trans disjoint)
    exact (image_frame (expression A) mid low).trans (same a ha)

end
end Hierarchy.DescentPackedRectangle

end OAI
