import OAI.Hierarchy.DescentResetStemBlindIssue
import OAI.Hierarchy.DescentResetStemArenaPlan
import OAI.Hierarchy.DescentResetStemProjectExpr

namespace OAI
/-! # Closed native reset-stem issue from the previous high rail to every next block -/
namespace Hierarchy.DescentResetStemPackedIssue.Mixed.Projected
open DescentSIMDLookup DescentPackedZip DescentResetStemIncidence DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D f Q X K w pitch : ℕ}
def flat (s : Fin Q→Fin (D+2)→Expr) (j : Fin (Q*(D+2))) := s (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
def direction (X : ℕ) (s : Fin Q→Bool) (q : Fin (X*Q)) := s (finProdFinEquiv.symm q).2
def operand (base Q D P G X f M₀ M : ℕ) (q : Fin (X*Q)) (i : Fin (D+2)) : Expr :=
  let j:=finProdFinEquiv.symm q
  .lookup (DescentResetStemProject.bank base (Q*(D+2)) P G X f M₀ M (finProdFinEquiv (j.2,i)) j.1) .row
def splitAt (base Q D P G X f M₀ M : ℕ) :=
  DescentResetStemProject.endAddress base (Q*(D+2)) P G X f M₀ M

variable (base ptr b P H G X M₀ M : ℕ) (parse : DescentResetStemKey.Decoder D f)
  (side : Fin Q→Bool) (src : Fin Q→Fin (D+2)→Expr) (ports : Ports (2*K))
local notation "ready" => splitAt base Q D P G X f M₀ M
local notation "A" => plan ready ptr K H
local notation "ops" => operand base Q D P G X f M₀ M
local notation "sides" => direction X side

def program (w : ℕ) := (DescentResetStemProjectExpr.program base P G X f M₀ M (flat src) w).seq
  ((A).native parse sides ops ports b ready M P H G w)
def ticks (w : ℕ) := DescentResetStemProjectExpr.ticks base P G X f M₀ M (flat src)+
  (A).budget parse sides ops ports b ready M P H G w
def image (m : Memory w) := (A).result parse sides ops ports b ready M P H G
  (DescentResetStemProjectExpr.image base P G X f M₀ M (flat src) m)
def extent (base ptr D f b K P H G X M₀ M Q : ℕ) :=
  endAddress (splitAt base Q D P G X f M₀ M) ptr D f b K P H G M X Q

private theorem geometry (base ptr D f b K P H G X M₀ M Q : ℕ)
    (limit : extent base ptr D f b K P H G X M₀ M Q<2^w) :
    let cut:=splitAt base Q D P G X f M₀ M
    base≤ cut ∧ cut<2^w ∧ ∀q i,(operand base Q D P G X f M₀ M q i).Fits w cut := by
  let cut:=splitAt base Q D P G X f M₀ M
  have lower : base≤ cut:=by dsimp [cut,splitAt];rw [DescentResetStemProject.extent];omega
  have top : cut+endAddress 0 0 D f b K P H G M X Q<2^w:=by
    change endAddress cut ptr D f b K P H G M X Q<2^w at limit
    rwa [affine] at limit
  have end_ : cut<2^w:=(Nat.le_add_right ..).trans_lt top
  refine ⟨lower,end_,fun q i=>⟨?_,trivial⟩⟩
  exact DescentResetStemProject.page_fits (finProdFinEquiv ((finProdFinEquiv.symm q).2,i))
    (finProdFinEquiv.symm q).1 end_

private theorem chart_mono {base stop : ℕ} (p : Ports K) (low : base≤ stop) (fits : p.All (Expr.Fits w base)) :
    p.All (Expr.Fits w stop) :=
  ⟨ProtocolRAMGeneratedWrite.fits_mono _ low fits.here,fun i=>ProtocolRAMGeneratedWrite.fits_mono _ low (fits.near i),
   fun i=>ProtocolRAMGeneratedWrite.fits_mono _ low (fits.src i),fun i=>ProtocolRAMGeneratedWrite.fits_mono _ low (fits.dst i),
   fun i=>ProtocolRAMGeneratedWrite.fits_mono _ low (fits.hub i)⟩

set_option maxHeartbeats 1600000 in
theorem any_full (m : Memory w) (hm : 0<M) (hx : 0<X) (fit : ∀q i,(src q i).Fits w base)
    (chart : ports.All (Expr.Fits w base)) (ptrRoom : ptr+span H≤ base)
    (limit : extent base ptr D f b K P H G X M₀ M Q<2^w) :
    (program base ptr b P H G X M₀ M parse side src ports w).Exec m
      (image base ptr b P H G X M₀ M parse side src ports m) (ticks base ptr b P H G X M₀ M parse side src ports w) ∧
    (∀u,u< base ∨ extent base ptr D f b K P H G X M₀ M Q≤ u→image base ptr b P H G X M₀ M parse side src ports m u=m u) ∧
    CheapCode (program base ptr b P H G X M₀ M parse side src ports w) := by
  obtain ⟨low,fitRow,after⟩:=geometry base ptr D f b K P H G X M₀ M Q limit
  have pre:=DescentResetStemProjectExpr.any base P G X f M₀ M (flat src) m hm hx (fun j=>fit _ _) fitRow
  have post:=(A).native_any_full parse sides ops ports b ready M P H G
    (DescentResetStemProjectExpr.image base P G X f M₀ M (flat src) m) (chart_mono ports low chart)
    after (ptrRoom.trans low) le_rfl le_rfl limit
  have preCheap : CheapCode (DescentResetStemProjectExpr.program base P G X f M₀ M (flat src) w) := pre.2.2
  have postCheap : CheapCode ((A).native parse sides ops ports b ready M P H G w) := post.2.2
  refine ⟨?_,?_,@cheap_seq w _ _ (@preCheap) (@postCheap)⟩
  · intro nPC nReg nPub machine pc reg slots exit rom advice cfg rawMem enter same
    exact Procedure.Exec.then pre.1 post.1 machine pc reg slots exit rom advice cfg rawMem enter same
  intro u hu
  rcases hu with before|high
  · exact (post.2.1 u (.inl (before.trans_le low))).trans (pre.2.1 u (.inl before))
  · have inner : ready≤ extent base ptr D f b K P H G X M₀ M Q:=by unfold extent;rw [affine];omega
    exact (post.2.1 u (.inr high)).trans (pre.2.1 u (.inr (inner.trans high)))

theorem any (m : Memory w) (hm : 0<M) (hx : 0<X) (fit : ∀q i,(src q i).Fits w base)
    (chart : ports.All (Expr.Fits w base)) (ptrRoom : ptr+span H≤ base)
    (limit : extent base ptr D f b K P H G X M₀ M Q<2^w) :
    (program base ptr b P H G X M₀ M parse side src ports w).Exec m
      (image base ptr b P H G X M₀ M parse side src ports m) (ticks base ptr b P H G X M₀ M parse side src ports w) :=
  (any_full base ptr b P H G X M₀ M parse side src ports m hm hx fit chart ptrRoom limit).1

set_option maxHeartbeats 1600000 in
theorem run (m : Memory w) (ha : 0<M₀) (hm : 0<M) (hx : 0<X)
    (fit : ∀q i,(src q i).Fits w base) (vals : Fin Q→Fin P→Fin (G*X)→Fin (D+2)→Cell f)
    (words : ∀q i,Source (src q i) (fun h g=>vals q h g i) M₀ m)
    (scene : Scene (2*K) H pitch) (raw : Reads ports scene m) (portRoom : ports.All (Expr.Fits w base))
    (owner : Fin H→Fin P) (directory : DescentResetStemKeyReindex.Directory ptr owner m)
    (ptrRoom : ptr+span H≤ base) (room : pitch<2^w) (wide : (b*7)*M≤ w) (zero : parse 0=none)
    (limit : extent base ptr D f b K P H G X M₀ M Q<2^w) :
    let out:=image base ptr b P H G X M₀ M parse side src ports m
    (program base ptr b P H G X M₀ M parse side src ports w).Exec m out
      (ticks base ptr b P H G X M₀ M parse side src ports w) ∧
    (∀x q (p : Row H G M),out ((A).out D f (b*7) K M P H G (X*Q)+
      (finProdFinEquiv (x,q)).val*(H*chunks G M)+(row H G M p).val)=
      ((data (fun h g=>DescentResetStemMux.pick (DescentResetStemKey.word parse (side q)
        (vals q (owner h) (finProdFinEquiv (g,x)))) (fun j=>DescentResetFieldAssembler.raw b (metaAt scene (side q) j h))) p).val:Word w)) ∧
    (∀u,u< base ∨ extent base ptr D f b K P H G X M₀ M Q≤ u → out u=m u) ∧
    CheapCode (program base ptr b P H G X M₀ M parse side src ports w) := by
  obtain ⟨lo,readyFit,after⟩:=geometry base ptr D f b K P H G X M₀ M Q limit
  let old (j : Fin (Q*(D+2))) (h : Fin P) (g : Fin (G*X)):=vals (finProdFinEquiv.symm j).1 h g (finProdFinEquiv.symm j).2
  let pre:=DescentResetStemProjectExpr.image base P G X f M₀ M (flat src) m
  obtain ⟨cpu,rows,_,frame,cheap⟩:=DescentResetStemProjectExpr.run base P G X f M₀ M (flat src) m old ha hm hx
    (fun j=>fit _ _) (fun j=>words _ _) readyFit
  have keep (u : ℕ) (small : u< base) : pre u=m u:=frame u (.inl small)
  have e (v : Expr) (below : v.Fits w base) (j : Word w) : v.eval pre j=v.eval m j:=
    eval_below v j m pre below keep
  have seen : Reads ports scene pre:=⟨fun j=>(e _ portRoom.here _).trans (raw.here j),
    fun j i=>(e _ (portRoom.near i) _).trans (raw.near j i),fun i j=>(e _ (portRoom.src i) _).trans (raw.src i j),
    fun i j=>(e _ (portRoom.dst i) _).trans (raw.dst i j),fun i j=>(e _ (portRoom.hub i) _).trans (raw.oldHub i j)⟩
  have ptrOK : DescentResetStemKeyReindex.Directory ptr owner pre:=by
    intro j
    have small:=j.isLt.trans_le (span_ge H)
    exact (keep _ (by omega)).trans (directory j)
  let y (k : Fin (X*Q)) (h : Fin P) (g : Fin G) :=
    vals (finProdFinEquiv.symm k).2 h (finProdFinEquiv (g,(finProdFinEquiv.symm k).1))
  have physical (k i) : Source (ops k i) (fun h g=>y k h g i) M pre:=by
    simpa only [operand,old,y,Equiv.symm_apply_apply] using
      rows (finProdFinEquiv ((finProdFinEquiv.symm k).2,i)) (finProdFinEquiv.symm k).1
  have done_:=(A).native_run parse sides ops ports b ready pre scene seen
    (chart_mono ports lo portRoom) room zero y owner after physical ptrOK
    (ptrRoom.trans lo) le_rfl le_rfl wide limit
  have postCheap : CheapCode ((A).native parse sides ops ports b ready M P H G w) := done_.2.2.2
  refine ⟨?_,?_,?_,@cheap_seq w _ _ (@cheap) (@postCheap)⟩
  · intro nPC nReg nPub machine pc reg slots exit rom advice cfg rawMem enter same
    exact Procedure.Exec.then cpu done_.1 machine pc reg slots exit rom advice cfg rawMem enter same
  · intro x q p
    change (A).result parse sides ops ports b ready M P H G pre _ = _
    simpa only [direction,y,Equiv.symm_apply_apply] using done_.2.1 (finProdFinEquiv (x,q)) p
  · intro u hu
    rcases hu with lt|ge
    · exact (done_.2.2.1 u (.inl (lt.trans_le lo))).trans (keep u lt)
    · have le : ready≤ extent base ptr D f b K P H G X M₀ M Q:=by unfold extent;rw [affine];omega
      exact (done_.2.2.1 u (.inr ge)).trans (frame u (.inr (le.trans ge)))

end
end Hierarchy.DescentResetStemPackedIssue.Mixed.Projected

end OAI
