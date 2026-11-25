import OAI.Hierarchy.DescentResetStemProjected

namespace OAI
/-! # Reading a reblocked original signed chip across the actual reset stem pass -/
namespace Hierarchy.DescentResetStemPackedIssue.Mixed.Layout
open DescentPackedColony DescentPackedZip DescentSIMDLookup DescentDyadicSpan DescentSixParty.Chronology DescentResetStemIncidence
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
variable {D f Q w K : ℕ}
variable (A : Layout) (parse : DescentResetStemKey.Decoder D f) (side : Fin Q→Bool) (src : Fin Q→Fin (D+2)→Expr)

theorem earlier_key (b K M P H G : ℕ) (m : Memory w) (safe : ∀q i,(src q i).Fits w A.base)
    (ptr : A.pointer+span H≤A.base) (raw : A.raw+(2*K)*H+span H≤A.base)
    (room : A.stop D f b K M P H G Q<2^w) {v : ℕ} (old : Bank) (value : Fin P→Fin G→Cell v)
    (owner : Fin H→Fin P) (prior : DescentResetStemKeyReindex.Directory A.pointer owner m)
    (early : old.Fits w A.base) (capacity : P*chunks G M≤old.size)
    (words : Source (.lookup old .row) value M m) :
    let term:=DescentResetStemKeyReindex.keyExpr old (A.mapping D f M P G Q) A.pointer P H G M
    term.Fits w (A.stop D f b K M P H G Q) ∧
      Source term (fun h g=>value (owner h) g) M (A.output parse side src b K M P H G m) := by
  let mapBase:=A.mapping D f M P G Q
  let headBase:=A.hdr D f M P H G Q
  let muxBase:=A.mux D f b K M P H G Q
  let emit:=A.out D f b K M P H G Q
  let first:=DescentResetStemKey.Columns.output parse side src A.base M P G m
  let remap:=DescentResetStemKeyReindex.phase w mapBase P H G M
  let mid:=remap.image first
  let pub:=DescentResetStemHeaders.phase w (2*K) H G M b A.raw headBase
  let sent:=pub.image mid
  let z:=DescentResetStemHeaders.outputBase H G M b headBase+(2*K)*(H*chunks G M)
  have lm : A.base≤ mapBase:=by dsimp [mapBase,mapping,DescentResetStemKey.Columns.stop,DescentResetStemKey.Columns.start];omega
  have mh : mapBase≤headBase:=Nat.le_add_right ..
  have hz : headBase≤z:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have zm : z≤ muxBase:=Nat.le_add_right ..
  have ml : muxBase≤emit:=Nat.le_add_right ..
  have wf : emit<2^w:=(Nat.le_add_right ..).trans_lt room
  have wh : headBase<2^w:=hz.trans_lt (zm.trans_lt (ml.trans_lt wf))
  have wm : mapBase<2^w:=mh.trans_lt wh
  have a:=DescentResetStemKey.Columns.any_full parse side src A.base m safe wm
  have h:=DescentResetStemHeaders.any (G:=G) (M:=M) (b:=b) mid (raw.trans (lm.trans mh)) (zm.trans_lt (ml.trans_lt wf))
  have fits (q : Fin Q) : (A.key D f M P H G q).Fits w muxBase := by
    exact ProtocolRAMGeneratedWrite.fits_mono _ (hz.trans zm)
      (DescentResetStemKeyReindex.fits _ (DescentResetStemKey.Columns.bank_fits A.base D f M P G Q w q wm).1
        (ptr.trans lm) wh)
  have heads (q : Fin Q) (j : Fin K) : (A.heads D f b M P H G side q j).Fits w muxBase :=
    DescentResetStemHeaders.expr_fits (headIndex (side q) j) le_rfl (ml.trans_lt wf)
  have e:=DescentResetStemIssuer.any muxBase (A.key D f M P H G) (A.heads D f b M P H G side (K:=K))
    (a:=f+2) (b:=b) (M:=M) (H:=H) (G:=G) emit sent fits heads le_rfl room
  have room' : old.Fits w mapBase:=⟨early.1,early.2.1,early.2.2.trans lm⟩
  have readers : DescentPackedColony.Reads old value M first:=by
    intro p
    have idx:=(row P G M p).isLt.trans_le capacity
    have lo:=early.2.2
    exact (a.2.1 _ (.inl (by omega))).trans
      ((DescentPackedZip.bank_read old m idx early).symm.trans (words p))
  have parents : DescentResetStemKeyReindex.Directory A.pointer owner first:=by
    intro h
    have h':=h.isLt.trans_le (span_ge H)
    exact (a.2.1 _ (.inl (by omega))).trans (prior h)
  obtain ⟨fit,available⟩:=DescentResetStemKeyReindex.source old value owner first readers parents room' capacity (ptr.trans lm) wh
  have cut : headBase≤A.stop D f b K M P H G Q :=(hz.trans (zm.trans ml)).trans (Nat.le_add_right ..)
  refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ cut fit,?_⟩
  intro p
  apply Eq.trans (eval_below _ _ mid _ fit ?_) (available p)
  intro u low
  have low':=low.trans_le (hz.trans zm)
  exact (e.2.1 u (.inl low') (.inl (low'.trans_le ml))).trans (h.2 u (.inl low))

end
end Hierarchy.DescentResetStemPackedIssue.Mixed.Layout

namespace Hierarchy.DescentResetStemPackedIssue.Mixed.Projected
open DescentSIMDLookup DescentPackedZip DescentResetStemIncidence DescentDyadicSpan
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open private Hierarchy.DescentResetStemPackedIssue.Mixed.Projected.geometry Hierarchy.DescentResetStemPackedIssue.Mixed.Projected.chart_mono from OAI.Hierarchy.DescentResetStemProjected
noncomputable section
variable {D f Q K w : ℕ}

def signedRegister (base ptr K P H G X M₀ M : ℕ) (x : Fin X) (j : Fin Q) : Expr :=
  let start:=splitAt base Q D P G X f M₀ M
  let a:=plan start ptr K H
  let raw:=DescentResetStemProject.bank base (Q*(D+2)) P G X f M₀ M
    (finProdFinEquiv (j,(0:Fin (D+1)).succ)) x
  DescentResetStemKeyReindex.keyExpr raw (a.mapping D f M P G (X*Q)) ptr P H G M

theorem signed_register_work (base ptr K P H G X M₀ M : ℕ) (x : Fin X) (j : Fin Q) :
    (signedRegister (D:=D) (f:=f) base ptr K P H G X M₀ M x j).work=30:=rfl

theorem signed_register_read (base ptr b P H G X M₀ M : ℕ) (parse : DescentResetStemKey.Decoder D f)
    (side : Fin Q→Bool) (src : Fin Q→Fin (D+2)→Expr) (ports : Ports (2*K)) (m : Memory w)
    (ha : 0<M₀) (hm : 0<M) (hx : 0<X)
    (xold : Fin Q→Fin P→Fin (G*X)→Fin (D+2)→Cell f) (owner : Fin H→Fin P)
    (safe : ∀j i,(src j i).Fits w base) (prior : ∀j i,Source (src j i) (fun h g=>xold j h g i) M₀ m)
    (domain : DescentResetStemKeyReindex.Directory ptr owner m) (ptrRoom : ptr+span H≤base)
    (range : ports.All (Expr.Fits w base)) (room : extent base ptr D f b K P H G X M₀ M Q<2^w)
    (x : Fin X) (j : Fin Q) :
    let term:=signedRegister (D:=D) (f:=f) base ptr K P H G X M₀ M x j
    term.Fits w (extent base ptr D f b K P H G X M₀ M Q) ∧
      Source term (fun h g=>xold j (owner h) (finProdFinEquiv (g,x)) (0:Fin (D+1)).succ) M
        (image base ptr b P H G X M₀ M parse side src ports m) :=by
  let early:=splitAt base Q D P G X f M₀ M
  let a:=plan early ptr K H
  let q : Fin (Q*(D+2)):=finProdFinEquiv (j,(0:Fin (D+1)).succ)
  let donor:=DescentResetStemProject.bank base (Q*(D+2)) P G X f M₀ M q x
  let vals (c : Fin (Q*(D+2))) (h : Fin P) (g : Fin (G*X)):=
    xold (finProdFinEquiv.symm c).1 h g (finProdFinEquiv.symm c).2
  let pre:=DescentResetStemProjectExpr.image base P G X f M₀ M (flat src) m
  obtain ⟨low,valid,ops⟩:=Hierarchy.DescentResetStemPackedIssue.Mixed.Projected.geometry
    base ptr D f b K P H G X M₀ M Q room
  obtain ⟨_,values,banks,keep,_⟩:=DescentResetStemProjectExpr.run base P G X f M₀ M (flat src) m vals ha hm hx
    (fun _=>safe _ _) (fun _=>prior _ _) valid
  let v (h : Fin P) (g : Fin G):=xold j h (finProdFinEquiv (g,x)) (0:Fin (D+1)).succ
  have previous : Source (.lookup donor .row) v M pre:=by
    simpa only [donor,q,vals,v,Equiv.symm_apply_apply] using values q x
  let stage:=DescentResetStemDescriptorRAM.output (ports.inputs (polarity K)) b H early a.raw pre
  have below : early≤a.base:=by dsimp [a,plan];omega
  have stemEnd : a.base≤a.stop D f (b*7) K M P H G (X*Q):=by
    unfold Layout.stop Layout.out Layout.mux Layout.hdr Layout.mapping DescentResetStemKey.Columns.stop DescentResetStemKey.Columns.start DescentResetStemHeaders.outputBase
    omega
  have cut : a.raw+2*K*H<2^w:=by
    have inSlice : a.raw+2*K*H≤a.base:=Nat.le_add_right ..
    exact (inSlice.trans stemEnd).trans_lt room
  have raw:=DescentResetStemDescriptorRAM.any (ports.inputs (polarity K)) b H early a.raw pre
    (ports.fits (polarity K) (Hierarchy.DescentResetStemPackedIssue.Mixed.Projected.chart_mono ports low range)) le_rfl cut
  have held (t : ℕ) (h : t<early) : stage t=pre t:=
    raw.2.1 t (.inl h) (.inl (h.trans_le (by change early≤early+56;omega)))
  have oldFit:=banks q x
  have measured : Source (.lookup donor .row) v M stage:=fun p=>
    (eval_below _ _ pre stage (show (Expr.lookup donor .row).Fits w early from ⟨oldFit,trivial⟩) held).trans (previous p)
  have directory : DescentResetStemKeyReindex.Directory ptr owner stage:=by
    intro h
    have h':=h.isLt.trans_le (span_ge H)
    have t : ptr+h.val<base:=by omega
    exact (held _ (t.trans_le low)).trans ((keep _ (.inl t)).trans (domain h))
  have more : donor.Fits w a.base:=⟨oldFit.1,oldFit.2.1,oldFit.2.2.trans below⟩
  exact a.earlier_key parse (direction X side) (operand base Q D P G X f M₀ M)
    (b*7) K M P H G stage (fun u d=>ProtocolRAMGeneratedWrite.fits_mono _ below (ops u d))
    (ptrRoom.trans (low.trans below)) le_rfl room donor v owner directory more (DescentResetStemProject.page_capacity q x) measured

end
end Hierarchy.DescentResetStemPackedIssue.Mixed.Projected

end OAI
