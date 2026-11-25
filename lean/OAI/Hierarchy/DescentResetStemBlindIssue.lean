import OAI.Hierarchy.DescentResetStemLiveDescriptor

namespace OAI
/-! # The concrete stem instruction schedule runs on every input tape -/
namespace Hierarchy.DescentResetStemPackedIssue.Mixed.Layout
open DescentSIMDLookup DescentDyadicSpan DescentSixParty.Chronology DescentResetStemIncidence
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
variable {D f Q w K : ℕ}
variable (A : Layout) (parse : DescentResetStemKey.Decoder D f) (side : Fin Q→Bool) (src : Fin Q→Fin (D+2)→Expr)

theorem any_full (b K M P H G : ℕ) (m : Memory w) (safe : ∀q i,(src q i).Fits w A.base)
    (ptr : A.pointer+span H≤A.base) (raw : A.raw+(2*K)*H+span H≤A.base)
    (room : A.stop D f b K M P H G Q<2^w) :
    (A.code parse side src b K M P H G w).Exec m (A.output parse side src b K M P H G m)
      (A.ticks parse side src b K M P H G w) ∧
      (∀a, a < A.base ∨ A.stop D f b K M P H G Q ≤ a → A.output parse side src b K M P H G m a=m a) ∧
      CheapCode (A.code parse side src b K M P H G w) := by
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
  have d:=DescentResetStemKeyReindex.run (H₀:=P) (H₁:=H) (G:=G) (M:=M) first wh
  have h:=DescentResetStemHeaders.any (G:=G) (M:=M) (b:=b) mid (raw.trans (lm.trans mh)) (zm.trans_lt (ml.trans_lt wf))
  have fits (q : Fin Q) : (A.key D f M P H G q).Fits w muxBase := by
    exact ProtocolRAMGeneratedWrite.fits_mono _ (hz.trans zm)
      (DescentResetStemKeyReindex.fits _ (DescentResetStemKey.Columns.bank_fits A.base D f M P G Q w q wm).1
        (ptr.trans lm) wh)
  have heads (q : Fin Q) (j : Fin K) : (A.heads D f b M P H G side q j).Fits w muxBase :=
    DescentResetStemHeaders.expr_fits (headIndex (side q) j) le_rfl (ml.trans_lt wf)
  have e:=DescentResetStemIssuer.any muxBase (A.key D f M P H G) (A.heads D f b M P H G side (K:=K))
    (a:=f+2) (b:=b) (M:=M) (H:=H) (G:=G) emit sent fits heads le_rfl room
  refine ⟨?_,?_,cheap_seq (cheap_seq (cheap_seq a.2.2 remap.cheap) pub.cheap) e.2.2⟩
  · intro nPC nReg nPub machine pc reg slots exit rom advice cfg rawMem enter same
    exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then a.1 d.1) h.1) e.1
      machine pc reg slots exit rom advice cfg rawMem enter same
  intro u away
  rcases away with lower|upper
  · have low1 := lower.trans_le lm
    have low2 := low1.trans_le mh
    have low3 := low2.trans_le (hz.trans zm)
    exact (e.2.1 u (.inl low3) (.inl (low3.trans_le ml))).trans
      ((h.2 u (.inl low2)).trans ((d.2.2 u (.inl low1)).trans (a.2.1 u (.inl lower))))
  · have endBound : emit ≤ A.stop D f b K M P H G Q := Nat.le_add_right ..
    have high1 := endBound.trans upper
    have high2 := (zm.trans ml).trans high1
    exact (e.2.1 u (.inr high1) (.inr upper)).trans
      ((h.2 u (.inr high2)).trans ((d.2.2 u (.inr (hz.trans high2))).trans
        (a.2.1 u (.inr ((mh.trans hz).trans high2)))))

theorem any (b K M P H G : ℕ) (m : Memory w) (safe : ∀q i,(src q i).Fits w A.base)
    (ptr : A.pointer+span H≤A.base) (raw : A.raw+(2*K)*H+span H≤A.base)
    (room : A.stop D f b K M P H G Q<2^w) :
    (A.code parse side src b K M P H G w).Exec m (A.output parse side src b K M P H G m)
      (A.ticks parse side src b K M P H G w) :=
  (A.any_full parse side src b K M P H G m safe ptr raw room).1

variable (chart : DescentResetStemIncidence.Ports (2*K))
theorem native_any_full (b location M P H G : ℕ) (m : Memory w)
    (ports : chart.All (Expr.Fits w location)) (safe : ∀q i,(src q i).Fits w location)
    (ptr : A.pointer+span H≤location) (literal : location+56≤A.raw)
    (raw : A.raw+(2*K)*H+span H≤A.base) (room : A.stop D f (b*7) K M P H G Q<2^w) :
    (A.native parse side src chart b location M P H G w).Exec m
      (A.result parse side src chart b location M P H G m) (A.budget parse side src chart b location M P H G w) ∧
      (∀u, u < location ∨ A.stop D f (b*7) K M P H G Q ≤ u →
        A.result parse side src chart b location M P H G m u=m u) ∧
      CheapCode (A.native parse side src chart b location M P H G w) := by
  have baseLow : A.base≤A.stop D f (b*7) K M P H G Q:=by
    unfold stop out mux hdr mapping DescentResetStemKey.Columns.stop DescentResetStemKey.Columns.start
      DescentResetStemHeaders.outputBase
    omega
  have mid := DescentResetStemDescriptorRAM.any (chart.inputs (polarity K)) b H location A.raw m
    (chart.fits (polarity K) ports) literal (by omega : A.raw+(2*K)*H<2^w)
  have stable : location≤A.base:=by omega
  have final := A.any_full parse side src (b*7) K M P H G
    (DescentResetStemDescriptorRAM.output (chart.inputs (polarity K)) b H location A.raw m)
    (fun q i=>ProtocolRAMGeneratedWrite.fits_mono _ stable (safe q i)) (ptr.trans stable) raw room
  refine ⟨?_,?_,cheap_seq mid.2.2 final.2.2⟩
  · intro nPC nReg nPub machine pc reg slots exit rom advice cfg rawMem enter same
    exact Procedure.Exec.then mid.1 final.1 machine pc reg slots exit rom advice cfg rawMem enter same
  intro u away
  rcases away with lower|upper
  · exact (final.2.1 u (.inl (lower.trans_le stable))).trans
      (mid.2.1 u (.inl lower) (.inl (by omega)))
  · exact (final.2.1 u (.inr upper)).trans
      (mid.2.1 u (.inr (by omega)) (.inr (by omega)))

theorem native_any (b location M P H G : ℕ) (m : Memory w)
    (ports : chart.All (Expr.Fits w location)) (safe : ∀q i,(src q i).Fits w location)
    (ptr : A.pointer+span H≤location) (literal : location+56≤A.raw)
    (raw : A.raw+(2*K)*H+span H≤A.base) (room : A.stop D f (b*7) K M P H G Q<2^w) :
    (A.native parse side src chart b location M P H G w).Exec m
      (A.result parse side src chart b location M P H G m) (A.budget parse side src chart b location M P H G w) :=
  (A.native_any_full parse side src chart b location M P H G m ports safe ptr literal raw room).1

end
end Hierarchy.DescentResetStemPackedIssue.Mixed.Layout

end OAI
