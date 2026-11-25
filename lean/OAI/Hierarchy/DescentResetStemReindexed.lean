import OAI.Hierarchy.DescentResetStemKeyColumns
import OAI.Hierarchy.DescentResetStemKeyReindex
import OAI.Hierarchy.DescentResetStemPackedIssue

namespace OAI
/-! # Physical stem issue between independently sized predecessor and receiver populations -/
namespace Hierarchy.DescentResetStemPackedIssue.Mixed
open DescentSIMDLookup DescentPackedZip DescentDyadicSpan DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D f b K P H G M Q w : ℕ}

structure Layout where
  raw : ℕ
  pointer : ℕ
  base : ℕ

namespace Layout
variable (A : Layout)
def mapping (D f M P G Q : ℕ) := DescentResetStemKey.Columns.stop A.base D f M P G Q
def hdr (D f M P H G Q : ℕ) := A.mapping D f M P G Q+DescentResetStemKeyReindex.size P H G M
def mux (D f b K M P H G Q : ℕ) :=
  DescentResetStemHeaders.outputBase H G M b (A.hdr D f M P H G Q)+(2*K)*(H*chunks G M)+span (H*chunks G M)
def out (D f b K M P H G Q : ℕ) := A.mux D f b K M P H G Q+DescentResetStemMux.words K (f+2) b M
def stop (D f b K M P H G Q : ℕ) := A.out D f b K M P H G Q+Q*(H*chunks G M)
def key (D f M P H G : ℕ) (q : Fin Q) : Expr :=
  DescentResetStemKeyReindex.keyExpr (DescentResetStemKey.Columns.bank A.base D f M P G q.val)
    (A.mapping D f M P G Q) A.pointer P H G M
def heads (D f b M P H G : ℕ) (side : Fin Q→Bool) (q : Fin Q) (i : Fin K) : Expr :=
  DescentResetStemHeaders.expr H G M b (A.hdr D f M P H G Q) (headIndex (side q) i).val

variable (parse : DescentResetStemKey.Decoder D f) (side : Fin Q→Bool) (src : Fin Q→Fin (D+2)→Expr)
def code (b K M P H G w : ℕ) :=
  let p:=DescentResetStemKey.Columns.code parse side src A.base M P G w
  let r:=DescentResetStemKeyReindex.phase w (A.mapping D f M P G Q) P H G M
  let h:=DescentResetStemHeaders.phase w (2*K) H G M b A.raw (A.hdr D f M P H G Q)
  let e:=DescentResetStemIssuer.code (A.mux D f b K M P H G Q) (A.key D f M P H G) (A.heads D f b M P H G side (K:=K))
    (f+2) b M H G w (A.out D f b K M P H G Q)
  ((p.seq r.program).seq h.program).seq e

def ticks (b K M P H G w : ℕ) :=
  DescentResetStemKey.Columns.ticks parse side src A.base M P G+
  (DescentResetStemKeyReindex.phase w (A.mapping D f M P G Q) P H G M).ticks+
  (DescentResetStemHeaders.phase w (2*K) H G M b A.raw (A.hdr D f M P H G Q)).ticks+
  DescentResetStemIssuer.ticks (A.mux D f b K M P H G Q) (A.key D f M P H G) (A.heads D f b M P H G side (K:=K))
    (f+2) b M H G (A.out D f b K M P H G Q)

def output (b K M P H G : ℕ) (m : Memory w) :=
  let first:=DescentResetStemKey.Columns.output parse side src A.base M P G m
  let mapped:=(DescentResetStemKeyReindex.phase w (A.mapping D f M P G Q) P H G M).image first
  let posted:=(DescentResetStemHeaders.phase w (2*K) H G M b A.raw (A.hdr D f M P H G Q)).image mapped
  DescentResetStemIssuer.output (A.mux D f b K M P H G Q) (A.key D f M P H G) (A.heads D f b M P H G side (K:=K))
    (f+2) b M H G (A.out D f b K M P H G Q) posted

theorem run (m : Memory w) (dead : parse 0=none) (x : Fin Q→Fin P→Fin G→Fin (D+2)→Cell f)
    (owner : Fin H→Fin P) (desc : Fin (2*K)→Fin H→Cell b)
    (inputs : ∀q i,(src q i).Fits w A.base) (reads : ∀q i,Source (src q i) (fun h g=>x q h g i) M m)
    (directory : DescentResetStemKeyReindex.Directory A.pointer owner m)
    (stored : DescentResetStemHeaders.Raw A.raw desc m)
    (ptrRoom : A.pointer+span H≤A.base) (early : A.raw+(2*K)*H+span H≤A.base) (wide : b*M≤ w)
    (room : A.stop D f b K M P H G Q<2^w) :
    let last:=A.output parse side src b K M P H G m
    (A.code parse side src b K M P H G w).Exec m last (A.ticks parse side src b K M P H G w) ∧
    (∀q (p : Row H G M),last (A.out D f b K M P H G Q+q.val*(H*chunks G M)+(row H G M p).val)=
      ((data (fun h g=>DescentResetStemMux.pick (DescentResetStemKey.word parse (side q) (x q (owner h) g))
        (fun j=>desc (headIndex (side q) j) h)) p).val:Word w)) ∧
    (∀a,a<A.base ∨ A.stop D f b K M P H G Q≤ a→last a=m a) ∧ CheapCode (A.code parse side src b K M P H G w) := by
  let mapBase:=A.mapping D f M P G Q
  let headBase:=A.hdr D f M P H G Q
  let muxBase:=A.mux D f b K M P H G Q
  let emit:=A.out D f b K M P H G Q
  let first:=DescentResetStemKey.Columns.output parse side src A.base M P G m
  let remap:=DescentResetStemKeyReindex.phase w mapBase P H G M
  let pub:=DescentResetStemHeaders.phase w (2*K) H G M b A.raw headBase
  let mid:=remap.image first
  let sent:=pub.image mid
  let z0:=DescentResetStemHeaders.outputBase H G M b headBase+(2*K)*(H*chunks G M)
  have lm : A.base≤ mapBase := by dsimp [mapBase,mapping,DescentResetStemKey.Columns.stop,DescentResetStemKey.Columns.start];omega
  have mh : mapBase≤ headBase := Nat.le_add_right ..
  have hz : headBase≤ z0 := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have zm : z0≤ muxBase:=Nat.le_add_right ..
  have ml : muxBase≤ emit:=Nat.le_add_right ..
  have end_ : emit≤A.stop D f b K M P H G Q:=Nat.le_add_right ..
  have wf:=end_.trans_lt room
  have wh:=hz.trans_lt (zm.trans_lt (ml.trans_lt wf))
  have wm:=mh.trans_lt wh
  obtain ⟨cpu,keyRows,frm,c1⟩:=DescentResetStemKey.Columns.run parse side src A.base m dead x inputs reads wm
  have mapped:=DescentResetStemKeyReindex.run (H₀:=P) (H₁:=H) (G:=G) (M:=M) first wh
  have ptr : DescentResetStemKeyReindex.Directory A.pointer owner first := by
    intro h
    have i:=h.isLt.trans_le (span_ge H)
    exact (frm _ (.inl (by omega))).trans (directory h)
  have projection (q : Fin Q):=
    let ok:=DescentResetStemKey.Columns.bank_fits A.base D f M P G Q w q wm
    DescentResetStemKeyReindex.source (DescentResetStemKey.Columns.bank A.base D f M P G q.val)
      (fun h g=>DescentResetStemKey.word parse (side q) (x q h g)) owner first (keyRows q) ptr ok.1 ok.2
      (ptrRoom.trans lm) wh
  have raw : DescentResetStemHeaders.Raw A.raw desc mid := by
    intro j h
    have sz:=Nat.mul_le_mul_right H j.isLt
    rw [Nat.succ_mul] at sz
    have iv:=h.isLt
    have before : A.raw+j.val*H+h.val<A.base:=by omega
    exact (mapped.2.2 _ (.inl (before.trans_le lm))).trans ((frm _ (.inl before)).trans (stored j h))
  obtain ⟨post,headers,frame⟩:=DescentResetStemHeaders.run (G:=G) (M:=M) desc mid raw
    (early.trans (lm.trans mh)) (zm.trans_lt (ml.trans_lt wf)) wide
  have headsFit (q : Fin Q) (j : Fin K) : (A.heads D f b M P H G side q j).Fits w muxBase :=
    DescentResetStemHeaders.expr_fits (headIndex (side q) j) le_rfl (ml.trans_lt wf)
  have lookup (q : Fin Q) : Source (A.key D f M P H G q)
      (fun h g=>DescentResetStemKey.word parse (side q) (x q (owner h) g)) M sent := by
    intro p
    exact (eval_below _ _ mid sent (projection q).1 (fun a ha=>frame a (.inl ha))).trans ((projection q).2 p)
  have tail:=DescentResetStemIssuer.run muxBase (A.key D f M P H G) (A.heads D f b M P H G side (K:=K)) emit
    (fun q h g=>DescentResetStemKey.word parse (side q) (x q (owner h) g)) (fun q j=>desc (headIndex (side q) j))
    sent (fun q=>ProtocolRAMGeneratedWrite.fits_mono _ (hz.trans zm) (projection q).1) headsFit lookup
    (fun q i=>headers (headIndex (side q) i)) le_rfl room
  refine ⟨?_,tail.2.1,?_,cheap_seq (cheap_seq (cheap_seq c1 remap.cheap) pub.cheap) tail.2.2.2⟩
  · intro nPC nReg nPub machine pc reg slots exit rom advice cfg rawMem enter same
    exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then cpu mapped.1) post) tail.1
      machine pc reg slots exit rom advice cfg rawMem enter same
  intro a ha
  rcases ha with before|after
  · have p:=before.trans_le lm
    have h:=p.trans_le mh
    have u:=h.trans_le (hz.trans zm)
    exact (tail.2.2.1 a (.inl u) (.inl (u.trans_le ml))).trans
      ((frame a (.inl h)).trans ((mapped.2.2 a (.inl p)).trans (frm a (.inl before))))
  · have u:=end_.trans after
    have h:=(zm.trans ml).trans u
    exact (tail.2.2.1 a (.inr u) (.inr after)).trans
      ((frame a (.inr h)).trans ((mapped.2.2 a (.inr (hz.trans h))).trans (frm a (.inr ((mh.trans hz).trans h)))))

theorem clock_bound (b K M P H G w U : ℕ) (small : ∀q i,(src q i).work≤U) :
    let oldRows:=P*chunks G M
    let newRows:=H*chunks G M
    let gate:=14+(D+2)*(U+11)
    A.ticks parse side src b K M P H G w ≤
      ((4+10*DescentResetStemKey.words D f M)+(4+Q*(4+oldRows*(2*gate+4))))+
      (4+10*(span P+2*span newRows))+
      (4+10*DescentResetStemHeaders.romSize b newRows+(4+(2*K)*(4+54*newRows)))+
      ((4+10*DescentResetStemMux.words K (f+2) b M)+(4+Q*(4+newRows*(2*(1+K*(30+7+22))+4)))) := by
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · exact Nat.add_le_add_right (DescentResetStemKey.Columns.clock_bound parse side src A.base M P G U small) _
    · exact DescentResetStemHeaders.ticks w (2*K) H G M b A.raw (A.hdr D f M P H G Q)
  · exact DescentResetStemIssuer.clock_bound (A.mux D f b K M P H G Q)
      (A.key D f M P H G) (A.heads D f b M P H G side (K:=K))
      (f+2) b M H G (A.out D f b K M P H G Q) 30 7 (fun _=>le_rfl) (fun _ _=>le_rfl)

end Layout
export Layout (run clock_bound)
end
end Hierarchy.DescentResetStemPackedIssue.Mixed

end OAI
