import OAI.Hierarchy.DescentResetStemKeyRAM
import OAI.Hierarchy.DescentResetStemHeaders
import OAI.Hierarchy.DescentResetStemIssuer

namespace OAI
/-! # One native signed-key and actor-descriptor issue over all public stem slots -/
namespace Hierarchy.DescentResetStemPackedIssue
open DescentSIMDLookup DescentPackedZip DescentDyadicSpan DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D f b K H G M Q w : ℕ}

def headIndex {K : ℕ} (s : Bool) (i : Fin K) : Fin (2*K) := finProdFinEquiv (finTwoEquiv.symm s,i)

structure Arena where
  raw : ℕ
  base : ℕ

namespace Arena
variable (A : Arena)
def header (D f M : ℕ) := A.base+DescentResetStemKey.words D f M
def mux (D f b K H G M : ℕ) :=
  DescentResetStemHeaders.outputBase H G M b (A.header D f M)+(2*K)*(H*chunks G M)+span (H*chunks G M)
def out (D f b K H G M : ℕ) := A.mux D f b K H G M+DescentResetStemMux.words K (f+2) b M
def stop (D f b K H G M Q : ℕ) := A.out D f b K H G M+Q*(H*chunks G M)

def key (parse : DescentResetStemKey.Decoder D f) (M : ℕ) (side : Fin Q→Bool)
    (src : Fin Q→Fin (D+2)→Expr) (q : Fin Q) := DescentResetStemKey.expr parse M A.base (side q) (src q)
def head (D f b H G M : ℕ) (side : Fin Q→Bool) (q : Fin Q) (j : Fin K) :=
  DescentResetStemHeaders.expr H G M b (A.header D f M) (headIndex (side q) j).val

variable (parse : DescentResetStemKey.Decoder D f) (side : Fin Q→Bool) (src : Fin Q→Fin (D+2)→Expr)
def code (b K H G M w : ℕ) :=
  let pre:=DescentResetStemKey.program parse M w A.base
  let publish:=DescentResetStemHeaders.phase w (2*K) H G M b A.raw (A.header D f M)
  (pre.seq publish.program).seq
    (DescentResetStemIssuer.code (A.mux D f b K H G M) (A.key parse M side src)
      (A.head D f b H G M side (K:=K)) (f+2) b M H G w (A.out D f b K H G M))

def ticks (b K H G M w : ℕ) :=
  let publish:=DescentResetStemHeaders.phase w (2*K) H G M b A.raw (A.header D f M)
  (4+10*DescentResetStemKey.words D f M)+publish.ticks+
    DescentResetStemIssuer.ticks (A.mux D f b K H G M) (A.key parse M side src)
      (A.head D f b H G M side (K:=K)) (f+2) b M H G (A.out D f b K H G M)

def output (b K H G M : ℕ) (m : Memory w) :=
  let first:=DescentResetStemKey.memory parse M A.base m
  let mid:=(DescentResetStemHeaders.phase w (2*K) H G M b A.raw (A.header D f M)).image first
  DescentResetStemIssuer.output (A.mux D f b K H G M) (A.key parse M side src)
    (A.head D f b H G M side (K:=K)) (f+2) b M H G (A.out D f b K H G M) mid

theorem run (m : Memory w) (dead : parse 0=none) (x : Fin Q→Fin H→Fin G→Fin (D+2)→Cell f)
    (descriptor : Fin (2*K)→Fin H→Cell b)
    (inputs : ∀q i,(src q i).Fits w A.base)
    (reads : ∀q i,Source (src q i) (fun h g=>x q h g i) M m)
    (stored : DescentResetStemHeaders.Raw A.raw descriptor m)
    (early : A.raw+(2*K)*H+span H≤A.base) (wide : b*M≤ w)
    (room : A.stop D f b K H G M Q<2^w) :
    let last:=A.output parse side src b K H G M m
    (A.code parse side src b K H G M w).Exec m last (A.ticks parse side src b K H G M w) ∧
    (∀q (p : Row H G M), last (A.out D f b K H G M+q.val*(H*chunks G M)+(row H G M p).val)=
       ((data (fun h g=>DescentResetStemMux.pick (DescentResetStemKey.word parse (side q) (x q h g))
         (fun j=>descriptor (headIndex (side q) j) h)) p).val:Word w)) ∧
    (∀a,a<A.base ∨ A.stop D f b K H G M Q≤ a→last a=m a) ∧ CheapCode (A.code parse side src b K H G M w) := by
  let hdr:=A.header D f M
  let mux:=A.mux D f b K H G M
  let out:=A.out D f b K H G M
  let pub:=DescentResetStemHeaders.phase w (2*K) H G M b A.raw hdr
  let first:=DescentResetStemKey.memory parse M A.base m
  let mid:=pub.image first
  have low : A.base≤ hdr := Nat.le_add_right ..
  have emitted : hdr≤DescentResetStemHeaders.outputBase H G M b hdr := Nat.le_add_right ..
  have broadcast : DescentResetStemHeaders.outputBase H G M b hdr+(2*K)*(H*chunks G M)≤ mux := Nat.le_add_right ..
  have hm : hdr≤ mux := emitted.trans ((Nat.le_add_right ..).trans broadcast)
  have mo : mux≤ out := Nat.le_add_right ..
  have close : out≤A.stop D f b K H G M Q := Nat.le_add_right ..
  have wb:=close.trans_lt room
  have hw:=hm.trans_lt (mo.trans_lt wb)
  obtain ⟨pre,_,_,firstFrame,preCheap⟩:=DescentResetStemKey.mounted parse M A.base m hw
  have oldData : DescentResetStemHeaders.Raw A.raw descriptor first := by
    intro i h
    have lim:=Nat.mul_le_mul_right H i.isLt
    rw [Nat.succ_mul] at lim
    have hv:=h.isLt
    exact (firstFrame _ (.inl (by omega))).trans (stored i h)
  obtain ⟨prep,headers,preserve⟩:=DescentResetStemHeaders.run (G:=G) (M:=M) descriptor first oldData
    (early.trans low) (broadcast.trans_lt (mo.trans_lt wb)) wide
  have original (q : Fin Q):=DescentResetStemKey.issued parse dead (side q) A.base (src q) m (x q)
    (inputs q) (reads q) hw
  have current (q : Fin Q) :
      Source (A.key parse M side src q) (fun v g=>DescentResetStemKey.word parse (side q) (x q v g)) M mid := by
    intro p
    exact (eval_below _ _ first mid (original q).1 (fun a ha=>preserve a (.inl ha))).trans ((original q).2 p)
  have cap (q : Fin Q) (j : Fin K) : (A.head D f b H G M side q j).Fits w mux :=
    DescentResetStemHeaders.expr_fits (headIndex (side q) j) le_rfl (mo.trans_lt wb)
  have tail:=DescentResetStemIssuer.run mux (A.key parse M side src) (A.head D f b H G M side (K:=K)) out
    (fun q h g=>DescentResetStemKey.word parse (side q) (x q h g)) (fun q j=>descriptor (headIndex (side q) j))
    mid (fun q=>ProtocolRAMGeneratedWrite.fits_mono _ hm (original q).1) cap current
    (fun q j=>headers (headIndex (side q) j)) le_rfl room
  refine ⟨?_,tail.2.1,?_,cheap_seq (cheap_seq preCheap pub.cheap) tail.2.2.2⟩
  · intro nPC nReg nPub machine pc reg slots exit rom advice cfg rawMem enter same
    exact Procedure.Exec.then (Procedure.Exec.then pre prep) tail.1 machine pc reg slots exit rom advice cfg rawMem enter same
  intro a ha
  rcases ha with before|after
  · exact (tail.2.2.1 a (.inl (before.trans_le (low.trans hm))) (.inl (before.trans_le (low.trans (hm.trans mo))))).trans
      ((preserve a (.inl (before.trans_le low))).trans (firstFrame a (.inl before)))
  · exact (tail.2.2.1 a (.inr (close.trans after)) (.inr after)).trans
      ((preserve a (.inr (broadcast.trans (mo.trans (close.trans after))))).trans (firstFrame a (.inr (hm.trans (mo.trans (close.trans after))))))

end Arena
end
end Hierarchy.DescentResetStemPackedIssue

end OAI
