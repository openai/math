import OAI.Hierarchy.DescentDenseParentColumn

namespace OAI
/-! # A bounded destination for every possible reset survivor word and ordinal -/
namespace Hierarchy.DescentParentBoundedKey
open DescentHubBits DescentCensusRAM DescentIssuedTerminalId ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section

def destination (bins H : ℕ) (flags ids : Bank) : Expr :=
  let id := Expr.lookup ids .row
  .op .add (.lit bins) (.branch .eq (.lookup flags .row) (.lit 0) (.lit H)
    (.branch .lt id (.lit H) id (.lit H)))

def clipped {w : ℕ} (H : ℕ) (flag idx : Word w) : Fin (H+1) :=
  if ok : flag≠0 ∧ idx.val<H then ⟨idx.val,by omega⟩ else Fin.last H

theorem digit {n w : ℕ} (bins H : ℕ) (flags ids : Bank) (m : Memory w) (i : Fin n) (small : H<2^w) :
    let f:=(Expr.lookup flags .row).eval m (i.val:Word w)
    let j:=(Expr.lookup ids .row).eval m (i.val:Word w)
    (destination bins H flags ids).eval m (i.val:Word w)=((bins+(clipped H f j).val:ℕ):Word w) := by
  intro f j
  have hc : (H:Word w).val=H:=Fin.val_cast_of_lt small
  change (bins:Word w)+(if (f==0) then (H:Word w) else if decide (j<(H:Word w)) then j else (H:Word w))=_
  by_cases ff:f=0
  · simp [ff,clipped]
  · by_cases hj:j.val<H
    · have lt : j<(H:Word w):=by change j.val<(H:Word w).val; rwa [hc]
      simp [ff,hj,lt,clipped]
    · have nl : ¬j<(H:Word w):=by change ¬j.val<(H:Word w).val; rwa [hc]
      simp [ff,hj,nl,clipped]

theorem fits {w n H : ℕ} (b : Banks w n (H+1)) {flags ids : Bank}
    (f : flags.Fits w b.first) (i : ids.Fits w b.first) : (destination b.bins H flags ids).Fits w b.first :=
  ⟨trivial,⟨f,trivial⟩,trivial,trivial,⟨i,trivial⟩,trivial,⟨i,trivial⟩,trivial⟩

def targetIn {n w : ℕ} (H : ℕ) (flags ids : Bank) (m : Memory w) (i : Fin n) :=
  clipped H ((Expr.lookup flags .row).eval m (i.val:Word w)) ((Expr.lookup ids .row).eval m (i.val:Word w))

/-- On an actual survivor the bounded and original directory choose the same bin, also on every ghost. -/
theorem genuine {V : Type} [Fintype V] {n H w : ℕ} (sparse : V↪Fin n) (rank : V↪Fin H)
    (b : Banks w n (H+1)) (flags ids : Bank) (m : Memory w) (ff : flags.Fits w b.first)
    (idf : ids.Fits w b.first) (nf : n≤flags.size) (ni : n ≤ ids.size)
    (bit : ∀i : Fin n,m (flags.base+i.val)=(if active sparse i then 1 else 0))
    (ord : ∀v,m (ids.base+(sparse v).val)=((rank v).val:Word w)) :
    targetIn H flags ids m=target sparse rank := by
  funext i
  have flag:=(lookup_nat flags m (i.val:Word w) .row i.val rfl (i.isLt.trans_le nf) ff.2.1).trans (bit i)
  have one : 1<2^w:=lt_of_le_of_lt ff.1 ff.2.1
  have total : H<2^w:=by have:=b.finish;omega
  by_cases live : active sparse i
  · have idRead:=(lookup_nat ids m (i.val:Word w) .row i.val rfl (i.isLt.trans_le ni) idf.2.1).trans
        (by simpa [live.choose_spec] using ord live.choose)
    have lt:=(rank live.choose).isLt
    have wide : w ≠ 0:=by rintro rfl;norm_num at one
    have nz : (1:Word w)≠0:=by simpa [Fin.ext_iff] using wide
    apply Fin.ext
    simp [targetIn,clipped,target,flag,live,idRead,nz,Fin.val_cast_of_lt (lt.trans total),lt]
  · simp [targetIn,clipped,target,flag,live]

theorem cost {w n H : ℕ} (b : Banks w n (H+1)) (flags ids codes : Bank) :
    (10+(3+12*n))+tallyCost b (destination b.bins H flags ids) (.lookup codes .row)≤240*(1+n+H) := by
  simp only [tallyCost,addCost,issueCost,slot,ProtocolRAMGeneratedWrite.work,destination,Expr.work]
  omega
end
end Hierarchy.DescentParentBoundedKey

end OAI
