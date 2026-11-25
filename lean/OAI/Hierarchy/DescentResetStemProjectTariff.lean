import OAI.Hierarchy.DescentResetStemProject
import OAI.Hierarchy.DescentOverlapTariff
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # The time, hardware count and physical footprint of the stem projection -/
namespace Hierarchy.DescentResetStemProject
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentStaticWordColumn (names names_seq)
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

def volume (N H G X a A M : ℕ) :=
  let g:=G*X
  let n:=N*H
  let overlap:=(Overlap.pieces g A (M*X)+1)*(A+1)*2^(a*A)
  let old:=Overlap.rows n g A
  let next:=Overlap.rows n g (M*X)
  let projection:=DescentVectorBookReshape.dictionaryWords X a M
  let fields:=N*DescentVectorBookReshape.rows H 1 G X M
  N+old+next+overlap+projection+fields+H*chunks G M+1

private theorem gather_names {N : ℕ} (src : Fin N→Bank) (H G A base w : ℕ) :
    names (ProtocolRAM.program w (gatherPasses src H G A base))≤15+N*39 := by
  apply le_trans (ProbeStage.Native.columns_text w (H*chunks G A) base 7 _ ?_)
  · simp only [gatherFields,List.length_ofFn,le_refl]
  · intro _ h
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp h
    exact le_rfl

theorem tariff {N : ℕ} (base H G X a A M w : ℕ) (src : Fin N→Bank)
    (oldPositive : 0<A) (blockPositive : 0<X) (newPositive : 0<M) :
    ticks base H G X a A M src + 7*names (program base H G X a A M src w)
      ≤4096*volume N H G X a A M := by
  let g:=G*X
  let lanes:=M*X
  let n:=N*H
  let middle:=overlapBase base N H G X A
  let copy:=gathered base N H G X A
  let cvt:=converted base N H G X a A M
  let books:=reshapeBase base N H G X a A M
  let dst:=out base N H G X a A M
  have old : clock (gatherPasses src H g A base)≤4+4*N+18*Overlap.rows n g A :=
    (gather_clock src H g A base).trans_eq (by dsimp only [Overlap.rows,n];ring)
  have text:=gather_names src H g A base w
  have overlap:=Overlap.tariff middle n g A lanes a w copy oldPositive (Nat.mul_pos newPositive blockPositive)
  have vector:=DescentVectorBookReshape.ticks_eq N H 1 G X a M
  have hw:=DescentVectorBookReshape.names (N:=N) (H:=H) (Q:=1) (J:=G) (r:=X) (a:=a) (M:=M)
    (w:=w) books dst cvt
  rw [program,names_seq,names_seq,ticks]
  dsimp only [volume,DescentVectorBookReshape.cells,dst,books,cvt,copy,middle,n,lanes,g] at *
  omega

theorem space_bound (base N H G X a A M : ℕ) (oldPositive : 0<A)
    (blockPositive : 0<X) (newPositive : 0<M) :
    endAddress base N H G X a A M≤base+4096*volume N H G X a A M := by
  let source:=N*(H*chunks (G*X) A)
  let depth:=(N*H)*chunks (G*X) (M*X)
  let host:=H*chunks G M
  let records:=N*DescentVectorBookReshape.rows H 1 G X M
  let dt:=DescentVectorBookReshape.dictionaryWords X a M
  let middle:=overlapBase base N H G X A
  let after:=Overlap.dest middle (N*H) (G*X) A (M*X) a
  let src:=gathered base N H G X A
  have before : middle≤after:=by change middle≤ middle+_+_;omega
  have growth:=Overlap.tariff middle (N*H) (G*X) A (M*X) a 1 src oldPositive (Nat.mul_pos newPositive blockPositive)
  have diff : after-middle≤Overlap.ticks middle (N*H) (G*X) A (M*X) a src := by
    change after-middle≤8+10*(after-middle)+_
    omega
  have pad (t : ℕ) : 2^Nat.clog 2 (t+1)≤2*t+3 := by
    have := DescentDyadicSpan.span_le (t+1)
    dsimp only [DescentDyadicSpan.span] at this
    omega
  have first:=pad source
  have second:=pad depth
  have third:=pad dt
  have fourth:=pad records
  have last:=pad host
  have addr : endAddress base N H G X a A M=
      after+2^Nat.clog 2 (depth+1)+(dt+2*records)+2^Nat.clog 2 (dt+1)+
        2^Nat.clog 2 (records+1)+records+2^Nat.clog 2 (host+1) := by
    rfl
  have start : middle=base+2^Nat.clog 2 (source+1):=rfl
  have old : Overlap.rows (N*H) (G*X) A=source:=Nat.mul_assoc ..
  have short : Overlap.rows (N*H) (G*X) (M*X)=depth:=rfl
  rw [addr]
  simp only [volume,old,short] at *
  change after + _ + (dt+2*records) + _ + _ + records + _ ≤
    base+4096*(N+source+depth+_+dt+records+host+1)
  omega

end
end Hierarchy.DescentResetStemProject

end OAI
