import OAI.Hierarchy.DescentOverlapRAM
import OAI.Hierarchy.DescentOverlapCount

namespace OAI
/-! # The installed cost of an arbitrary-width packed handoff -/
namespace Hierarchy.DescentSIMDLookup.Overlap
open ProtocolRAM DescentPackedZip DescentColonies.SplitRAM
open DescentStaticWordColumn (names names_mount names_seq names_scan)
noncomputable section

theorem body_work (base H G A B a : ℕ) (src : Bank) :
    (body base H G A B a src).work≤1+40*pieces G A B := by
  have bound (j : Fin (pieces G A B)) : (term base H G A B a src j).work≤39 := by change 35≤39;decide
  simpa [body,Nat.mul_comm] using work_total _ 39 bound (List.finRange _)

/-- The shared dictionaries may have exponentially many entries in one short
word. Every other scan or installed row is linear in the two packed grids. -/
theorem tariff (base H G A B a w : ℕ) (src : Bank) (oldPos : 0< A) (newPos : 0< B) :
    ticks base H G A B a src+7*names (program base H G A B a w src) ≤
      2048*((pieces G A B+1)*(A+1)*2^(a*A)+rows H G A+rows H G B+1) := by
  let P:=pieces G A B
  let c:=rows H G B
  let e:=rows H G A
  let d:=P*2^keyBits a A
  let m:=(P+1)*2^mapBits H G B
  let work:=(body base H G A B a src).work
  have price_ : ticks base H G A B a src+7*names (program base H G A B a w src)=
      299+115*(m+d)+c*(2*work+4)+28*work := by
    simp only [program,tables,DescentOrdinaryAtomFieldRAM.ROM.mount,names_seq,names_mount,names_scan,
      ticks,dest,dictBase]
    dsimp [m,d,c,work,P];omega
  have wlim : work≤1+40*P:=body_work ..
  have joined : c*P≤2*(e+c):=by
    have h:=Nat.mul_le_mul_left H (probes (G:=G) oldPos newPos)
    dsimp [P,c,e,rows,pieces]; nlinarith only [h]
  have wk : c*work≤ c*(1+40*P):=Nat.mul_le_mul_left _ wlim
  have du : d≤2*(P*(A+1)*2^(a*A)):=by
    have h:=Nat.mul_le_mul_right (P*2^(a*A)) (rounded A)
    dsimp [d,keyBits];rw [pow_add];nlinarith only [h]
  have mu : m≤2*((P+1)*(c+1)):=by
    have h:=Nat.mul_le_mul_left (P+1) (rounded c)
    dsimp [m,mapBits]; nlinarith only [h]
  have powPos : 1≤2^(a*A):=Nat.two_pow_pos _
  have seed : P+1≤(P+1)*(A+1)*2^(a*A):=by
    exact (Nat.le_mul_of_pos_right _ (Nat.succ_pos A)).trans (Nat.le_mul_of_pos_right _ powPos)
  have dict : P*(A+1)*2^(a*A)≤(P+1)*(A+1)*2^(a*A):=by gcongr;omega
  rw [price_]
  change _≤2048*((P+1)*(A+1)*2^(a*A)+e+c+1)
  nlinarith only [wlim,joined,wk,du,mu,seed,dict]

end
end Hierarchy.DescentSIMDLookup.Overlap

end OAI
