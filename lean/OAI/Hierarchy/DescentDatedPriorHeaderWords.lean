import OAI.Hierarchy.DescentDatedPriorHeaderRuns

namespace OAI
/-! Earlier words in the same physical poststate, with the flattened
indices of both the single and paired walk recovered literally. -/
namespace Hierarchy.DescentDatedAddressBook.PriorHeader
open DescentHaloWalkRAM DescentPackedColony DescentSIMDLookup DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w H G M D:ℕ}
local notation "P"=>breadth D
local notation "N"=>H*P
local notation "L"=>H*(P*P)
local notation "n"=>H*chunks G M
local notation "pitch"=>stride H G M D
theorem quot {K:ℕ} (h:ℕ) (j:Fin K):(h*K+j.val)/K=h:=by
  rw [Nat.mul_comm h,Nat.mul_add_div (Nat.zero_lt_of_lt j.isLt),Nat.div_eq_of_lt j.isLt,Nat.add_zero]
theorem rem {K:ℕ} (h:ℕ) (j:Fin K):(h*K+j.val)%K=j.val:=by
  rw [Nat.mul_comm h,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt j.isLt]
theorem rect {U V:ℕ} (h:Fin U) (j:Fin V):(finProdFinEquiv (h,j)).val=h.val*V+j.val:=by
  simp [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
theorem row_rect (v:Fin H) (p:Fin P):(DescentHaloWalkRAM.row v p).val=v.val*P+p.val:=rect v p
theorem pair_rect (v:Fin H) (p q:Fin P):(Ranks.id v (PairRanks.pair p q)).val=v.val*(P*P)+(p.val*P+q.val):=by
  rw [show (Ranks.id v (PairRanks.pair p q)).val=v.val*(P*P)+(PairRanks.pair p q).val from rect ..]
  exact congrArg _ (rect p q)

variable (base:ℕ) (adj:Bank)
local notation "col"=>bank H G M D base
local notation "top"=>endAddress H G M D base
local notation "out"=>image H G M D base adj
variable (ok:Room adj H G M D base w) (m:Memory w)
include ok
theorem literal_word (j:ℕ) (room:j<P+13) (i:ℕ) (lo:i<pitch):
    out m ((col j).base+i)=(digits G M D j i:Word w):=by
  have strict:j*pitch+i<(P+13)*pitch:=(Nat.add_lt_add_left lo _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ room)
  have v:=(all_written H G M D base adj ok m).1 ⟨j*pitch+i,strict⟩
  simpa only [bank,start,literal,Fin.val_mk,Nat.add_assoc,quot j (⟨i,lo⟩:Fin pitch),rem j (⟨i,lo⟩:Fin pitch)] using v

local notation "walk"=>walks H G M D base adj
local notation "rk4"=>ranks4 H G M D base
local notation "first"=>duplicates H G M D base
local notation "rev"=>reversals H G M D base
local notation "mix"=>pairs H G M D base
local notation "rk8"=>ranks8 H G M D base
theorem raw_steps:
    (∀i:Fin N,out m ((ends H G M D base).base+i.val)=(DescentHaloWalkRAM.body walk H D 4).eval (out m) (i.val:Word w)) ∧
    (∀i:Fin N,out m ((localRank H G M D base).base+i.val)=(Ranks.body rk4 P).eval (out m) (i.val:Word w)) ∧
    (∀i:Fin N,out m ((visited H G M D base).base+i.val)=(Gather.onceRow first H P).eval (out m) (i.val:Word w)) ∧
    (∀i:Fin N,out m ((reverseRank H G M D base).base+i.val)=(Rebase.body rev .rank H D).eval (out m) (i.val:Word w)) ∧
    (∀i:Fin N,out m ((reversePath H G M D base).base+i.val)=(Rebase.body rev .path H D).eval (out m) (i.val:Word w)) ∧
    (∀i:Fin L,out m ((priorEnds H G M D base).base+i.val)=(PairRanks.op mix H).eval (out m) (i.val:Word w)) ∧
    (∀i:Fin L,out m ((priorRanks H G M D base).base+i.val)=(Ranks.body rk8 (P*P)).eval (out m) (i.val:Word w)):=by
  have r:=all_written H G M D base adj ok m
  simp only [jobs,SignedPrefix.Written,SignedPrefix.Job.Written,SignedPrefix.Job.width,Nat.one_mul] at r
  rcases r with ⟨_,w1,w2,w3,w4,w5,w6,w7,_⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    have eqn:=w1 (0:Fin 1) i
    simp only [Fin.val_zero,Nat.zero_mul,Nat.add_zero] at eqn
    refine Eq.trans (congrArg (out m) ?_) eqn
    change base+(P+13)*pitch+i.val=_
    ring
  · intro i
    have eqn:=w2 (0:Fin 1) i
    simp only [Fin.val_zero,Nat.zero_mul,Nat.add_zero] at eqn
    refine Eq.trans (congrArg (out m) ?_) eqn
    change base+(P+14)*pitch+i.val=_
    ring
  · intro i
    have eqn:=w3 (0:Fin 1) i
    simp only [Fin.val_zero,Nat.zero_mul,Nat.add_zero] at eqn
    refine Eq.trans (congrArg (out m) ?_) eqn
    change base+(P+15)*pitch+i.val=_
    ring
  · intro i
    have eqn:=w4 (0:Fin 1) i
    simp only [Fin.val_zero,Nat.zero_mul,Nat.add_zero] at eqn
    refine Eq.trans (congrArg (out m) ?_) eqn
    change base+(P+16)*pitch+i.val=_
    ring
  · intro i
    have eqn:=w5 (0:Fin 1) i
    simp only [Fin.val_zero,Nat.zero_mul,Nat.add_zero] at eqn
    refine Eq.trans (congrArg (out m) ?_) eqn
    change base+(P+17)*pitch+i.val=_
    ring
  · intro i
    have eqn:=w6 (0:Fin 1) i
    simp only [Fin.val_zero,Nat.zero_mul,Nat.add_zero] at eqn
    refine Eq.trans (congrArg (out m) ?_) eqn
    change base+(P+18)*pitch+i.val=_
    ring
  · intro i
    have eqn:=w7 (0:Fin 1) i
    simp only [Fin.val_zero,Nat.zero_mul,Nat.add_zero] at eqn
    refine Eq.trans (congrArg (out m) ?_) eqn
    change base+(P+19)*pitch+i.val=_
    ring

variable (R:Fin H→Fin D→Option (Fin H)) (old:∀(v:Fin H) (j:Fin D),m (adj.base+v.val*D+j.val)=(number (R v j):Word w))
include old
local notation "R₄"=>Gather.reaching R
theorem walk_words:DescentHaloWalkRAM.Reads walk R (out m):=by
  have cap:=limits H G M D
  constructor
  · intro v j
    have addr:v.val*D+j.val<H*D:=(rect v j) ▸ (finProdFinEquiv (v,j)).isLt
    have earlier:adj.base+(v.val*D+j.val)<base:=(Nat.add_lt_add_left (addr.trans_le ok.oldSize) _).trans_le ok.old.2.2
    have kept:=(any H G M D base adj ok m).2 _ (.inl (by omega))
    simpa only [walks,Nat.add_assoc] using kept.trans (by simpa only [Nat.add_assoc] using old v j)
  · intro v p
    have lo:=(DescentHaloWalkRAM.row v p).isLt.trans_le cap.2.2.1
    simpa only [walks,digits,ite_true,eq_self,row_rect,quot] using (literal_word base adj ok m 0 (by omega) (DescentHaloWalkRAM.row v p).val lo)
  · intro v p j
    have lo:=(DescentHaloWalkRAM.row v p).isLt.trans_le cap.2.2.1
    have j₁:1+j.val≠0:=by omega
    have j₂:1+j.val-1=j.val:=by omega
    have mod:(⟨(v.val*P+p.val)%P,Nat.mod_lt _ cap.1⟩:Fin P)=p:=Fin.ext (rem _ _)
    simpa only [walks,digits,ite_eq_right j₁,j₂,dite_eq_left j.isLt,row_rect,mod,Fin.eta] using (literal_word base adj ok m (1+j.val) (by omega) (DescentHaloWalkRAM.row v p).val lo)

end
end Hierarchy.DescentDatedAddressBook.PriorHeader

end OAI
