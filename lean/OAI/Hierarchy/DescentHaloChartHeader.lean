import OAI.Hierarchy.DescentColonySplitRAM
import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.DescentSharedCableSerial

namespace OAI
/-! # The resident per-rack chart, finite digit assembly, and its physical bounds -/
namespace Hierarchy.DescentHaloPackedRebase
open DescentSIMDLookup DescentSharedCableNames DescentColonies.SplitRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H G M w P : ℕ}
local notation "b" => Packed.bits P

def field (value : Fin (P+1)) : Cell b:=⟨value.val,value.isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩
def digest (table : Fin P→Fin (P+1)) : Cell (b*P) := encode _ _ (fun j=>field (table j))

def fetch (P : ℕ) (owned : Cell (Packed.bits P*P)) (query : Cell (Packed.bits P)) : Cell (Packed.bits P) :=
  Packed.token ((Packed.readToken P query).bind fun p=>
    let v:=(encode (Packed.bits P) P).symm owned p
    if good : v.val<P then some ⟨v.val,good⟩ else none)

theorem fetch_at (table : Fin P→Fin (P+1)) (p : Fin P) (rank : Fin P) (valid : (table p).val=rank.val) :
    fetch P (digest table) (Packed.token (some p))=Packed.token (some rank) :=by
  have fits : (table p).val<P:=by rw [valid];exact rank.isLt
  simp only [fetch,digest,Packed.token_back,Option.bind_some,Equiv.symm_apply_apply,field,dite_eq_left fits]
  exact congrArg (fun x : Fin P=>Packed.token (some x)) (Fin.ext valid)

theorem ghost : fetch P 0 0=0:=by simp [fetch,Packed.readToken,Packed.token]

/-- One static table per shared walk index, used to place its short digit in
all occupied lanes. The common chart itself is never copied once per group. -/
def shift (P M i used value : ℕ) := ∑j : Fin M,if j.val<used then value*(2^Packed.bits P)^i*(2^(Packed.bits P*P))^j.val else 0

theorem pieces (value : Fin H→Fin P→Fin (P+1)) (p : Row H G M) :
    (data (fun h (_:Fin G)=>digest (value h)) p).val = ∑i : Fin P,shift P M i.val (used G M p.2.val) (value p.1 i).val :=by
  change (∑j : Fin M,((if live : p.2.val*M+j.val<G then digest (value p.1) else 0):Cell (b*P)).val*(2^(b*P))^j.val)=_
  unfold shift;rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro j _
  by_cases live : p.2.val*M+j.val<G
  · rw [dite_eq_left live];have kept:=active j live;simp only [ite_eq_left kept]
    change (∑i : Fin P,(value p.1 i).val*(2^b)^i.val)*(2^(b*P))^j.val=_
    rw [Finset.sum_mul]
  · have missed : ¬j.val<used G M p.2.val:=by unfold used;omega
    simp [live,missed]

structure Headers (P : ℕ) where
  chart : Bank
  block : Bank
  live : Bank
  spread : Fin P→Bank

structure Fits (T : Headers P) (H G M w out : ℕ) : Prop where
  chart : T.chart.Fits w out
  block : T.block.Fits w out
  live : T.live.Fits w out
  spread : ∀i,(T.spread i).Fits w out
  chartSize : H*P≤T.chart.size
  blockSize : H*chunks G M≤T.block.size
  liveSize : H*chunks G M≤T.live.size
  spreadSize : ∀i,(M+1)*(P+1)≤(T.spread i).size

structure Reads (T : Headers P) (value : Fin H→Fin P→Fin (P+1)) (M G : ℕ) (m:Memory w) : Prop where
  chart : ∀h p,m (T.chart.base+(h.val*P+p.val))=((value h p).val:Word w)
  block : ∀p : Row H G M,m (T.block.base+(row H G M p).val)=((p.1.val*P:ℕ):Word w)
  live : ∀p : Row H G M,m (T.live.base+(row H G M p).val)=((used G M p.2.val*(P+1):ℕ):Word w)
  spread : ∀(i : Fin P)(input : Fin (P+1))(n : Fin (M+1)),m ((T.spread i).base+(n.val*(P+1)+input.val))=(shift P M i.val n.val input.val:Word w)

def term (T : Headers P) (i : Fin P) : Expr:=.lookup (T.spread i)
  (.op .add (.lookup T.live .row) (.lookup T.chart (.op .add (.lookup T.block .row) (.lit i.val))))
def context (T : Headers P) :=total (term T) (List.finRange P)

private theorem eval_total {X : Type} (e:X→Expr) (v:X→ℕ) (m:Memory w) (r:Word w) (ok:∀i,(e i).eval m r=(v i:Word w)) (xs:List X) :
    (total e xs).eval m r=(((xs.map v).sum:ℕ):Word w) :=by induction xs with | nil=>rfl | cons x xs ih=>simp [total,Expr.eval,RowOp.opcode,BinaryOp.eval,ok,ih]

theorem source (T : Headers P) (out : ℕ) (room : Fits T H G M w out) (value : Fin H→Fin P→Fin (P+1)) (m : Memory w) (mount : Reads T value M G m) :
    DescentPackedZip.Source (context T) (fun h (_:Fin G)=>digest (value h)) M m :=by
  intro p;let r:=row H G M p
  let K:=used G M p.2.val
  have bound : K≤M:=min_le_left ..
  have root:=(DescentPackedZip.bank_read T.block m (r.isLt.trans_le room.blockSize) room.block).trans (mount.block p)
  have zero:=(DescentPackedZip.bank_read T.live m (r.isLt.trans_le room.liveSize) room.live).trans (mount.live p)
  have entry (i:Fin P) : (term T i).eval m (r.val:Word w)=(shift P M i.val K (value p.1 i).val:Word w):=by
    have idx : p.1.val*P+i.val<T.chart.size:=by
      have upper:=Nat.mul_le_mul_right P (Nat.succ_le_of_lt p.1.isLt);rw [Nat.succ_mul] at upper;have:=i.isLt;exact lt_of_lt_of_le (by omega) room.chartSize
    have target : K*(P+1)+(value p.1 i).val<(T.spread i).size:=by
      calc
        K*(P+1)+(value p.1 i).val < K*(P+1)+(P+1) := Nat.add_lt_add_left (value p.1 i).isLt _
        _ = (K+1)*(P+1) := (Nat.succ_mul _ _).symm
        _ ≤ (M+1)*(P+1) := Nat.mul_le_mul_right _ (Nat.succ_le_succ bound)
        _ ≤ _ := room.spreadSize i
    change (T.spread i).read m (T.live.read m (r.val:Word w)+T.chart.read m (T.block.read m (r.val:Word w)+(i.val:Word w)))=_
    rw [zero,root,←Nat.cast_add,DescentPackedZip.bank_read _ _ idx room.chart,mount.chart,←Nat.cast_add,DescentPackedZip.bank_read _ _ target (room.spread i)]
    exact mount.spread i (value p.1 i) ⟨K,Nat.lt_succ_of_le bound⟩
  change (context T).eval m (r.val:Word w)=_
  rw [context,eval_total _ _ m _ entry,←List.ofFn_eq_map,List.sum_ofFn,pieces]

theorem context_fits (T : Headers P) (out : ℕ) (room : Fits T H G M w out) : (context T).Fits w out:=
  fits_total (term T) (fun i=>⟨room.spread i,⟨room.live,trivial⟩,room.chart,⟨room.block,trivial⟩,trivial⟩) _

theorem context_work (T : Headers P) : (context T).work≤1+40*P:=by
  have size:=work_total (term T) 39 (fun i=>by simp [term,Expr.work]) (List.finRange P);simpa [context,Nat.mul_comm] using size


end
end Hierarchy.DescentHaloPackedRebase

end OAI
