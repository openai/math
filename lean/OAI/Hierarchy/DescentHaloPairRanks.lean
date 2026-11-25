import OAI.Hierarchy.DescentHaloPackedGather
import OAI.Hierarchy.DescentHaloRebaseRAM

namespace OAI
/-! # Cross-donor peer comparison in the receiver’s common eight-hop rack table -/
namespace Hierarchy.DescentHaloWalkRAM.PairRanks
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H P w : ℕ}

def pair (p q : Fin P) : Fin (P*P):=finProdFinEquiv (p,q)

def combined (reach : Fin H→Fin P→Option (Fin H)) (v : Fin H) (s : Fin (P*P)) :=
  let j:Fin P×Fin P:=finProdFinEquiv.symm s
  (reach v j.1).bind (fun old=>reach old j.2)

@[simp] theorem joined (reach : Fin H→Fin P→Option (Fin H)) (v : Fin H) (p q : Fin P) :
    combined reach v (pair p q)=(reach v p).bind (fun old=>reach old q) :=by simp [combined,pair]

def ticket (reach : Fin H→Fin P→Option (Fin H)) (v : Fin H) (p q : Fin P) : Fin (P*P) :=
  let endpoint:=fun t s=>number (combined reach t s)
  ⟨Ranks.earlier endpoint v (endpoint v (pair p q)),Ranks.bound endpoint v (pair p q)⟩

/-- Relative paths from two unrelated issuing donors compare the *same*
other rack iff their new receiver-local header digits agree. -/
theorem same (reach : Fin H→Fin P→Option (Fin H)) (v a b l r : Fin H) (p q s t : Fin P)
    (old1 : reach v p=some a) (peer1 : reach a q=some l) (old2 : reach v s=some b) (peer2 : reach b t=some r) :
    ticket reach v p q=ticket reach v s t ↔ l=r :=by
  let addr:=fun v s=>number (combined reach v s)
  have lr:=Ranks.compare addr v (pair p q) (pair s t)
  have rl:=Ranks.compare addr v (pair s t) (pair p q)
  have left:addr v (pair p q)=l.val:=by simp [addr,old1,peer1,number]
  have right:addr v (pair s t)=r.val:=by simp [addr,old2,peer2,number]
  change (⟨Ranks.earlier addr v (addr v (pair p q)),_⟩:Fin (P*P))=⟨Ranks.earlier addr v (addr v (pair s t)),_⟩ ↔ l=r
  rw [Fin.ext_iff]
  change Ranks.earlier addr v (addr v (pair p q))=Ranks.earlier addr v (addr v (pair s t)) ↔ l=r
  rw [left,right] at lr rl ⊢
  constructor
  · intro ranks
    apply Fin.ext
    exact le_antisymm (le_of_not_gt fun h=>(rl.2 h).ne ranks.symm)
      (le_of_not_gt fun h=>(lr.2 h).ne ranks)
  · rintro rfl
    rfl

structure Banks where
  endpoints : Bank
  previous : Bank
  suffix : Bank
  offset : Bank

structure Fits (B : Banks) (out H P w : ℕ) : Prop where
  endpoints : B.endpoints.Fits w out
  previous : B.previous.Fits w out
  suffix : B.suffix.Fits w out
  offset : B.offset.Fits w out
  endpointsSize : H*P≤B.endpoints.size
  previousSize : H*(P*P)≤B.previous.size
  suffixSize : H*(P*P)≤B.suffix.size
  offsetSize : H≤B.offset.size
  sentinel : H<2^w
  room : out+H*(P*P)<2^w

structure Reads (B : Banks) (reach : Fin H→Fin P→Option (Fin H)) (m : Memory w) : Prop where
  endpoints : ∀v j,m (B.endpoints.base+(Ranks.id v j).val)=(number (reach v j):Word w)
  previous : ∀(v:Fin H)(p q:Fin P),m (B.previous.base+(Ranks.id v (pair p q)).val)=((Ranks.id v p).val:Word w)
  suffix : ∀(v:Fin H)(p q:Fin P),m (B.suffix.base+(Ranks.id v (pair p q)).val)=(q.val:Word w)
  offset : ∀v:Fin H,m (B.offset.base+v.val)=((v.val*P:ℕ):Word w)

def op (B : Banks) (H : ℕ) :=let prev:=Expr.lookup B.endpoints (.lookup B.previous .row)
  Expr.branch .eq prev (.lit H) (.lit H) (.lookup B.endpoints (.op .add (.lookup B.offset prev) (.lookup B.suffix .row)))

private theorem get (B : Bank) {a out} (ok:B.Fits w out) (m:Memory w) (small:a<B.size) : B.read m (a:Word w)=m (B.base+a):=by
  simp [Bank.read,Fin.val_cast_of_lt (small.trans ok.2.1),Nat.mod_eq_of_lt small]

private theorem row_val (v:Fin H) (j:Fin P) : (Ranks.id v j).val=v.val*P+j.val:=by simp [Ranks.id,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]

theorem eval (B : Banks) (out : ℕ) (fit : Fits B out H P w) (reach : Fin H→Fin P→Option (Fin H)) (m : Memory w) (data : Reads B reach m)
    (v : Fin H) (p q : Fin P) : (op B H).eval m ((Ranks.id v (pair p q)).val:Word w)=(number (combined reach v (pair p q)):Word w) :=by
  let j:=Ranks.id v (pair p q)
  have atPrev : B.previous.read m (j.val:Word w)=((Ranks.id v p).val:Word w):=(get B.previous fit.previous m (j.isLt.trans_le fit.previousSize)).trans (data.previous v p q)
  have atSuffix : B.suffix.read m (j.val:Word w)=(q.val:Word w):=(get B.suffix fit.suffix m (j.isLt.trans_le fit.suffixSize)).trans (data.suffix v p q)
  have prev : B.endpoints.read m ((Ranks.id v p).val:Word w)=(number (reach v p):Word w):=(get B.endpoints fit.endpoints m ((Ranks.id v p).isLt.trans_le fit.endpointsSize)).trans (data.endpoints v p)
  change (op B H).eval m (j.val:Word w)=_
  cases hit:reach v p with
  | none=>simp [op,Expr.eval,DescriptorExpr.Comparison.test,atPrev,prev,hit,number,joined]
  | some u=>
    have active : (u.val:Word w)≠(H:Word w):=by intro h;apply u.isLt.ne;simpa [Fin.val_cast_of_lt (u.isLt.trans fit.sentinel),Fin.val_cast_of_lt fit.sentinel] using congrArg Fin.val h
    have offset:= (get B.offset fit.offset m (u.isLt.trans_le fit.offsetSize)).trans (data.offset u)
    have fetched : B.endpoints.read m (((u.val*P:ℕ):Word w)+(q.val:Word w))=(number (reach u q):Word w):=by
      rw [←Nat.cast_add,←row_val u q,get B.endpoints fit.endpoints m ((Ranks.id u q).isLt.trans_le fit.endpointsSize)];exact data.endpoints u q
    simp [op,Expr.eval,DescriptorExpr.Comparison.test,RowOp.opcode,BinaryOp.eval,atPrev,atSuffix,prev,hit,number,offset,active,joined]
    simpa only [Nat.cast_mul,number] using fetched

theorem run (B : Banks) (out : ℕ) (fit : Fits B out H P w) (reach : Fin H→Fin P→Option (Fin H)) (m : Memory w) (data : Reads B reach m) :
    let after:=image out (H*(P*P)) (op B H) m
    (scan w out (H*(P*P)) (op B H)).Exec m after (4+H*(P*P)*(2*(op B H).work+4)) ∧
    (∀v s,after (out+(Ranks.id v s).val)=(number (combined reach v s):Word w)) ∧ CheapCode (scan w out (H*(P*P)) (op B H)) :=by
  intro after
  have bounded:(op B H).Fits w out:=by simp [op,Expr.Fits,fit.endpoints,fit.previous,fit.offset,fit.suffix]
  refine ⟨scan_exec _ _ _ _ bounded fit.room,?_,by apply scan_cheap⟩
  intro v s;obtain ⟨⟨p,q⟩,rfl⟩:=finProdFinEquiv.surjective s
  exact (ProtocolRAMGeneratedWrite.read_image _ _ _ _ (Ranks.id v (pair p q))).trans (eval B out fit reach m data v p q)

/-- Direct mount of the native second-endpoint column for `Ranks.run`. -/
theorem mounted (B : Banks) (C : Ranks.Columns) (fit : Fits B C.endpoints.base H P w) (reach : Fin H→Fin P→Option (Fin H)) (m : Memory w) (data : Reads B reach m)
    (prior : C.start.base+C.start.size≤C.endpoints.base) (size : H*(P*P)≤C.start.size)
    (arithmetic : ∀(v:Fin H)(j:Fin (P*P)),m (C.start.base+(Ranks.id v j).val)=((v.val*(P*P):ℕ):Word w)) :
    Ranks.Reads C (fun v j=>number (combined reach v j)) (image C.endpoints.base (H*(P*P)) (op B H) m) :=by
  let published:=(run B C.endpoints.base fit reach m data).2.1
  refine ⟨fun v j=>?_,fun v j=>?_,fun v j=>?_⟩
  · simpa only [row_val] using published v j
  · have lo:C.start.base+(Ranks.id v j).val<C.endpoints.base:=by have:=(Ranks.id v j).isLt;omega
    rw [show image C.endpoints.base (H*(P*P)) (op B H) m (C.start.base+(Ranks.id v j).val)=m (C.start.base+(Ranks.id v j).val) by simp [image,fillSegment,lo.not_ge]];exact arithmetic v j
  · cases u:combined reach v j with | none=>exact fit.sentinel | some t=>exact t.isLt.trans fit.sentinel

end
end Hierarchy.DescentHaloWalkRAM.PairRanks

end OAI
