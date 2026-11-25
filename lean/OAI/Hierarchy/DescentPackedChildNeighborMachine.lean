import OAI.Hierarchy.DescentHaloRankRAM
import OAI.Hierarchy.DescentStaticWordColumn
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Convert an actual eight-hop local ticket to the sorted next cable neighbor -/
namespace Hierarchy.DescentPackedChildNeighbor
open DescentHaloWalkRAM DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H L Q D w : ℕ}

/-- The successor name has its exact dense host pitch. The local slot and
heap ordinal are already combined in `low`. -/
def host (v : Fin H) (low : Fin Q) : Fin (H*Q) :=finProdFinEquiv (v,low)

theorem host_val (v : Fin H) (low : Fin Q) : (host v low).val=v.val*Q+low.val :=by simp [host,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]

abbrev Key (H L Q : ℕ) := (Fin H×Fin Q)×(Fin L×Fin Q)
def rowId (H L Q : ℕ) : Key H L Q ≃ Fin ((H*Q)*(L*Q)) :=(finProdFinEquiv.prodCongr finProdFinEquiv).trans finProdFinEquiv

def rank (endAt : Fin H→Fin L→Option (Fin H)) (v : Fin H) (p : Fin L) :=
  Ranks.earlier (fun u j=>number (endAt u j)) v (number (endAt v p))

def search {α : Type} (get result : α→ℕ) (wanted absent : ℕ) : List α→ℕ
  | []=>absent
  | i::is=>if get i=wanted then result i else search get result wanted absent is

theorem search_live {α : Type} (get result : α→ℕ) (wanted absent answer : ℕ) (l : List α)
    (live : ∃i∈l,get i=wanted) (consistent : ∀i∈l,get i=wanted→ result i=answer) : search get result wanted absent l=answer :=by
  induction l with
  | nil=>simp at live
  | cons e es ih=>
    by_cases h:get e=wanted
    · rw [search,ite_eq_left h];exact consistent e (.head _) h
    · rw [search,ite_eq_right h];apply ih _ (fun i hi=>consistent i (.tail _ hi))
      obtain ⟨i,hit,read⟩:=live;rcases List.mem_cons.mp hit with rfl|member
      · contradiction
      · exact ⟨i,member,read⟩

def previous (endAt : Fin H→Fin L→Option (Fin H)) (v : Fin H) (t : Fin L) :=
  search (rank endAt v) (fun i=>number (endAt v i)) t.val H (List.finRange L)

theorem previous_at (endAt : Fin H→Fin L→Option (Fin H)) (v : Fin H) (q : Fin L) :
    previous endAt v ⟨rank endAt v q,Ranks.bound ..⟩=number (endAt v q) := by
  apply search_live _ _ _ _ _ _ ⟨q,List.mem_finRange _,rfl⟩
  intro i _ hit
  let value:=fun u j=>number (endAt u j)
  have ab:=Ranks.compare value v i q;have ba:=Ranks.compare value v q i
  change Ranks.earlier value v (value v i)=Ranks.earlier value v (value v q) at hit
  change value v i=value v q
  omega

def value (endAt : Fin H→Fin L→Option (Fin H)) (roster : Fin (H*Q)→Fin D→Option (Fin (H*Q))) (z : Key H L Q) :=
  let other:=previous endAt z.1.1 z.2.1
  if other=H then D else search (fun j=>number (roster (host z.1.1 z.1.2) j)) Fin.val (other*Q+z.2.2.val) D (List.finRange D)

theorem value_at (endAt : Fin H→Fin L→Option (Fin H)) (roster : Fin (H*Q)→Fin D→Option (Fin (H*Q)))
    (v other : Fin H) (mine his : Fin Q) (q : Fin L) (j : Fin D) (reached : endAt v q=some other)
    (neighbor : roster (host v mine) j=some (host other his))
    (unique : ∀l,roster (host v mine) l=some (host other his)→l=j) :
    value endAt roster ((v,mine),(⟨rank endAt v q,Ranks.bound ..⟩,his))=j.val := by
  simp only [value,previous_at,reached,number,Option.elim_some,ite_eq_right other.isLt.ne]
  apply search_live _ _ _ _ _ _ ⟨j,List.mem_finRange _,by rw [neighbor];exact host_val ..⟩
  intro t _ hit
  apply congrArg Fin.val (unique t ?_)
  cases h:roster (host v mine) t with
  | none=>rw [h] at hit;have room:=(host other his).isLt;rw [host_val] at room;change H*Q=_ at hit;omega
  | some x=>apply congrArg some;apply Fin.ext;simpa only [h,number,Option.elim_some,host_val] using hit

structure Banks where
  ranks : Bank
  endpoints : Bank
  roster : Bank
  timesPitch : Bank
  oldOffset : Bank
  ticket : Bank
  low : Bank
  newOffset : Bank

def atIndex (value start : Bank) (j : ℕ) : Expr:=.lookup value (.op .add (.lookup start .row) (.lit j))

def findWord {α : Type} (get pay : α→Expr) (want : Expr) (missing : ℕ) : List α→Expr
  | []=>.lit missing
  | j::js=>.branch .eq (get j) want (pay j) (findWord get pay want missing js)

def prev (B : Banks) (H L : ℕ) :=findWord (fun i : Fin L=>atIndex B.ranks B.oldOffset i.val) (fun i=>atIndex B.endpoints B.oldOffset i.val) (.lookup B.ticket .row) H (List.finRange L)

def body (B : Banks) (H L D : ℕ) : Expr:=
  let old:=prev B H L
  let target:=Expr.op .add (.lookup B.timesPitch old) (.lookup B.low .row)
  .branch .eq old (.lit H) (.lit D) (findWord (fun j : Fin D=>atIndex B.roster B.newOffset j.val) (fun j=>.lit j.val) target D (List.finRange D))

structure Room (B : Banks) (H L Q D w out : ℕ) : Prop where
  shapes : ∀b∈[B.oldOffset,B.ticket,B.low,B.newOffset],b.Fits w out ∧ (H*Q)*(L*Q)≤b.size
  ranks : B.ranks.Fits w out ∧ H*L≤B.ranks.size
  ends : B.endpoints.Fits w out ∧ H*L≤B.endpoints.size
  roster : B.roster.Fits w out ∧ (H*Q)*D≤B.roster.size
  scale : B.timesPitch.Fits w out ∧ H≤B.timesPitch.size
  limits : max (H*Q) (max H (max D L))<2^w
  last : out+(H*Q)*(L*Q)<2^w

structure Mounted (B : Banks) (endAt : Fin H→Fin L→Option (Fin H)) (roster : Fin (H*Q)→Fin D→Option (Fin (H*Q))) (m : Memory w) : Prop where
  old : ∀q : Key H L Q,m (B.oldOffset.base+(rowId H L Q q).val)=((q.1.1.val*L:ℕ):Word w)
  query : ∀q : Key H L Q,m (B.ticket.base+(rowId H L Q q).val)=(q.2.1.val:Word w)
  lower : ∀q : Key H L Q,m (B.low.base+(rowId H L Q q).val)=(q.2.2.val:Word w)
  current : ∀q : Key H L Q,m (B.newOffset.base+(rowId H L Q q).val)=(((host q.1.1 q.1.2).val*D:ℕ):Word w)
  cost : ∀v : Fin H,m (B.timesPitch.base+v.val)=((v.val*Q:ℕ):Word w)
  prior : ∀v j,m (B.ranks.base+(v.val*L+j.val))=(rank endAt v j:Word w)
  finish : ∀v j,m (B.endpoints.base+(v.val*L+j.val))=(number (endAt v j):Word w)
  neighbors : ∀v j,m (B.roster.base+(v.val*D+j.val))=(number (roster v j):Word w)

private theorem find_at {α : Type} (get pay : α→Expr) (want : Expr) (fallback x : ℕ) (f g : α→ℕ) (m : Memory w) (r : Word w)
    (ask : want.eval m r=(x:Word w)) (small : x<2^w) (read : ∀i,(get i).eval m r=(f i:Word w)) (fit : ∀i,f i<2^w)
    (give : ∀i,(pay i).eval m r=(g i:Word w)) (l : List α) :
    (findWord get pay want fallback l).eval m r=(search f g x fallback l:Word w) := by
  induction l with
  | nil=>rfl
  | cons j l ih=>
    have eqn : (f j : Word w)=(x:Word w) ↔ f j=x :=by rw [Fin.ext_iff,Fin.val_cast_of_lt (fit j),Fin.val_cast_of_lt small]
    by_cases yes:f j=x <;> simp [findWord,Expr.eval,read,ask,give,ih,DescriptorExpr.Comparison.test,search,eqn,yes]

private theorem find_fit {α : Type} (get pay : α→Expr) (want : Expr) (fallback out : ℕ) (a : ∀i,(get i).Fits w out)
    (b : ∀i,(pay i).Fits w out) (c : want.Fits w out) (l : List α) : (findWord get pay want fallback l).Fits w out :=by
  induction l with | nil=>trivial | cons j js ih=>exact ⟨a j,c,b j,ih⟩

private theorem index_fit (B t : Bank) (j out : ℕ) (h : B.Fits w out) (g : t.Fits w out) : (atIndex B t j).Fits w out :=⟨h,⟨g,trivial⟩,trivial⟩

private theorem at_index (B b : Bank) {out n k : ℕ} (h : B.Fits w out) (g : b.Fits w out) (p : Fin n) (j : Fin k) (index : ℕ)
    (room : index<b.size) (space : n*k≤B.size) (m : Memory w) (stored : m (b.base+index)=((p.val*k:ℕ):Word w)) :
    (atIndex B b j.val).eval m (index:Word w)=m (B.base+(p.val*k+j.val)) :=by
  have small : p.val*k+j.val<n*k:=(Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ p.isLt)
  change B.read m ((b.read m (index:Word w))+(j.val:Word w))=_
  rw [DescentPackedZip.bank_read _ _ room g,stored,←Nat.cast_add,DescentPackedZip.bank_read _ _ (small.trans_le space) h]

private theorem previous_le (endAt : Fin H→Fin L→Option (Fin H)) (v : Fin H) (t : Fin L) : previous endAt v t≤H :=by
  have bounded (is : List (Fin L)) : search (rank endAt v) (fun j=>number (endAt v j)) t.val H is≤H := by
    induction is with
    | nil=>exact le_rfl
    | cons j js ih =>
      rw [search]
      split
      · cases live : endAt v j with
        | none => exact le_rfl
        | some z => exact z.isLt.le
      · exact ih
  exact bounded _

theorem eval (B : Banks) (out : ℕ) (ok : Room B H L Q D w out) (ends : Fin H→Fin L→Option (Fin H)) (roster : Fin (H*Q)→Fin D→Option (Fin (H*Q)))
    (m : Memory w) (present : Mounted B ends roster m) (z : Key H L Q) :
    (body B H L D).eval m ((rowId H L Q z).val:Word w)=(value ends roster z:Word w) :=by
  let i:=rowId H L Q z;let v:=z.1.1;let here:=host v z.1.2;let t:=z.2.1;let low:=z.2.2
  have numH : H<2^w := (Nat.le_max_left H _).trans_lt ((Nat.le_max_right _ _).trans_lt ok.limits)
  have numL : L<2^w := (Nat.le_max_right _ _).trans_lt ((Nat.le_max_right _ _).trans_lt ((Nat.le_max_right _ _).trans_lt ok.limits))
  have numQ : H*Q<2^w := (Nat.le_max_left _ _).trans_lt ok.limits
  have cold:=ok.shapes B.oldOffset (by simp);have cur:=ok.shapes B.newOffset (by simp)
  have query:=ok.shapes B.ticket (by simp);have lo:=ok.shapes B.low (by simp)
  have readRank (j : Fin L) :=(at_index B.ranks B.oldOffset ok.ranks.1 cold.1 v j i.val (i.isLt.trans_le cold.2) ok.ranks.2 m (present.old z)).trans (present.prior v j)
  have readEnd (j : Fin L) :=(at_index B.endpoints B.oldOffset ok.ends.1 cold.1 v j i.val (i.isLt.trans_le cold.2) ok.ends.2 m (present.old z)).trans (present.finish v j)
  have test : B.ticket.read m (i.val:Word w)=(t.val:Word w):=(DescentPackedZip.bank_read _ _ (i.isLt.trans_le query.2) query.1).trans (present.query z)
  have short (j : Fin L) : rank ends v j<2^w:=(Ranks.bound _ _ _).trans numL
  have lower := find_at (fun j : Fin L => atIndex B.ranks B.oldOffset j.val)
    (fun j : Fin L => atIndex B.endpoints B.oldOffset j.val)
    (.lookup B.ticket .row) H t.val (rank ends v) (fun j => number (ends v j)) m
    (i.val : Word w) test (t.isLt.trans numL) readRank short readEnd (List.finRange L)
  change (prev B H L).eval m (i.val : Word w)=(previous ends v t : Word w) at lower
  have le := previous_le ends v t
  have eqn : (previous ends v t : Word w)=(H : Word w) ↔ previous ends v t=H := by
    rw [Fin.ext_iff,Fin.val_cast_of_lt (le.trans_lt numH),Fin.val_cast_of_lt numH]
  have flag : DescriptorExpr.Comparison.eq.test ((prev B H L).eval m (i.val : Word w)) (H : Word w)=true ↔
      previous ends v t=H := by
    rw [lower]
    simpa only [DescriptorExpr.Comparison.test,beq_iff_eq] using eqn
  let item := Expr.op .add (.lookup B.timesPitch (prev B H L)) (.lookup B.low .row)
  let candidate := findWord (fun j : Fin D => atIndex B.roster B.newOffset j.val) (fun j => .lit j.val)
    item D (List.finRange D)
  change (if DescriptorExpr.Comparison.eq.test ((prev B H L).eval m (i.val : Word w)) (H : Word w)
      then (D : Word w) else candidate.eval m (i.val : Word w)) =
    (((if previous ends v t=H then D else search (fun j => number (roster here j)) Fin.val
      (previous ends v t*Q+low.val) D (List.finRange D)) : ℕ) : Word w)
  by_cases empty : previous ends v t=H
  · rw [ite_eq_left (flag.mpr empty),ite_eq_left empty]
  · rw [ite_eq_right (fun hit => empty (flag.mp hit)),ite_eq_right empty]
    let u : Fin H := ⟨previous ends v t,lt_of_le_of_ne le empty⟩
    have mul : B.timesPitch.read m (u.val:Word w)=((u.val*Q:ℕ):Word w):=(DescentPackedZip.bank_read _ _ (u.isLt.trans_le ok.scale.2) ok.scale.1).trans (present.cost u)
    have rest : B.low.read m (i.val:Word w)=(low.val:Word w):=(DescentPackedZip.bank_read _ _ (i.isLt.trans_le lo.2) lo.1).trans (present.lower z)
    have target : item.eval m (i.val:Word w)=((u.val*Q+low.val:ℕ):Word w):=by
      change (B.timesPitch.read m ((prev B H L).eval m (i.val:Word w)))+(B.low.read m (i.val:Word w))=_
      rw [lower,mul,rest,Nat.cast_add]
    have bound : u.val*Q+low.val<2^w:=by rw [←host_val u low];exact (host u low).isLt.trans numQ
    have rd (j : Fin D) := (at_index B.roster B.newOffset ok.roster.1 cur.1 here j i.val (i.isLt.trans_le cur.2) ok.roster.2 m (present.current z)).trans (present.neighbors here j)
    have noWrap (j : Fin D) : number (roster here j)<2^w:=by cases hj:roster here j with | none=>exact numQ | some a=>exact a.isLt.trans numQ
    exact find_at (fun j : Fin D => atIndex B.roster B.newOffset j.val) (fun j => .lit j.val)
      item D (u.val*Q+low.val) (fun j => number (roster here j)) Fin.val m (i.val : Word w)
      target bound rd noWrap (fun _ => rfl) (List.finRange D)

private theorem body_fit (B : Banks) (out : ℕ) (ok : Room B H L Q D w out) : (body B H L D).Fits w out :=by
  have b:=ok.shapes B.oldOffset (by simp);have query:=ok.shapes B.ticket (by simp);have l:=ok.shapes B.low (by simp);have curr:=ok.shapes B.newOffset (by simp)
  have old : (prev B H L).Fits w out :=
    find_fit (fun i : Fin L => atIndex B.ranks B.oldOffset i.val)
      (fun i : Fin L => atIndex B.endpoints B.oldOffset i.val) (.lookup B.ticket .row) H out
      (fun i => index_fit _ _ i.val out ok.ranks.1 b.1) (fun i => index_fit _ _ i.val out ok.ends.1 b.1)
      ⟨query.1,trivial⟩ (List.finRange L)
  let target := Expr.op .add (.lookup B.timesPitch (prev B H L)) (.lookup B.low .row)
  have targetFits : target.Fits w out := ⟨⟨ok.scale.1,old⟩,l.1,trivial⟩
  exact ⟨old,trivial,trivial,find_fit (fun j : Fin D => atIndex B.roster B.newOffset j.val)
    (fun j : Fin D => .lit j.val) target D out
    (fun j => index_fit _ _ j.val out ok.roster.1 curr.1) (fun _ => trivial) targetFits (List.finRange D)⟩

/-- Common receiver-local directory, built once over compact host coordinates.
The scanner has no per-cable or per-group instruction. -/
theorem run (B : Banks) (out : ℕ) (ok : Room B H L Q D w out) (ends : Fin H→Fin L→Option (Fin H)) (roster : Fin (H*Q)→Fin D→Option (Fin (H*Q)))
    (m : Memory w) (stored : Mounted B ends roster m) :
    let n:=(H*Q)*(L*Q);let op:=body B H L D;let done:=image out n op m
    (scan w out n op).Exec m done (4+n*(2*op.work+4)) ∧
      (∀z,done (out+(rowId H L Q z).val)=(value ends roster z:Word w)) ∧
      (∀j,j<out ∨ out+n≤j→done j=m j) ∧ CheapCode (scan w out n op) :=by
  exact ⟨scan_exec _ _ _ _ (body_fit B out ok) ok.last,
    fun z=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ (rowId H L Q z)).trans (eval B out ok ends roster m stored z),
    fun j h=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ j h,@scan_cheap _ _ _ _⟩

private theorem find_work {α : Type} (get pay : α→Expr) (want : Expr) (none a b : ℕ) (l : List α) (x : ∀i,(get i).work=a) (y : ∀i,(pay i).work=b) :
    (findWord get pay want none l).work=1+l.length*(a+want.work+b+1) := by
  induction l with
  | nil=>simp [findWord,Expr.work]
  | cons j l ih=>simp only [findWord,Expr.work,x,y,ih,List.length_cons,Nat.succ_mul];omega

theorem work (B : Banks) (H L D : ℕ) : (body B H L D).work=5+36*L+D*(30+36*L) := by
  have old : (prev B H L).work=1+36*L:=by
    unfold prev;rw [find_work _ _ _ H 14 14 _ (fun _=>rfl) (fun _=>rfl),List.length_finRange];change 1+L*36=1+36*L;omega
  simp only [body,Expr.work,find_work (fun j : Fin D=>atIndex B.roster B.newOffset j.val) (fun j=>.lit j.val) _ D 14 1 _ (fun _=>rfl) (fun _=>rfl),List.length_finRange,old]
  ring

end
end Hierarchy.DescentPackedChildNeighbor

end OAI
