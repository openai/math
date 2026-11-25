import OAI.Hierarchy.DescentHaloRebaseRAM
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Deduplicated physical four-hop gather of the previous packed donor rows -/
namespace Hierarchy.DescentHaloWalkRAM.Gather
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentSIMDLookup DescentPackedColony
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H D P w : ℕ}

/-- Two walks to one donor yield exactly one resident entry. Missing walks
and later duplicate visits select the all-zero group word in `peerExpr`. -/
def select (reach : Fin H→Fin P→Option (Fin H)) (v : Fin H) (p : Fin P) :=
  if ∃q:Fin P,q<p ∧ reach v q=reach v p then none else reach v p

theorem once (reach : Fin H→Fin P→Option (Fin H)) (v u : Fin H) (hit : ∃p,reach v p=some u) :
    ∃!p,select reach v p=some u :=by
  let candidates:=Finset.univ.filter (fun j=>reach v j=some u)
  have alive:candidates.Nonempty:=by obtain ⟨j,hj⟩:=hit;exact ⟨j,by simp [candidates,hj]⟩
  let first:=candidates.min' alive
  have firstHit : reach v first=some u:=by
    have h : first ∈ candidates := Finset.min'_mem candidates alive
    exact (Finset.mem_filter.mp h).2
  have minimum {j : Fin P} (eqn : reach v j=some u) : first≤j :=
    Finset.min'_le candidates j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eqn⟩)
  have keep:¬∃j,j<first ∧ reach v j=reach v first:=by
    rintro ⟨j,earlier,same⟩;exact (not_lt.mpr (minimum (same.trans firstHit))) earlier
  have retained : select reach v first=some u := by
    unfold select
    exact (ite_eq_right keep).trans firstHit
  refine ⟨first,retained,?_⟩
  intro j selected
  change select reach v j=some u at selected
  unfold select at selected
  split at selected
  · contradiction
  · rename_i clear
    refine le_antisymm ?_ (minimum selected)
    by_contra! later
    exact clear ⟨first,later,firstHit.trans selected.symm⟩

structure Columns extends Ranks.Columns where
  ordinal : Bank

structure Room (C : Columns) (out H P w : ℕ) : Prop extends Ranks.Fits C.toColumns out H P w where
  ordinal : C.ordinal.Fits w out
  sizeOrdinal : H*P≤C.ordinal.size
  sentinel : H<2^w
  paths : P≤2^w

structure Reads (C : Columns) (reach : Fin H→Fin P→Option (Fin H)) (m : Memory w) : Prop where
  prior : Ranks.Reads C.toColumns (fun v p=>number (reach v p)) m
  ordinal : ∀(v:Fin H) (p:Fin P),m (C.ordinal.base+(Ranks.id v p).val)=(p.val:Word w)

private theorem bank_at (b : Bank) {out i : ℕ} (ok : b.Fits w out) (hi : i<b.size) (m : Memory w) :
    b.read m (i:Word w)=m (b.base+i) :=by simp [Bank.read,Fin.val_cast_of_lt (hi.trans ok.2.1),Nat.mod_eq_of_lt hi]

private theorem code_inj {a b : Option (Fin H)} : number a=number b ↔ a=b:=by
  constructor
  · intro eqn;cases a with
    | none=>cases b with | none=>rfl | some b=>change H=b.val at eqn;exact False.elim (b.isLt.ne eqn.symm)
    | some a=>cases b with | none=>change a.val=H at eqn;exact False.elim (a.isLt.ne eqn) | some b=>exact congrArg some (Fin.ext eqn)
  · exact congrArg number

def duplicate (C : Columns) (i : Fin P) : Expr :=
  .branch .eq (.lookup C.endpoints (.op .add (.lookup C.start .row) (.lit i.val))) (.lookup C.endpoints .row)
    (.branch .lt (.lit i.val) (.lookup C.ordinal .row) (.lit 1) (.lit 0)) (.lit 0)

theorem duplicate_at (C : Columns) {out} (ok : Room C out H P w) (R : Fin H→Fin P→Option (Fin H))
    (m : Memory w) (pins : Reads C R m) (v : Fin H) (p i : Fin P) :
    (duplicate C i).eval m ((Ranks.id v p).val:Word w)=((if i<p ∧ R v i=R v p then 1 else 0 : ℕ):Word w) :=by
  let r:=Ranks.id v p
  have addr (i : Fin P) : (Ranks.id v i).val=v.val*P+i.val:=by simp [Ranks.id,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]
  have here : C.endpoints.read m (r.val:Word w)=(number (R v p):Word w):=by
    rw [bank_at C.endpoints ok.endpoints (r.isLt.trans_le ok.sizeEnd) m,addr];exact pins.prior.endpoints v p
  have now : C.ordinal.read m (r.val:Word w)=(p.val:Word w):=(bank_at C.ordinal ok.ordinal (r.isLt.trans_le ok.sizeOrdinal) m).trans (pins.ordinal v p)
  have start : C.start.read m (r.val:Word w)=((v.val*P:ℕ):Word w):=(bank_at C.start ok.start (r.isLt.trans_le ok.sizeStart) m).trans (pins.prior.start v p)
  have other (i : Fin P) : C.endpoints.read m (((v.val*P:ℕ):Word w)+(i.val:Word w))=(number (R v i):Word w):=by
    rw [←Nat.cast_add,bank_at C.endpoints ok.endpoints (show v.val*P+i.val<C.endpoints.size by rw [←addr];exact (Ranks.id v i).isLt.trans_le ok.sizeEnd) m];exact pins.prior.endpoints v i
  have otherWord : C.endpoints.read m ((v.val:Word w)*(P:Word w)+(i.val:Word w))=(number (R v i):Word w) := by
    simpa only [Nat.cast_mul] using other i
  have same : ((number (R v i):Word w)=(number (R v p):Word w)) ↔ R v i=R v p:=by
    rw [←Fin.val_inj,Fin.val_cast_of_lt (pins.prior.addressBound v i),Fin.val_cast_of_lt (pins.prior.addressBound v p),code_inj]
  change (duplicate C i).eval m (r.val:Word w)=_
  by_cases eqn : R v i=R v p <;> by_cases small : i.val<p.val <;>
    simp [duplicate,Expr.eval,RowOp.opcode,BinaryOp.eval,DescriptorExpr.Comparison.test,now,start,Nat.cast_mul,otherWord,here,same,Fin.val_cast_of_lt (i.isLt.trans_le ok.paths),Fin.val_cast_of_lt (p.isLt.trans_le ok.paths),Fin.lt_def,eqn,small]

def onceRow (C : Columns) (H P : ℕ) := Expr.branch .eq (DescentColonies.SplitRAM.total (duplicate C) (List.finRange P)) (.lit 0) (.lookup C.endpoints .row) (.lit H)

private theorem sum_rows {α : Type} (f : α→Expr) (a : α→ℕ) (m : Memory w) (r : Word w)
    (ok : ∀i,(f i).eval m r=(a i:Word w)) (xs : List α) :
    (DescentColonies.SplitRAM.total f xs).eval m r=((xs.map a).sum:Word w) :=by
  induction xs with
  | nil=>rfl
  | cons i is ih=>simp [DescentColonies.SplitRAM.total,Expr.eval,RowOp.opcode,BinaryOp.eval,ok,ih]

theorem row_at (C : Columns) {out} (ok : Room C out H P w) (R : Fin H→Fin P→Option (Fin H)) (m : Memory w)
    (pins : Reads C R m) (v : Fin H) (p : Fin P) :
    (onceRow C H P).eval m ((Ranks.id v p).val:Word w)=(number (select R v p):Word w) :=by
  let S:=(Finset.univ.filter (fun i:Fin P=>i<p ∧ R v i=R v p))
  let a (i:Fin P):=if i<p ∧ R v i=R v p then 1 else 0
  have total:=sum_rows (duplicate C) a m ((Ranks.id v p).val:Word w) (duplicate_at C ok R m pins v p) (List.finRange P)
  rw [←List.ofFn_eq_map,List.sum_ofFn] at total
  have size : ∑i,a i=S.card:=by simp [a,S]
  rw [size] at total
  have inside:S⊂Finset.univ:=(Finset.ssubset_iff_of_subset (Finset.subset_univ _)).2 ⟨p,Finset.mem_univ _,by simp [S]⟩
  have limit:S.card<2^w:=lt_of_lt_of_le (by simpa using Finset.card_lt_card inside) ok.paths
  have here : C.endpoints.read m ((Ranks.id v p).val:Word w)=(number (R v p):Word w):=by
    rw [bank_at C.endpoints ok.endpoints ((Ranks.id v p).isLt.trans_le ok.sizeEnd) m];simpa [Ranks.id,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm] using pins.prior.endpoints v p
  by_cases earlier:∃i:Fin P,i<p ∧ R v i=R v p
  · obtain ⟨i,low,same⟩:=earlier
    have nz:S.card≠0:=Finset.card_ne_zero.mpr ⟨i,by simp [S,low,same]⟩
    have diff : (S.card:Word w)≠0:=by intro eqn;apply nz;simpa [Fin.val_cast_of_lt limit] using congrArg Fin.val eqn
    simp [onceRow,Expr.eval,DescriptorExpr.Comparison.test,total,diff,select,show ∃i:Fin P,i<p ∧ R v i=R v p from ⟨i,low,same⟩,number]
  · have empty:S=∅:=by ext i;simp [S];exact fun b c=>earlier ⟨i,b,c⟩
    simp [onceRow,Expr.eval,DescriptorExpr.Comparison.test,total,empty,select,earlier,here]

theorem fits (C : Columns) {out} (ok : Room C out H P w) : (onceRow C H P).Fits w out :=
  ⟨DescentColonies.SplitRAM.fits_total (duplicate C) (fun _=>⟨⟨ok.endpoints,⟨⟨ok.start,trivial⟩,trivial⟩⟩,⟨ok.endpoints,trivial⟩,
    ⟨trivial,⟨ok.ordinal,trivial⟩,trivial,trivial⟩,trivial⟩) _,trivial,⟨ok.endpoints,trivial⟩,trivial⟩

theorem work (C : Columns) (H P : ℕ) : (onceRow C H P).work≤16+64*P:=by
  have bound:=DescentColonies.SplitRAM.work_total (duplicate C) 48 (fun _=>by simp [duplicate,Expr.work]) (List.finRange P)
  simp only [List.length_finRange] at bound;simp [onceRow,Expr.work];omega

theorem header_run (C : Columns) {out} (ok : Room C out H P w) (R : Fin H→Fin P→Option (Fin H)) (m : Memory w) (pins : Reads C R m) :
    let result:=image out (H*P) (onceRow C H P) m
    (scan w out (H*P) (onceRow C H P)).Exec m result (4+H*P*(2*(onceRow C H P).work+4)) ∧
    (∀v p,result (out+(Ranks.id v p).val)=(number (select R v p):Word w)) ∧ CheapCode (scan w out (H*P) (onceRow C H P)) :=by
  intro result;exact ⟨scan_exec _ _ _ _ (fits C ok) ok.output,
    fun v p=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ (Ranks.id v p)).trans (row_at C ok R m pins v p),by apply scan_cheap⟩

/-- Fetch one whole packed donor column across the unique path. The caller
can iterate the same cheap row kernel over `(oldBlock, oldOutgoing, role)`;
last partial group words are included in `Reads`. -/
theorem gather {a G M : ℕ} (ports : Ports P) (old : Bank) (out : ℕ) (p : Fin P)
    (R : Fin H→Fin P→Option (Fin H)) (x : Fin H→Fin G→Cell a) (m : Memory w)
    (ok : Accessible ports old H G M w out) (mount : Mounted ports (select R) m G M)
    (inData : DescentPackedColony.Reads old x M m) (space : out+H*chunks G M<2^w) :
    let f:=peerExpr ports old H p
    let result:=image out (H*chunks G M) f m
    (scan w out (H*chunks G M) f).Exec m result (4+H*chunks G M*(2*f.work+4)) ∧
    (∀r : Row H G M,result (out+(DescentSIMDLookup.row H G M r).val)=((data (fun v g=>(select R v p).elim 0 (fun u=>x u g)) r).val:Word w)) ∧
    CheapCode (scan w out (H*chunks G M) f) :=by
  intro f result;exact ⟨scan_exec _ _ _ _ (peer_fits ports old out ok p) space,
    fun r=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ (DescentSIMDLookup.row H G M r)).trans (peerSource ports old out ok (select R) m mount x inData p r),by apply scan_cheap⟩

def reaching (R : Fin H→Fin D→Option (Fin H)) (v : Fin H) (p : Fin (breadth D)):=walk R v (path p) 4

end
end Hierarchy.DescentHaloWalkRAM.Gather

end OAI
