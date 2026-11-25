import OAI.Hierarchy.DescentOrdinaryRankBanks
import OAI.Hierarchy.DescentPackedParentFilterRAM
import OAI.Hierarchy.DescentPackedHostLookupROM

namespace OAI
/-! The dynamic header for the ordinary receiver has three scalar directories.
For each distinct prior donor and endpoint path it physically supplies the
reverse receiver rank, the donor's local endpoint rank, and the shared
two-walk endpoint rank. All groups use the same header. -/
namespace Hierarchy.DescentOrdinaryDonorRankDirectory
open DescentHaloWalkRAM DescentParallelBase DescentParallelBase.ParentFilter DescentPackedZip DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H D w:ℕ} (R:Fin H→Fin D→Option (Fin H))
local notation "P" => breadth D
def numberAt (f:Field) (v:Fin H) (p q:Fin P):ℕ:=
  (Gather.select (Gather.reaching R) v p).elim 0 (fun h=>match f with
    | .reverse=>Rebase.value R .rank v p
    | .localEndpoint=>(ParentFilter.localRank R h q).val
    | .sharedEndpoint=>(PairRanks.ticket (Gather.reaching R) v p q).val)

def expression (B:Banks) (H:ℕ) (f:Field):Expr:=
  let prev:=Expr.lookup B.previous .row
  let old:=Expr.lookup B.endpoints prev
  .branch .eq old (.lit H) (.lit 0) (match f with
    | .reverse=>.lookup B.reverseRank prev
    | .localEndpoint=>.lookup B.localRank (.op .add (.lookup B.offset old) (.lookup B.suffix .row))
    | .sharedEndpoint=>.lookup B.sharedRank .row)

theorem observed (B:Banks) (out:ℕ) (ok:Fits B out H P w) (m:Memory w) (r:Reads R B m)
    (f:Field) (v:Fin H) (p q:Fin P):
    (expression B H f).eval m ((Ranks.id v (PairRanks.pair p q)).val:Word w)=(numberAt R f v p q:Word w):=by
  let j:=Ranks.id v (PairRanks.pair p q)
  have pre:B.previous.read m (j.val:Word w)=((Ranks.id v p).val:Word w):=(bank_read _ m (j.isLt.trans_le ok.previousSize) ok.previous).trans (r.prev v p q)
  have here:B.endpoints.read m ((Ranks.id v p).val:Word w)=(number (Gather.select (Gather.reaching R) v p):Word w):=
    (bank_read _ m ((Ranks.id v p).isLt.trans_le ok.endpointsSize) ok.endpoints).trans (r.visit v p)
  have suffix:B.suffix.read m (j.val:Word w)=(q.val:Word w):=(bank_read _ m (j.isLt.trans_le ok.suffixSize) ok.suffix).trans (r.suffix v p q)
  have back:B.reverseRank.read m ((Ranks.id v p).val:Word w)=(Rebase.value R .rank v p:Word w):=
    (bank_read _ m ((Ranks.id v p).isLt.trans_le ok.reverseSize) ok.reverse).trans (r.reverse v p)
  have joint:B.sharedRank.read m (j.val:Word w)=((PairRanks.ticket (Gather.reaching R) v p q).val:Word w):=
    (bank_read _ m (j.isLt.trans_le ok.sharedSize) ok.shared).trans (r.shared v p q)
  cases gate:Gather.select (Gather.reaching R) v p with
  | none=>
    simp only [gate,number,Option.elim_none] at here
    cases f <;> simp [expression,Expr.eval,pre,here,DescriptorExpr.Comparison.test,numberAt,gate,j]
  | some donor=>
    simp only [gate,number,Option.elim_some] at here
    have different:(donor.val:Word w)≠(H:Word w):=by
      intro eqn;have val:=congrArg Fin.val eqn
      simp only [Fin.val_cast_of_lt (donor.isLt.trans ok.sentinel),Fin.val_cast_of_lt ok.sentinel] at val
      exact donor.isLt.ne val
    have base:B.offset.read m (donor.val:Word w)=((donor.val*P:ℕ):Word w):=
      (bank_read _ m (donor.isLt.trans_le ok.offsetSize) ok.offset).trans (r.offset donor)
    have num:(Ranks.id donor q).val=donor.val*P+q.val:=by simp [Ranks.id,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]
    have localRead:B.localRank.read m (((donor.val*P:ℕ):Word w)+(q.val:Word w))=((ParentFilter.localRank R donor q).val:Word w):=by
      rw [←Nat.cast_add,←num]
      exact (bank_read _ m ((Ranks.id donor q).isLt.trans_le ok.localSize) ok.localFit).trans (r.localValue donor q)
    simp only [Nat.cast_mul] at localRead
    cases f <;> simp [expression,Expr.eval,pre,here,suffix,back,joint,base,localRead,DescriptorExpr.Comparison.test,RowOp.opcode,BinaryOp.eval,different,numberAt,gate,j]

theorem execute (B:Banks) (out:ℕ) (ok:Fits B out H P w) (m:Memory w) (r:Reads R B m) (f:Field):
    let e:=expression B H f
    let done:=image out (H*(P*P)) e m
    (scan w out (H*(P*P)) e).Exec m done (4+H*(P*P)*(2*e.work+4)) ∧
    (∀v p q,done (out+(Ranks.id v (PairRanks.pair p q)).val)=(numberAt R f v p q:Word w)) ∧
    (∀a,a<out ∨ out+H*(P*P)≤a→done a=m a) ∧ CheapCode (scan w out (H*(P*P)) e):=by
  intro e done
  have fits:e.Fits w out:=by cases f <;> simp [e,expression,Expr.Fits,ok.endpoints,ok.previous,ok.offset,ok.localFit,ok.suffix,ok.reverse,ok.shared]
  exact ⟨scan_exec _ _ e m fits ok.room,fun v p q=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ _).trans (observed R B out ok m r f v p q),
    ProtocolRAMGeneratedWrite.frame_image out _ e m,@scan_cheap _ _ _ _⟩

theorem expression_work (B : Banks) (H : ℕ) (f : Field) :
    (expression B H f).work =
      match f with
      | .reverse => 27
      | .localEndpoint => 45
      | .sharedEndpoint => 22 := by
  cases f <;> rfl

/-- The three directory fields fit the bound used by the signed prefix invoice. -/
theorem expression_work_le_120 (B : Banks) (H : ℕ) (f : Field) :
    (expression B H f).work ≤ 120 := by
  rw [expression_work]
  cases f <;> decide

/-- Before appending the low digit, the two issued scalar endpoint ranks are
the physical fields in the five-column ordinary projection. -/
theorem geometric {Q:ℕ} {v old:Fin H} {p:Fin P} (selected:Gather.select (Gather.reaching R) v p=some old) (q:Fin P) (low:Fin Q):
    numberAt R .reverse v p q=Rebase.value R .rank v p ∧
    numberAt R .localEndpoint v p q=(ParentFilter.localRank R old q).val ∧
    numberAt R .sharedEndpoint v p q*Q+low.val=(peer R v p ⟨q,low⟩).val:=by
  simp [numberAt,selected,peer,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]

open DescentPackedChildNeighbor.SIMD

theorem number_le (f:Field) (v:Fin H) (p q:Fin P):numberAt R f v p q≤P*P:=by
  have pos:0<P:=by simp [breadth]
  have bound:P≤P*P:=by simpa using Nat.mul_le_mul_left P (show 1≤P from pos)
  unfold numberAt
  cases h:Gather.select (Gather.reaching R) v p with
  | none=>simp
  | some old=>
    cases f with
    | reverse=>exact (Rebase.value_le R .rank v p).trans bound
    | localEndpoint=>exact (ParentFilter.localRank R old q).isLt.le.trans bound
    | sharedEndpoint=>exact (PairRanks.ticket (Gather.reaching R) v p q).isLt.le

def directory {b:ℕ} (fits:P*P<2^b) (f:Field) (v:Fin H) (j:Fin (P*P)):Cell b:=
  let steps:Fin P×Fin P:=finProdFinEquiv.symm j
  ⟨numberAt R f v steps.1 steps.2,(number_le R f v ..).trans_lt fits⟩

theorem header_words {b:ℕ} (f:Field) (fits:P*P<2^b) (m:Memory w) (base:ℕ)
    (read:∀v p q,m (base+(Ranks.id v (PairRanks.pair p q)).val)=(numberAt R f v p q:Word w))
    (v:Fin H) (j:Fin (P*P)):m (base+(v.val*(P*P)+j.val))=((directory R fits f v j).val:Word w):=by
  obtain ⟨⟨p,q⟩,rfl⟩:=finProdFinEquiv.surjective j
  simpa only [directory,Equiv.symm_apply_apply,Ranks.id,PairRanks.pair,finProdFinEquiv_apply_val,
    Nat.mul_comm,Nat.add_comm] using read v p q

/-- Every packed endpoint query now selects a value from the actual, dynamically
issued scalar header. The all-zero input is the ordinary padding query. -/
theorem packed_at {G a b:ℕ} (f:Field) (fits:P*P<2^b) (query:Fin H→Fin G→Cell a)
    (v:Fin H) (g:Fin G) (p q:Fin P) (reads:(query v g).val=(PairRanks.pair p q).val+1):
    (lookup (directory R fits f v) (query v g) (List.finRange (P*P))).val=numberAt R f v p q:=by
  rw [lookup_at _ _ _ reads]
  simp [directory,PairRanks.pair]

theorem packed_ghost {G a b:ℕ} (f:Field) (fits:P*P<2^b) (query:Fin H→Fin G→Cell a)
    (v:Fin H) (g:Fin G) (absent:query v g=0):lookup (directory R fits f v) (query v g) (List.finRange (P*P))=0:=by
  apply lookup_missing
  intro j
  simp [absent]

end
end Hierarchy.DescentOrdinaryDonorRankDirectory

end OAI
