import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! Lifting a physically reached old host to a successor host number.
The public chart contains only source coordinates and local shape transitions. -/
namespace Hierarchy.DescentOrdinaryPeerLifts
open DescentSixParty.Chronology DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H P S n w out : ℕ}

structure Entry (H P S : ℕ) where
  host : Fin H
  slot : Fin P
  shape : Fin S

def Entry.index (p : Entry H P S) : Fin (H*P) := finProdFinEquiv (p.host,p.slot)

abbrev Request (H P S n : ℕ) := Fin n → Option (Entry H P S)

structure Tables where
  sender : Bank
  select : Bank
  shape : Bank
  origin : Bank

/-- The measured count suppresses all rows for padded receivers. The old roster
supplies the entire dynamic part of a neighbor address. -/
def issue (T : Tables) (count old : Bank) (H Hnew : ℕ) : Expr :=
  let src:=Expr.lookup T.sender .row
  let reached:=Expr.lookup old (.lookup T.select .row)
  .branch .lt src (.lookup count (.lit 0))
    (.branch .lt reached (.lit H)
      (.op .add (.lookup T.origin reached) (.lookup T.shape .row)) (.lit Hnew)) (.lit Hnew)

def result (N Hnew S : ℕ) (peer : Fin H→Fin P→Option (Fin H)) (p : Option (Entry H P S)) : ℕ :=
  p.elim Hnew fun a=>
    if a.host.val<N then (peer a.host a.slot).elim Hnew (fun v=>v.val*S+a.shape.val) else Hnew

structure Room (T : Tables) (count old : Bank) (H P n w out : ℕ) : Prop where
  sender : T.sender.Fits w out
  select : T.select.Fits w out
  shape : T.shape.Fits w out
  origin : T.origin.Fits w out
  count : count.Fits w out
  prior : old.Fits w out
  senders : n≤T.sender.size
  choices : n≤T.select.size
  shapes : n≤T.shape.size
  origins : H≤T.origin.size
  reached : H*P≤old.size
  bound : H<2^w

structure Reads (T : Tables) (count old : Bank) (N : ℕ) (req : Request H P S n)
    (peer : Fin H→Fin P→Option (Fin H)) (m : Memory w) : Prop where
  total : m count.base=(N:Word w)
  sender : ∀i,m (T.sender.base+i.val)=(((req i).elim H (fun x=>x.host.val) : ℕ):Word w)
  select : ∀i,m (T.select.base+i.val)=(((req i).elim 0 (fun x=>x.index.val) : ℕ):Word w)
  shape : ∀i,m (T.shape.base+i.val)=(((req i).elim 0 (fun x=>x.shape.val) : ℕ):Word w)
  origin : ∀j : Fin H,m (T.origin.base+j.val)=((j.val*S:ℕ):Word w)
  peer : ∀(v:Fin H)(j:Fin P),m (old.base+(finProdFinEquiv (v,j)).val)=(((peer v j).elim H Fin.val : ℕ):Word w)

theorem fits (T : Tables) (count old : Bank) (Hnew : ℕ) (s : Room T count old H P n w out) :
    (issue T count old H Hnew).Fits w out :=
  ⟨⟨s.sender,trivial⟩,⟨s.count,trivial⟩,
    ⟨⟨s.prior,s.select,trivial⟩,trivial,⟨⟨s.origin,s.prior,s.select,trivial⟩,⟨s.shape,trivial⟩⟩,trivial⟩,trivial⟩

private theorem lt_read {a b : ℕ} (ha:a<2^w) (hb:b<2^w) :
    Comparison.lt.test (a:Word w) (b:Word w)=decide (a<b) := by
  simp [Comparison.test, Fin.lt_def, Fin.val_cast_of_lt ha, Fin.val_cast_of_lt hb]

theorem eval (T : Tables) (count old : Bank) (N Hnew : ℕ) (req : Request H P S n)
    (peer : Fin H→Fin P→Option (Fin H)) (m : Memory w) (bounded : N≤H)
    (s : Room T count old H P n w out) (reads : Reads T count old N req peer m) (i : Fin n) :
    (issue T count old H Hnew).eval m (i.val:Word w)=(result N Hnew S peer (req i):Word w) := by
  have sr:=(bank_read T.sender m (i.isLt.trans_le s.senders) s.sender).trans (reads.sender i)
  have ix:=(bank_read T.select m (i.isLt.trans_le s.choices) s.select).trans (reads.select i)
  have sh:=(bank_read T.shape m (i.isLt.trans_le s.shapes) s.shape).trans (reads.shape i)
  have cn : count.read m (0:Word w)=(N:Word w):=
    (bank_read count m s.count.1 s.count).trans (by simpa using reads.total)
  have pe (a : Entry H P S) : old.read m (a.index.val:Word w)=(((peer a.host a.slot).elim H Fin.val : ℕ):Word w):=
    (bank_read old m (a.index.isLt.trans_le s.reached) s.prior).trans (reads.peer a.host a.slot)
  have orig (v : Fin H) : T.origin.read m (v.val:Word w)=((v.val*S:ℕ):Word w):=
    (bank_read T.origin m (v.isLt.trans_le s.origins) s.origin).trans (reads.origin v)
  simp only [issue,Expr.eval,sr,ix,sh,Nat.cast_zero,cn]
  cases eqn : req i with
  | none =>
    simp [result,lt_read s.bound (bounded.trans_lt s.bound),Nat.not_lt_of_ge bounded]
  | some a =>
    simp only [result,Option.elim_some, lt_read (a.host.isLt.trans s.bound) (bounded.trans_lt s.bound),pe a]
    by_cases live : a.host.val<N
    · simp only [live,decide_true,ite_true]
      cases peer a.host a.slot with
      | none=>simp [lt_read s.bound s.bound]
      | some v=>simp [lt_read (v.isLt.trans s.bound) s.bound,v.isLt,orig v,RowOp.opcode,BinaryOp.eval]
    · simp [live]

def phase (w out n H Hnew : ℕ) (T : Tables) (count old : Bank) : NativePhase w :=
  let e:=issue T count old H Hnew
  ⟨scan w out n e,4+n*(2*e.work+4),ProtocolRAM.image out n e,scan_cheap w out n e⟩

theorem any (T : Tables) (count old : Bank) (Hnew : ℕ) (m : Memory w) (s : Room T count old H P n w out)
    (ok : out+n<2^w) :
    let p:=phase w out n H Hnew T count old
    p.Runs m ∧ ∀a,a<out ∨ out+n≤a→p.image m a=m a :=by
  dsimp only
  refine ⟨?_,fun address outside=>ProtocolRAMGeneratedWrite.frame_image out n (issue T count old H Hnew) m address outside⟩
  exact @scan_exec w out n (issue T count old H Hnew) m (fits T count old Hnew s) ok

theorem emit (T : Tables) (count old : Bank) (N Hnew : ℕ) (req : Request H P S n)
    (peer : Fin H→Fin P→Option (Fin H)) (m : Memory w) (bounded : N≤H)
    (s : Room T count old H P n w out) (reads : Reads T count old N req peer m) (i : Fin n) :
    (phase w out n H Hnew T count old).image m (out+i.val)=(result N Hnew S peer (req i):Word w) :=
  (ProtocolRAMGeneratedWrite.read_image _ _ _ _ i).trans (eval T count old N Hnew req peer m bounded s reads i)

end
end Hierarchy.DescentOrdinaryPeerLifts

end OAI
