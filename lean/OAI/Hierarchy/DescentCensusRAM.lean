import OAI.Hierarchy.ProtocolRAMGeneratedWriteCheap
import OAI.Hierarchy.ProtocolRAMWeightedScatter

namespace OAI
/-! # Native cumulative counts from two original measurement expressions -/

namespace Hierarchy.DescentCensusRAM
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators

variable {w n B : ℕ}

/-- Two temporary columns, followed by the interleaved scatter tape and
the cumulative bins, can be reused across any number of streams. -/
structure Banks (w n B : ℕ) where
  first : ℕ
  second : ℕ
  tape : ℕ
  bins : ℕ
  scratch : first+n≤ second
  beforeTape : second+n≤tape
  beforeBins : tape+2*n≤bins
  finish : bins+B<2^w

def slot (tape offset : ℕ) : Expr := .op .add (.lit (tape+offset)) (.op .add .row .row)

def atSlot (tape offset : ℕ) (i : Fin n) := tape+2*i.val+offset

theorem eval_slot (tape offset : ℕ) (m : Memory w) (i : Fin n) :
    (slot tape offset).eval m (i.val:Word w)=(atSlot tape offset i:Word w) := by
  simp only [slot,Expr.eval,RowOp.opcode,BinaryOp.eval,atSlot]
  push_cast
  ring

def issue (S : Banks w n B) (d : ℕ) (value : Expr) :=
  ProtocolRAMGeneratedWrite.program w S.first S.second n (slot S.tape d) value

def issueCost (tape d n : ℕ) (value : Expr) := ProtocolRAMGeneratedWrite.work n (slot tape d) value

def issued (S : Banks w n B) (d : ℕ) (V : Expr) (value : Fin n→ℕ) (m : Memory w) :=
  ProtocolRAMGeneratedWrite.image S.first S.second (slot S.tape d) V (atSlot S.tape d)
    (fun i=>(value i:Word w)) m

theorem issue_exec (S : Banks w n B) (d : ℕ) (hd : d<2) (V : Expr) (value : Fin n→ℕ) (m : Memory w)
    (fit : V.Fits w S.first) (read : ∀i,V.eval m (i.val:Word w)=(value i:Word w)) :
    (issue S d V).Exec m (issued S d V value m) (issueCost S.tape d n V) := by
  obtain ⟨a,b,t,z,ab,bt,tz,room⟩ := S
  apply ProtocolRAMGeneratedWrite.run a b (slot t d) V (atSlot t d) (fun i=>(value i:Word w)) m
    (by exact ⟨trivial,trivial,trivial⟩) fit ab (by omega) (eval_slot t d m) read
  · intro i;have := i.isLt;unfold atSlot;omega
  · intro i j;have := i.isLt;unfold atSlot;omega
  · intro i j;have := i.isLt;unfold atSlot;omega

theorem issued_at (S : Banks w n B) (d : ℕ) (V : Expr) (value : Fin n→ℕ) (m : Memory w) (i : Fin n) :
    issued S d V value m (atSlot S.tape d i)=(value i:Word w) := by
  apply ProtocolRAMGeneratedWrite.read
  intro x y eqn
  apply Fin.ext
  unfold atSlot at eqn
  omega

theorem issued_away (S : Banks w n B) (d : ℕ) (V : Expr) (value : Fin n→ℕ) (m : Memory w) (a : ℕ)
    (below : a<S.first ∨ S.tape≤a) (away : ∀i : Fin n,a≠atSlot S.tape d i) : issued S d V value m a=m a := by
  obtain ⟨k,v,t,b,kv,vt,tb,fit⟩ := S
  change a<k ∨ t≤a at below
  exact ProtocolRAMGeneratedWrite.frame k v (slot t d) V (atSlot t d) (fun i=>(value i:Word w)) m a
    away (by rcases below with h|h <;> omega) (by rcases below with h|h <;> omega)

def add (S : Banks w n B) (key value : Expr) :=
  ((issue S 0 key).seq (issue S 1 value)).seq (ProtocolRAMWeightedScatter.program w S.tape n)

def addCost (S : Banks w n B) (key value : Expr) :=
  issueCost S.tape 0 n key+issueCost S.tape 1 n value+(3+12*n)

def afterAdd (S : Banks w n B) (key value : Expr) (tag : Fin n→Fin B) (wt : Fin n→ℕ) (m : Memory w) :=
  let dest := fun i=>S.bins+(tag i).val
  ProtocolRAMWeightedScatter.image dest wt (issued S 1 value wt (issued S 0 key dest m)) n

theorem scatter_issued (S : Banks w n B) (key value : Expr) (tag : Fin n→Fin B) (wt : Fin n→ℕ) (m : Memory w) :
    let dest := fun i=>S.bins+(tag i).val
    let v := issued S 1 value wt (issued S 0 key dest m)
    (ProtocolRAMWeightedScatter.program w S.tape n).Exec v (afterAdd S key value tag wt m) (3+12*n) := by
  let dest := fun i=>S.bins+(tag i).val
  let a := issued S 0 key dest m
  let v := issued S 1 value wt a
  have source (i : Fin n) : v (S.tape+2*i.val)=(dest i:Word w) ∧ v (S.tape+2*i.val+1)=(wt i:Word w) := by
    refine ⟨?_,issued_at S 1 value wt a i⟩
    rw [show v (S.tape+2*i.val)=a (S.tape+2*i.val) from
      issued_away S 1 value wt a _ (.inr (by omega)) (fun j=>by unfold atSlot;omega)]
    simpa only [atSlot,Nat.add_zero] using issued_at S 0 key dest m i
  change (ProtocolRAMWeightedScatter.program w S.tape n).Exec v (afterAdd S key value tag wt m) _
  intro P R K M pc reg pub exit installed params cfg raw entry eq
  exact ProtocolRAMWeightedScatter.run S.tape dest wt v
    (S.beforeBins.trans (by have := S.finish;omega))
    (fun i=>by have := (tag i).isLt;have := S.finish;dsimp [dest];omega)
    (fun i=>.inr (by have := S.beforeBins;dsimp [dest];omega)) source M pc reg pub exit installed params cfg raw entry eq

theorem add_exec (S : Banks w n B) (key value : Expr) (tag : Fin n→Fin B) (wt : Fin n→ℕ) (m : Memory w)
    (kf : key.Fits w S.first) (vf : value.Fits w S.first)
    (keys : ∀i : Fin n,key.eval m (i.val:Word w)=((S.bins+(tag i).val:ℕ):Word w))
    (values : ∀i : Fin n,value.eval m (i.val:Word w)=(wt i:Word w)) :
    (add S key value).Exec m (afterAdd S key value tag wt m) (addCost S key value) := by
  let dest := fun i=>S.bins+(tag i).val
  let a := issued S 0 key dest m
  let v := issued S 1 value wt a
  have sk : (issue S 0 key).Exec m a (issueCost S.tape 0 n key) := issue_exec S 0 (by decide) key dest m kf keys
  have sv : (issue S 1 value).Exec a v (issueCost S.tape 1 n value) := issue_exec S 1 (by decide) value wt a vf (fun i=>
    (eval_below value _ m a vf (fun j hj=>issued_away S _ _ _ _ j (.inl hj)
      (fun z=>by have := S.scratch;have := S.beforeTape;unfold atSlot;omega))).trans (values i))
  have run : (ProtocolRAMWeightedScatter.program w S.tape n).Exec v (afterAdd S key value tag wt m) (3+12*n) := scatter_issued S key value tag wt m
  intro P R U M pc reg pub ep prog data cfg raw entry eqn
  exact Procedure.Exec.then (Procedure.Exec.then sk sv) run M pc reg pub ep prog data cfg raw entry eqn

def sumAt (tag : Fin n→Fin B) (wt : Fin n→ℕ) (j : Fin B) := ∑i,if tag i=j then wt i else 0

theorem add_read (S : Banks w n B) (key value : Expr) (tag : Fin n→Fin B) (wt : Fin n→ℕ)
    (m : Memory w) (j : Fin B) :
    afterAdd S key value tag wt m (S.bins+j.val)=m (S.bins+j.val)+(sumAt tag wt j:Word w) := by
  let dest := fun i=>S.bins+(tag i).val
  let a := S.bins+j.val
  have old (d : ℕ) (h : d<2) (val : Expr) (weight : Fin n→ℕ) (mem : Memory w) :
      issued S d val weight mem a=mem a := by
    apply issued_away _ _ _ _ _ _ (.inr (by have := S.beforeBins;dsimp [a];omega))
    intro i;have := S.beforeBins;have := i.isLt;dsimp [a,atSlot];omega
  have same (i : Fin n) : dest i=a ↔ tag i=j := by simp [dest,a,Fin.ext_iff]
  change issued S 1 value wt (issued S 0 key dest m) a+_ = _
  rw [old 1 (by decide),old 0 (by decide)]
  simp [ProtocolRAMWeightedScatter.partialLoad,Fin.is_lt,sumAt,a,Fin.ext_iff]

theorem add_frame (S : Banks w n B) (key value : Expr) (tag : Fin n→Fin B) (wt : Fin n→ℕ)
    (m : Memory w) (a : ℕ) (old : a<S.first) : afterAdd S key value tag wt m a=m a := by
  let dest := fun i=>S.bins+(tag i).val
  have one (d : ℕ) (v : Expr) (x : Fin n→ℕ) (mem : Memory w) : issued S d v x mem a=mem a :=
    issued_away S _ _ _ _ _ (.inl old) (fun i=>by have := S.scratch;have := S.beforeTape;unfold atSlot;omega)
  change ProtocolRAMWeightedScatter.image dest wt _ n a=m a
  rw [ProtocolRAMWeightedScatter.frame _ _ _ _ _ (fun i=>by have := S.scratch;have := S.beforeTape;have := S.beforeBins;dsimp [dest];omega)]
  exact (one 1 _ _ _).trans (one 0 _ _ _)

def tally (S : Banks w n B) (key value : Expr) :=
  (scan w S.bins B (.lit 0)).seq (add S key value)

def tallyCost (S : Banks w n B) (key value : Expr) := (4+B*6)+addCost S key value

theorem tally_exec (S : Banks w n B) (key value : Expr) (tag : Fin n→Fin B) (wt : Fin n→ℕ) (m : Memory w)
    (kf : key.Fits w S.first) (vf : value.Fits w S.first)
    (keys : ∀i : Fin n,key.eval m (i.val:Word w)=((S.bins+(tag i).val:ℕ):Word w))
    (values : ∀i : Fin n,value.eval m (i.val:Word w)=(wt i:Word w)) :
    ∃ out : Memory w,(tally S key value).Exec m out (tallyCost S key value) ∧
      (∀j : Fin B,out (S.bins+j.val)=(sumAt tag wt j:Word w)) ∧ ∀a<S.first,out a=m a := by
  let clear := ProtocolRAM.image S.bins B (.lit 0) m
  have init : (scan w S.bins B (.lit 0)).Exec m clear (4+B*6) := scan_exec S.bins B (.lit 0) m trivial S.finish
  have keep (a) (h : a<S.first) : clear a=m a :=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by
      have := S.scratch;have := S.beforeTape;have := S.beforeBins;omega))
  have run : (add S key value).Exec clear (afterAdd S key value tag wt clear) (addCost S key value) := add_exec S key value tag wt clear kf vf (fun i=>(eval_below key _ m clear kf keep).trans (keys i))
    (fun i=>(eval_below value _ m clear vf keep).trans (values i))
  refine ⟨_,?_,?_,fun a h=>(add_frame S key value tag wt clear a h).trans (keep a h)⟩
  · intro P R U M pc reg pub ep prog data cfg raw entry eqn
    exact Procedure.Exec.then init run M pc reg pub ep prog data cfg raw entry eqn
  · intro j
    rw [add_read,show clear (S.bins+j.val)=0 from ProtocolRAMGeneratedWrite.read_image _ _ _ _ j,zero_add]

def Banks.take (S : Banks w n B) (r : ℕ) (small : r≤n) : Banks w r B :=
  ⟨S.first,S.second,S.tape,S.bins,by have := S.scratch;omega,by have := S.beforeTape;omega,
    by have := S.beforeBins;omega,S.finish⟩

theorem add_cheap (S : Banks w n B) (key value : Expr) : ProtocolRAM.CheapCode (add S key value) :=
  ProtocolRAM.cheap_seq (ProtocolRAM.cheap_seq (ProtocolRAMRankCheap.generated w S.first S.second n (slot S.tape 0) key)
    (ProtocolRAMRankCheap.generated w S.first S.second n (slot S.tape 1) value))
    (ProtocolRAMWeightedScatter.cheap w S.tape n)

theorem tally_cheap (S : Banks w n B) (key value : Expr) : ProtocolRAM.CheapCode (tally S key value) :=
  ProtocolRAM.cheap_seq (ProtocolRAM.scan_cheap w S.bins B (.lit 0)) (add_cheap S key value)

end Hierarchy.DescentCensusRAM

end OAI
