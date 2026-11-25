import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.DescentNeighborOrder
import OAI.Computability.VPVNP.RAMSerialization
import OAI.ThreeFlat.Routing.CallPoolBudget

namespace OAI
/-! # Native packed-vector exchange on a common bounded-degree host -/
namespace Hierarchy.DescentPackedExchange
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open ThreeFlat.Routing
open scoped Classical BigOperators Fin.CommRing
noncomputable section

/-- One dynamic address per neighbor slot, shared across all chunks and all
occurrences at that common position. Missing neighbors use the zero sentinel. -/
def target {H : ℕ} (v : Option (Fin H)) := v.elim H Fin.val
theorem target_le {H : ℕ} (v : Option (Fin H)) : target v≤H := by
  cases v with
  | none=>exact le_rfl
  | some i=>exact i.isLt.le

def packed {w b : ℕ} (x : Fin b→Bool) (c : ℕ) : Word w :=
  (wordBits w).symm (fun i=>if h : c*w+i.val<b then x ⟨c*w+i.val,h⟩ else false)

theorem packed_at {w b : ℕ} (x : Fin b→Bool) (c : ℕ) (i : Fin w) :
    wordBits w (packed x c) i = if h : c*w+i.val<b then x ⟨c*w+i.val,h⟩ else false :=
  congrFun ((wordBits w).apply_symm_apply _) i

def payload {H w b : ℕ} (x : Fin H→Fin b→Bool) (v : Option (Fin H)) (c : ℕ) : Word w :=
  v.elim 0 (fun j=>packed (x j) c)

def batch (w b : ℕ) := poolBatchCount b w
abbrev Port (H degree : ℕ) := Fin H × Fin degree
abbrev Row (H degree w b : ℕ) := Fin (batch w b) × Port H degree

def slot (H degree : ℕ) : Port H degree ≃ Fin (H*degree) := finProdFinEquiv

def id (H degree w b : ℕ) : Row H degree w b ≃ Fin ((H*degree)*batch w b) :=
  (Equiv.prodComm _ _).trans (((slot H degree).prodCongr (Equiv.refl _)).trans finProdFinEquiv)

structure Banks where
  adjacency : Bank
  position : Bank
  chunk : Bank
  vectorOffset : Bank
  data : Bank

def Banks.all (g : Banks) := [g.adjacency,g.position,g.chunk,g.vectorOffset,g.data]

/-- Position and chunk columns have branch-independent entries. Only the
adjacency table and source vectors come from the preceding physical state. -/
def gather (g : Banks) : Expr :=
  .lookup g.data (.op .add (.lookup g.chunk .row) (.lookup g.vectorOffset (.lookup g.adjacency (.lookup g.position .row))))

def work (g : Banks) := (gather g).work
@[simp] theorem work_fixed (g : Banks) : work g=30 := rfl

variable {H degree w b : ℕ}
def rows (H degree w b : ℕ) := (H*degree)*batch w b

def program (out : ℕ) (H degree w b : ℕ) (g : Banks) :=
  scan w out (rows H degree w b) (gather g)

structure Fits (g : Banks) (out H degree w b : ℕ) : Prop where
  banks : ∀ a∈g.all,a.Fits w out
  directory : H*degree≤g.adjacency.size
  position : rows H degree w b≤g.position.size
  chunk : rows H degree w b≤g.chunk.size
  offsets : H+1≤g.vectorOffset.size
  vectors : (H+1)*batch w b≤g.data.size
  output : out+rows H degree w b<2^w

structure Reads (g : Banks) (next : Port H degree → Option (Fin H)) (x : Fin H→Fin b→Bool)
    (m : Memory w) : Prop where
  /-- Mutable preceding-stage graph. The source ordinal is installed only
  once per real position and neighboring port. -/
  adjacency : ∀ a,m (g.adjacency.base+(slot H degree a).val)=(target (next a) : Word w)
  /-- The following two columns are deterministic indexing of the output tape. -/
  position : ∀ a : Row H degree w b,m (g.position.base+(id H degree w b a).val)=
    ((slot H degree a.2).val : Word w)
  chunk : ∀ a : Row H degree w b,m (g.chunk.base+(id H degree w b a).val)=
    (a.1.val : Word w)
  vectorOffset : ∀ v : Option (Fin H),m (g.vectorOffset.base+target v)=(target v*batch w b : ℕ)
  /-- True bit fields packed into consecutive chunks at each common position. -/
  data : ∀ c : Fin (batch w b), ∀ v : Option (Fin H),
    m (g.data.base+(c.val+target v*batch w b))=payload x v c.val

/-- The three static columns are public arithmetic functions of the output row
and the ceiling chunk count. Their values can be installed once in immutable
header space; they do not depend on the graph or on the represented bits. -/
def PositionROM (H degree w b : ℕ) := Fin (rows H degree w b) ⊕ (Fin (rows H degree w b) ⊕ Fin (H+1))

def publicWord : PositionROM H degree w b→Word w
  | .inl r=>((slot H degree ((id H degree w b).symm r).2).val : ℕ)
  | .inr (.inl r)=>(((id H degree w b).symm r).1.val : ℕ)
  | .inr (.inr v)=>(v.val*batch w b : ℕ)

def publicAddress (g : Banks) : PositionROM H degree w b→ℕ
  | .inl r=>g.position.base+r.val
  | .inr (.inl r)=>g.chunk.base+r.val
  | .inr (.inr v)=>g.vectorOffset.base+v.val

def publicPin (r : PositionROM H degree w b) (j : Fin w) : Bool := wordBits w (publicWord r) j

theorem from_frame (g : Banks) (next : Port H degree→Option (Fin H)) (x : Fin H→Fin b→Bool)
    (m : Memory w)
    (fixed : ∀ r : PositionROM H degree w b,∀ j : Fin w,wordBits w (m (publicAddress g r)) j=publicPin r j)
    (oldAdj : ∀a,m (g.adjacency.base+(slot H degree a).val)=(target (next a) : Word w))
    (oldData : ∀ (c : Fin (batch w b)) (v : Option (Fin H)),
      m (g.data.base+(c.val+target v*batch w b))=payload x v c.val) : Reads g next x m := by
  have word (r : PositionROM H degree w b) : m (publicAddress g r)=publicWord r :=
    (wordBits w).injective (funext (fixed r))
  refine ⟨oldAdj,?_,?_,?_,oldData⟩
  · intro a;simpa [publicAddress,publicWord] using word (.inl (id H degree w b a))
  · intro a;simpa [publicAddress,publicWord] using word (.inr (.inl (id H degree w b a)))
  · intro v
    exact word (.inr (.inr ⟨target v,Nat.lt_succ_of_le (target_le v)⟩))

private theorem bank_read {w out : ℕ} (g : Bank) (m : Memory w) (i : ℕ)
    (hi : i<g.size) (fit : g.Fits w out) :
    g.read m (i : Word w)=m (g.base+i) := by
  simp [Bank.read,Fin.val_cast_of_lt (hi.trans fit.2.1),Nat.mod_eq_of_lt hi]

theorem read {out : ℕ} (g : Banks) (fit : Fits g out H degree w b)
    (next : Port H degree→Option (Fin H)) (x : Fin H→Fin b→Bool) (m : Memory w)
    (real : Reads g next x m) (a : Row H degree w b) :
    (gather g).eval m ((id H degree w b a).val : Word w)=payload x (next a.2) a.1.val := by
  let r:=id H degree w b a
  have hrow : r.val<rows H degree w b := r.isLt
  have addr : a.1.val+target (next a.2)*batch w b<g.data.size := by
    have full : (target (next a.2)).succ * batch w b ≤ (H+1) * batch w b :=
      Nat.mul_le_mul_right (batch w b) (Nat.succ_le_succ (target_le (next a.2)))
    rw [Nat.succ_mul] at full
    rw [Nat.add_comm a.1.val]
    exact ((Nat.add_lt_add_left a.1.isLt _).trans_le full).trans_le fit.vectors
  change g.data.read m (g.chunk.read m (r.val : Word w) +
    g.vectorOffset.read m (g.adjacency.read m (g.position.read m (r.val : Word w)))) = _
  rw [bank_read g.chunk m r.val (hrow.trans_le fit.chunk) (fit.banks _ (by simp [Banks.all])),real.chunk a,
      bank_read g.position m r.val (hrow.trans_le fit.position) (fit.banks _ (by simp [Banks.all])),real.position a,
      bank_read g.adjacency m (slot H degree a.2).val ((slot H degree a.2).isLt.trans_le fit.directory)
        (fit.banks _ (by simp [Banks.all])),real.adjacency a.2,
      bank_read g.vectorOffset m (target (next a.2)) ((Nat.lt_succ_of_le (target_le (next a.2))).trans_le fit.offsets)
        (fit.banks _ (by simp [Banks.all])),real.vectorOffset (next a.2),
      ← Nat.cast_add (R := Word w) a.1.val (target (next a.2)*batch w b)]
  exact (bank_read g.data m _ addr (fit.banks _ (by simp [Banks.all]))).trans (real.data a.1 (next a.2))

theorem spec (g : Banks) (out : ℕ) (fit : Fits g out H degree w b)
    (next : Port H degree→Option (Fin H)) (x : Fin H→Fin b→Bool) :
    (program out H degree w b g).Spec (Reads g next x)
      (fun src after=>after=image out (rows H degree w b) (gather g) src ∧
        ∀ a : Row H degree w b,after (out+(id H degree w b a).val)=payload x (next a.2) a.1.val)
      (4+rows H degree w b*(2*work g+4)) ∧ CheapCode (program out H degree w b g) := by
  refine ⟨?_,scan_cheap w out (rows H degree w b) (gather g)⟩
  have fits : (gather g).Fits w out := by
    simp only [gather,Expr.Fits,fit.banks g.data (by simp [Banks.all]),fit.banks g.chunk (by simp [Banks.all]),
      fit.banks g.adjacency (by simp [Banks.all]),fit.banks g.vectorOffset (by simp [Banks.all]),fit.banks g.position (by simp [Banks.all]),and_self]
  intro P N K machine pc reg pub exit rom pubRegs cfg m start input
  obtain ⟨time,clock,done,after,run,ended,mem⟩:=scan_exec out (rows H degree w b) (gather g) m
    fits fit.output machine pc reg pub exit rom pubRegs cfg m start rfl
  refine ⟨time,clock,done,after,run,ended,mem,?_⟩
  intro a
  rw [mem]
  have hi : (id H degree w b a).val<rows H degree w b := (id H degree w b a).isLt
  simpa [image,fillSegment,show out≤out+(id H degree w b a).val ∧
    out+(id H degree w b a).val<out+rows H degree w b by omega,Nat.cast_add] using
    read g fit next x m input a

/-- Every input bank is below the destination, including the branch-dependent
adjacency and payloads. The scan also preserves every memory word outside its output. -/
theorem frame (out : ℕ) (g : Banks) (m : Memory w) (a : ℕ)
    (older : a<out ∨ out+rows H degree w b≤a) :
    image out (rows H degree w b) (gather g) m a=m a := by
  simp [image,fillSegment,show ¬(out≤a ∧ a<out+rows H degree w b) by omega]

def neighborSlot {V : Type} [Fintype V] (name : V≃Fin H) (near : V→Finset V)
    (a : Port H degree) : Option (Fin H) :=
  let ns:=near (name.symm a.1)
  if hi : a.2.val<Fintype.card ns then
    some (name (((neighborOrder name ns).symm ⟨a.2.val,hi⟩).val)) else none

theorem neighbor_at {V : Type} [Fintype V] (name : V≃Fin H) (near : V→Finset V)
    (cap : ∀ v,(near v).card≤degree) {v u : V} (peer : u∈near v) :
    ∃ d : Fin degree,neighborSlot name near (name v,d)=some (name u) := by
  let ns:=near (name.symm (name v))
  have hu : u∈ns := by simpa only [ns,Equiv.symm_apply_apply] using peer
  let n : ns:=⟨u,hu⟩
  let t:=(neighborOrder name ns) n
  have hd : Fintype.card ns≤degree := by simpa only [ns,Fintype.card_coe] using cap (name.symm (name v))
  refine ⟨⟨t.val,t.isLt.trans_le hd⟩,?_⟩
  change (if hi : t.val<Fintype.card ns then some (name (((neighborOrder name ns).symm ⟨t.val,hi⟩).val))
    else none) = some (name u)
  rw [dite_eq_left t.isLt]
  exact congrArg (fun z : ns => some (name z.val)) ((neighborOrder name ns).symm_apply_apply n)

theorem neighbor_info {V : Type} [Fintype V] (name : V≃Fin H) (near : V→Finset V)
    (a : Port H degree) (u : V) (hit : neighborSlot name near a=some (name u)) :
    ∃ h : u∈near (name.symm a.1),
      ((neighborOrder name (near (name.symm a.1))) ⟨u,h⟩).val=a.2.val := by
  let ns:=near (name.symm a.1)
  change (if hi : a.2.val<Fintype.card ns then some (name (((neighborOrder name ns).symm ⟨a.2.val,hi⟩).val))
    else none) = some (name u) at hit
  split at hit
  · rename_i valid
    let v : ns:=(neighborOrder name ns).symm ⟨a.2.val,valid⟩
    have eq : v.val=u := name.injective (Option.some.inj hit)
    subst u
    exact ⟨v.2,congrArg Fin.val ((neighborOrder name ns).apply_symm_apply _)⟩
  · contradiction

def reciprocal {V : Type} (near : V→Finset V) (v : V) := (near v).filter (fun u=>v∈near u)

theorem reciprocal_cap {V : Type} (near : V→Finset V) (cap : ∀ v,(near v).card≤degree) (u : V) :
    (reciprocal near u).card≤degree := (Finset.card_filter_le ..).trans (cap u)

theorem reciprocal_symm {V : Type} (near : V→Finset V) (v u : V) :
    u∈reciprocal near v ↔ v∈reciprocal near u := by simp [reciprocal,and_comm]

/-- For each payload position, even the largest individual source word is read
at most degree times. A self-loop occupies one slot. The proof recovers the
canonical local slot from its true vertex and the returned source word. -/
theorem bounded_reads {V : Type} [Fintype V] (name : V≃Fin H) (near : V→Finset V)
    (cap : ∀v,(near v).card≤degree) (symm : ∀v u,u∈near v → v∈near u) (u : V) :
    Fintype.card {a : Port H degree // neighborSlot name near a=some (name u)}≤degree := by
  classical
  let inj : {a : Port H degree // neighborSlot name near a=some (name u)} ↪ (near u) :=
    ⟨fun a=>⟨name.symm a.val.1,symm _ _ (neighbor_info name near a.val u a.2).choose⟩,by
      rintro ⟨⟨i,d⟩,ha⟩ ⟨⟨j,l⟩,hb⟩ eq
      have hv : i=j := name.symm.injective (congrArg Subtype.val eq)
      subst j
      obtain ⟨_,ja⟩:=neighbor_info name near (i,d) u ha
      obtain ⟨_,jb⟩:=neighbor_info name near (i,l) u hb
      exact Subtype.ext (Prod.ext rfl (Fin.ext (ja.symm.trans jb)))⟩
  exact (Fintype.card_le_of_embedding inj).trans (by simpa only [Fintype.card_coe] using cap u)

theorem neighbor_read {V : Type} [Fintype V] (name : V≃Fin H) (near : V→Finset V)
    (cap : ∀ v,(near v).card≤degree) {v u : V} (peer : u∈near v)
    (x : Fin H→Fin b→Bool) (after : Memory w) (out : ℕ)
    (reads : ∀ a : Row H degree w b,after (out+(id H degree w b a).val)=
      payload x (neighborSlot name near a.2) a.1.val) :
    ∃ d : Fin degree, ∀ c : Fin (batch w b), ∀ j : Fin w,
      wordBits w (after (out+(id H degree w b (c,name v,d)).val)) j =
        if h : c.val*w+j.val<b then x (name u) ⟨c.val*w+j.val,h⟩ else false := by
  obtain ⟨d,nearby⟩:=neighbor_at name near cap peer
  refine ⟨d,fun c j=>?_⟩
  rw [reads (c,name v,d)]
  simp only [nearby,payload,Option.elim_some]
  exact packed_at ..

/-- In each common position the initial directory, both static progression
columns and the output are charged per word. An extra blank position per chunk
is shared by all missing slots. -/
def tapeWords (N H degree w b : ℕ) := N+H*degree+(H+1)+3*rows H degree w b+(H+1)*batch w b

theorem batch_bits (w b : ℕ) : batch w b*w≤b+w :=
  (Nat.div_mul_le_self _ _).trans (Nat.sub_le ..)

theorem volume (N H degree w b : ℕ) (occupied : 0<H) :
    tapeWords N H degree w b*w ≤ (4*degree+4)*((N+H)*w+H*b) := by
  have units:=batch_bits w b
  have hostBound:=Nat.mul_le_mul_left H units
  have rep:=Nat.mul_le_mul_left (3*degree) hostBound
  have pad:=Nat.mul_le_mul_left (H+1) units
  unfold tapeWords rows
  nlinarith only [rep,hostBound,pad,occupied,Nat.zero_le N,Nat.zero_le (degree*N*w),
    Nat.zero_le (degree*H*w),Nat.zero_le (degree*H*b),Nat.zero_le (N*w),Nat.zero_le (H*b),Nat.zero_le (H*w),
    Nat.mul_le_mul_right b (show 1≤H by omega),Nat.mul_le_mul_right w (show 1≤H by omega)]

/-- Allocate the actual masked banks consecutively. Their power-of-two padding is
included in the returned span. -/
def bankAt (start n : ℕ) : Bank := ⟨start,n.log2+1⟩
def bankEnd (a : Bank) := a.base+a.size

def place (start H degree w b : ℕ) : Banks :=
  let adj:=bankAt start (H*degree)
  let pos:=bankAt (bankEnd adj) (rows H degree w b)
  let chunk:=bankAt (bankEnd pos) (rows H degree w b)
  let offset:=bankAt (bankEnd chunk) (H+1)
  let data:=bankAt (bankEnd offset) ((H+1)*batch w b)
  ⟨adj,pos,chunk,offset,data⟩

theorem bank_size (start n : ℕ) :
    n≤(bankAt start n).size ∧ (bankAt start n).size≤2*(n+1) := by
  refine ⟨Nat.lt_log2_self.le,?_⟩
  change 2^(n.log2+1)≤2*(n+1)
  rw [Nat.pow_succ]
  by_cases h : n=0
  · simp [h]
  · have := Nat.log2_self_le h
    omega

theorem placed_fits (start H degree w b : ℕ)
    (stop : bankEnd (place start H degree w b).data+rows H degree w b<2^w) :
    Fits (place start H degree w b) (bankEnd (place start H degree w b).data) H degree w b := by
  refine ⟨?_,(bank_size ..).1,(bank_size ..).1,(bank_size ..).1,(bank_size ..).1,(bank_size ..).1,stop⟩
  intro a member
  simp only [Banks.all,place,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl <;>
    refine ⟨Nat.two_pow_pos _,?_,?_⟩ <;>
    dsimp only [place,bankEnd,bankAt] at * <;> omega

theorem placed_span (start H degree w b : ℕ) :
    bankEnd (place start H degree w b).data+rows H degree w b≤
      start+2*tapeWords 0 H degree w b+10 := by
  have a:=(bank_size 0 (H*degree)).2
  have z:=(bank_size 0 (rows H degree w b)).2
  have v:=(bank_size 0 (H+1)).2
  have c:=(bank_size 0 ((H+1)*batch w b)).2
  dsimp [place,bankEnd,bankAt,tapeWords,Bank.size] at *
  omega

end
end Hierarchy.DescentPackedExchange

end OAI
