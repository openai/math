import OAI.Computability.BorderVNP.CellSparseExteriorBatchRow
import OAI.Computability.BorderVNP.CellSparseExteriorNativeRun

/-! # Execution of the full owned sparse external input preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

open VPVNP.BurstRAM CellPacketEncode Finset

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- Physical state after precisely the first `i` compact task rows have been encoded. -/
def written (l : Layout) (owned : ℕ → Owned) (initial : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => initial
  | i+1 => (owned i).image l i (written l owned initial i)

/-- All operands read by one native iteration, including the addressed interval
data and the raw count-and-use suffix in the original dense physical bank. -/
def Owned.Source (o : Owned) (l : Layout) (i a : ℕ) : Prop :=
  a ∈ o.addresses l i ∨
    (l.triples+3*o.first ≤ a ∧ a < l.triples+3*(o.first+o.field.spans.length)) ∨
    (o.dense+o.field.width ≤ a ∧ a < o.dense+o.field.width+o.field.tail.length) ∨
    ∃ r ∈ o.field.spans, r.source ≤ a ∧ a < r.source+r.bits.length

/-- An address not mutated by this iteration's encoded bits or three publications. -/
def Owned.Outside (o : Owned) (l : Layout) (i a : ℕ) : Prop :=
  (a<o.dest l ∨ o.dest l+o.field.bytes.length ≤ a) ∧
  a≠l.tasks+7*i+2 ∧ a≠l.tasks+7*i+3 ∧ a≠l.counts+o.global

/-- Exact entry-level row, original physical live inputs and every word-fit test. -/
structure Owned.Initial (o : Owned) (l : Layout) (i : ℕ) (m : Memory w) : Prop where
  row : o.Stored l i (readings m)
  inputs : Native.Stored m (l.triples+3*o.first) (o.dense+o.field.width) o.field.spans o.field.tail
  fits : o.Fits l i w
  ordered : Ordered o.field.width 0 o.field.spans
  room : Native.Room w (l.triples+3*o.first) (o.dense+o.field.width) (o.dest l) o.field.bytes.length o.field.spans o.field.tail

/-- Any live address outside earlier result regions has its exact original value. -/
theorem written_preserve (l : Layout) (owned : ℕ → Owned) (m : ℕ → ℕ) {i j : ℕ} (ij : i ≤ j)
    (a : ℕ) (safe : ∀ k, i ≤ k → k < j → (owned k).Outside l k a) :
    written l owned m j a=written l owned m i a := by
  induction j with
  | zero => have := Nat.eq_zero_of_le_zero ij; subst i; rfl
  | succ j ih =>
    by_cases last : i=j+1
    · rw [last]
    · obtain ⟨outside,t₁,t₂,ct⟩ := safe j (by omega) (by omega)
      rw [written,Owned.image,Function.update_of_ne ct,Function.update_of_ne t₂,
        Function.update_of_ne t₁,putDigits_outside _ _ _ _ outside]
      exact ih (by omega) fun k hk hk' => safe k hk (by omega)

/-- Transport an original row's verified data through preceding disjoint cell writes. -/
theorem Owned.Initial.congr {l : Layout} {o : Owned} {i : ℕ} {m mt : Memory w} (h : o.Initial l i m)
    (same : ∀ a, o.Source l i a → readings mt a=readings m a) : o.Initial l i mt := by
  have scalar (a : ℕ) (ha : a ∈ o.addresses l i) := same a (.inl ha)
  have hdr := h.row
  have row : o.Stored l i (readings mt) := by
    constructor <;> apply Eq.trans (scalar _ (by simp [Owned.addresses]))
    all_goals first | exact hdr.number | exact hdr.width | exact hdr.base | exact hdr.size | exact hdr.start | exact hdr.length
  refine ⟨row,⟨?_,?_,?_⟩,h.fits,h.ordered,h.room⟩
  · intro j
    have old := h.inputs.rows j
    have atRow (k : ℕ) (hk : k<3) :
        readings mt (l.triples+3*o.first+3*j.val+k) = readings m (l.triples+3*o.first+3*j.val+k) := by
      apply same _ (.inr (.inl ?_))
      have := j.isLt
      omega
    exact ⟨(atRow 0 (by decide)).trans old.logical,(atRow 1 (by decide)).trans old.physical,(atRow 2 (by decide)).trans old.length⟩
  · intro r hr k hk
    exact (same (r.source+k) (.inr (.inr (.inr ⟨r,hr,by omega,by omega⟩)))).trans (h.inputs.sources r hr k hk)
  · intro k hk
    exact (same (o.dense+o.field.width+k) (.inr (.inr (.inl ⟨by omega,by omega⟩)))).trans (h.inputs.reports k hk)

/-- Total per-row allowance, including the counted-loop guard. -/
def Owned.charge (o : Owned) (w : ℕ) := 1+readOwned.slots+(4+Native.ticks w o.field.spans o.field.tail)+publish.slots

private theorem step_run (s : Bank w) (m : Memory w) (l : Layout) (o : Owned) (i : ℕ)
    (ready : l.Ready i (readings s)) (initial : o.Initial l i m) :
    ∃ es t mt, Runs pub mac step s m es t mt ∧ traceCost es+1 ≤ o.charge w ∧
      l.Ready (i+1) (readings t) ∧ readings mt=o.image l i (readings m) := by
  obtain ⟨a,u,read,ha,caller,ptr,past,logical,tail,num,dst,task,dest,counter⟩ :=
    readOwned_run (pub:=pub) (mac:=mac) s m l o i ready initial.row initial.fits
  have endEq : readings u 22=(l.triples+3*o.first)+3*o.field.spans.length := by rw [past]; ring
  obtain ⟨b,v,mv,write,hb,out⟩ := Native.write_run (pub:=pub) (mac:=mac) u m (l.triples+3*o.first)
    o.field.width (o.dense+o.field.width) o.field.spans o.field.tail (by have := initial.fits.constants; omega)
    ptr endEq logical tail num initial.ordered initial.inputs (dst ▸ initial.room)
  have held (j : Reg) (hj : 40 ≤ j.val) : readings v j=readings u j := congrArg Fin.val (write.keepsReg (Native.keeps_high j hj))
  have keep : l.Ready i (readings v) := by
    simp only [Layout.Ready,held 40 (by decide),held 41 (by decide),held 42 (by decide),held 43 (by decide),
      held 44 (by decide),held 45 (by decide),held 46 (by decide),held 47 (by decide),held 48 (by decide),held 53 (by decide)]
    exact caller
  obtain ⟨c,z,mz,pubRun,hc,done,mem⟩ := publish_run (pub:=pub) (mac:=mac) v mv l o i keep
    ((held 49 (by decide)).trans task) ((held 51 (by decide)).trans dest) ((held 52 (by decide)).trans counter)
    (out.cursor.trans (congrArg (·+o.field.bytes.length) dst)) initial.fits
  have effect : readings mv=putDigits (readings m) (o.dest l) o.field.bytes := out.memory.trans (congrArg (fun d => putDigits _ d _) dst)
  refine ⟨_,_,_,read.seq (write.seq pubRun),?_,done,?_⟩
  · rw [show traceCost (a++(b++c))=traceCost a+(traceCost b+traceCost c) from by simp [traceCost,VPVNP.RAMBuckets.cost_append]]
    dsimp only [Owned.charge]
    omega
  · change readings mz=_ at mem
    rw [mem,effect]; rfl

private theorem loop_run (l : Layout) (owned : ℕ → Owned) (m : Memory w)
    (initial : ∀ i < l.count, (owned i).Initial l i m)
    (safe : ∀ i < l.count, ∀ j < i, ∀ a, (owned i).Source l i a → (owned j).Outside l j a)
    (i : ℕ) (hi : i ≤ l.count) (s : Bank w) (mi : Memory w)
    (ready : l.Ready i (readings s)) (current : readings mi=written l owned (readings m) i) :
    ∃ es t mt, Runs pub mac (.whileLt 48 40 step) s mi es t mt ∧
      traceCost es ≤ (∑ j ∈ Ico i l.count, (owned j).charge w)+1 ∧ readings mt=written l owned (readings m) l.count := by
  have cursor := ready.2.2.2.2.2.2.2.2.1
  by_cases last : i=l.count
  · have guard : ¬s 48 < s 40 := show ¬readings s 48<readings s 40 by rw [cursor,ready.1,last]; omega
    exact ⟨_,s,mi,.whileDone guard,by change 1≤_; omega,current.trans (congrArg (written l owned (readings m)) last)⟩
  · have lt : i<l.count := by omega
    have guard : s 48<s 40 := show readings s 48<readings s 40 by rwa [cursor,ready.1]
    have input := (initial i lt).congr (mt:=mi) fun a h => by
      rw [current]; exact written_preserve l owned (readings m) (i:=0) (Nat.zero_le i) a (fun k _ hk => safe i lt k hk a h)
    obtain ⟨x,u,mu,run,hx,ready',img⟩ := step_run (pub:=pub) (mac:=mac) s mi l (owned i) i ready input
    have next : readings mu=written l owned (readings m) (i+1) := by rw [img,current,written]
    obtain ⟨y,t,mt,tail,hy,hm⟩ := loop_run l owned m initial safe (i+1) lt u mu ready' next
    refine ⟨_,_,_,.whileStep guard run tail,?_,hm⟩
    change 1+traceCost (x++y) ≤ _
    rw [show traceCost (x++y)=traceCost x+traceCost y from VPVNP.RAMBuckets.cost_append ..,sum_eq_sum_Ico_succ_bot lt]
    omega
termination_by l.count-i

/-- The actual frame-driven owned scan, including every write of the compressed
external arguments and their pointers, at a linear cost in the true per-row data. -/
theorem prepare_run (s : Bank w) (m : Memory w) (l : Layout) (owned : ℕ → Owned)
    (fp : (pub 0).val=l.frame) (loaded : l.Loaded (readings m))
    (frame : l.frame+92 < 2^w) (header : l.control+36 < 2^w)
    (initial : ∀ i < l.count, (owned i).Initial l i m)
    (safe : ∀ i < l.count, ∀ j < i, ∀ a, (owned i).Source l i a → (owned j).Outside l j a) :
    ∃ es t mt, Runs pub mac prepare s m es t mt ∧
      traceCost es ≤ setup.slots+(∑ i ∈ range l.count, (owned i).charge w)+1 ∧
      readings mt=written l owned (readings m) l.count ∧ (∀ e ∈ es, e.choices=[] ∧ e.sign=.plus) := by
  obtain ⟨x,u,head,hx,ready⟩ := setup_run (pub:=pub) (mac:=mac) s m l fp loaded frame header
  obtain ⟨y,t,mt,tail,hy,hm⟩ := loop_run (pub:=pub) (mac:=mac) l owned m initial safe 0 (Nat.zero_le _) u m ready rfl
  have all := head.seq tail
  refine ⟨_,_,_,all,?_,hm,all.unsigned_events (by decide)⟩
  rw [show traceCost (x++y)=traceCost x+traceCost y from VPVNP.RAMBuckets.cost_append ..]
  simp only [Nat.Ico_zero_eq_range] at hy
  omega

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
