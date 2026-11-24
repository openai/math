import OAI.Computability.VPVNP.CompressorShrinkKernelSlices
import OAI.Computability.VPVNP.CompressorShrinkMotifOrder

/-!
# Scanning the shrinking supply rows

Each dense term contributes four surviving rows. The width cells use the
absolute old CD arc number. The interval frames use the dense term number.
The total cell immediately precedes each row's private interval workspace.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSliceSweep

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression SliceSchedule ShrinkSliceArrays

variable {w : ℕ}

private theorem rows_separate {i j width : ℕ} (hne : i ≠ j) :
    i*width+width ≤ j*width ∨ j*width+width ≤ i*width := by
  rcases lt_or_gt_of_ne hne with hi | hj
  · exact Or.inl (Nat.succ_mul i width ▸ Nat.mul_le_mul_right width hi)
  · exact Or.inr (Nat.succ_mul j width ▸ Nat.mul_le_mul_right width hj)

/-- Per-row physical ports of the surviving slice schedule. -/
structure Row (w : ℕ) where
  /-- Address of the selected term record supplying the surviving width for this motif and
  role. -/
  term : Word w
  /-- The supply worker receives the selected layout and role coordinate, the selector width,
  and the address of the total. -/
  supply : Fin 3 → Word w
  /-- Number of subdivisions into which this surviving supply width is split. -/
  count : Word w
  /-- First output address for the subdivision widths of this old arc and role. -/
  dst : Word w
  /-- First address of the interval descriptor workspace for this dense motif and role. -/
  bank : Word w

/-- The cell where the supply worker writes the selected role's total width before subdivision. -/
def Row.total (r : Row w) := r.supply 2

/-- The address is outside the row's total cell, subdivision widths and interval descriptor
bank. -/
def Row.Outside (r : Row w) (x : ℕ) : Prop :=
  x ≠ r.total.val ∧ (x < r.dst.val ∨ r.dst.val+r.count.val ≤ x) ∧
    (x < r.bank.val ∨ stop r.bank.val 1 r.count.val ≤ x)

/-- Native reports in chronological order, with every return/choice checked
by the existing segment semantics. -/
structure Run (r : Row w) (width : ℕ) (initial out : Memory w) (reports : List (Report w)) : Prop where
  executed : ∃ split desc,
    let call := supplyReport r.supply r.term initial
    let mid := after initial call.events
    let M := (template supplyOps 0).instantiate w r.supply
    execute M.program 16 (M.program.start r.term) initial [] = some call ∧
    (mid r.total.val).val = width ∧
    SplitPass r.total r.count r.dst mid split ∧
    Built r.total r.dst r.bank [width] (List.ofFn (splitWidth width r.count.val)) (after mid (eventLog split)) desc ∧
    out = desc.result (after mid (eventLog split)) ∧ reports = call :: (split ++ desc.all)

/-- Readout and frame information for one completed row. The terminal memory
of its interval pass supplies the values inside that row's descriptor bank. -/
structure Image (r : Row w) (width : ℕ) (out : Memory w) : Prop where
  total : (out r.total.val).val = width
  widths : ∀ j : Fin r.count.val, (out (r.dst.val+j.val)).val = splitWidth width r.count.val j
  descriptors : ∃ before stored, Stored r.bank [width] (List.ofFn (splitWidth width r.count.val)) before stored ∧
    ∀ x, r.bank.val ≤ x → x < stop r.bank.val 1 r.count.val → out x = stored x

theorem Image.keep {r : Row w} {width : ℕ} {before out : Memory w} (h : Image r width before)
    (frame : ∀ x, ¬ r.Outside x → out x = before x) : Image r width out := by
  constructor
  · rw [frame _ (fun hn => hn.1 rfl)]; exact h.total
  · intro j
    rw [frame _ (fun hn => by have := hn.2.1; have := j.isLt; omega)]
    exact h.widths j
  · obtain ⟨src,stored,hs,hv⟩ := h.descriptors
    refine ⟨src,stored,hs,fun x hl hu => ?_⟩
    exact (frame x (fun hn => by have := hn.2.2; omega)).trans (hv x hl hu)

/-- Replaying the reports reaches the final memory used by the next row. -/
theorem Run.replay {r : Row w} {b : ℕ} {init out : Memory w} {reports : List (Report w)}
    (run : Run r b init out reports) : after init (eventLog reports) = out := by
  obtain ⟨s,d,_,_,_,_,rfl,rfl⟩ := run.executed
  simp only [Passes.all,Passes.result,Passes.tested,Passes.prepared,SliceRAM.preparationAfter,
    eventLog,List.flatMap_cons,List.flatMap_append,after,List.foldl_append]

/-- All supply-row writes preserve every cell outside that row. -/
theorem Run.frame {r : Row w} {b : ℕ} {init out : Memory w} {reports : List (Report w)}
    (run : Run r b init out reports) {x : ℕ} (hx : r.Outside x) : out x = init x := by
  obtain ⟨s,d,_,_,hs,hd,rfl,_⟩ := run.executed
  rw [hd.stored.outside _ (by simpa only [List.length_singleton,List.length_ofFn] using hx.2.2),
    hs.widths.frame x hx.2.1,(supply_native r.supply r.term init).2.1]
  exact ite_eq_right hx.1

/-- Once the split and descriptor workspaces fit, the complete row stores
the chosen width, the subdivisions and the interval records. -/
theorem Run.image {r : Row w} {b : ℕ} {init out : Memory w} {reports : List (Report w)}
    (run : Run r b init out reports) (space : Workspace r.total r.dst r.bank 1 r.count.val)
    (apart : r.total.val < r.dst.val ∨ r.dst.val+r.count.val ≤ r.total.val) : Image r b out := by
  obtain ⟨s,d,_,ht,hs,hd,rfl,_⟩ := run.executed
  constructor
  · rw [hd.stored.outside _ (by
      simp only [List.length_singleton,List.length_ofFn]; have := space.oldApart; omega),
      hs.widths.frame _ apart]
    exact ht
  · intro j
    rw [hd.stored.outside _ (by
      simp only [List.length_singleton,List.length_ofFn]; have := space.newApart; have := j.isLt; omega)]
    exact (hs.widths.rows j j.isLt).trans (congrArg (fun b => splitWidth b r.count.val j) ht)
  · exact ⟨_,_,hd.stored,fun _ _ _ => rfl⟩

/-- A supply row with q subdivisions uses one source-reader call, q split
calls and the descriptor builder. Its total calls plus probes are linear in q. -/
theorem Run.cost {r : Row w} {b : ℕ} {init out : Memory w} {reports : List (Report w)}
    (run : Run r b init out reports) :
    reports.length = 5+5*r.count.val ∧ (reports.map Report.probes).sum ≤ 10+21*r.count.val ∧
      (reports.map (fun t => t.events.length+1)).sum ≤ 54+112*r.count.val := by
  obtain ⟨s,d,_,_,hs,hd,_,rfl⟩ := run.executed
  let q := r.count.val
  have hp : (s.map Report.probes).sum = 2*s.length := by
    have he : s.map Report.probes = List.replicate s.length 2 :=
      List.map_eq_replicate_iff.mpr (fun x hx => (hs.cost x hx).1)
    simp [he,Nat.mul_comm]
  have hi : (s.map (fun x => x.events.length+1)).sum = 16*s.length := by
    have he : s.map (fun x => x.events.length+1) = List.replicate s.length 16 :=
      List.map_eq_replicate_iff.mpr (fun x hx => (hs.cost x hx).2)
    simp [he,Nat.mul_comm]
  have hk := copyRecords_length_le [b] (List.ofFn (splitWidth b q))
  have hc := (supply_native r.supply r.term init).2.2
  simp only [List.length_singleton,List.length_ofFn,one_mul,q] at hk
  simp only [List.length_cons,List.length_append,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
    hd.calls,hd.probes,hd.instructions,List.length_nil,List.length_ofFn,hp,hi,hs.length,hc.1,hc.2]
  omega

variable {ι : Type*}

/-- In the supplied order, thread each interval builder's output memory into
the first width read of the next row. -/
inductive Runs (r : ι → Row w) (b : ι → ℕ) :
    List ι → Memory w → Memory w → List (Report w) → Prop where
  | nil (m : Memory w) : Runs r b [] m m []
  | cons {i : ι} {is : List ι} {m next out : Memory w} {head tail : List (Report w)} :
      Run (r i) (b i) m next head → Runs r b is next out tail → Runs r b (i::is) m out (head++tail)

theorem Runs.replay {r : ι → Row w} {b : ι → ℕ} {is : List ι} {m out : Memory w}
    {rs : List (Report w)} (h : Runs r b is m out rs) : after m (eventLog rs) = out := by
  induction h with
  | nil => rfl
  | @cons _ _ m next _ head tail step _ ih =>
    rw [show after m (eventLog (head ++ tail)) = after (after m (eventLog head)) (eventLog tail) from
      by simp only [after,eventLog,List.flatMap_append,List.foldl_append],step.replay,ih]

/-- Exact memory frame of a sequence of native rows. -/
theorem Runs.frame {r : ι → Row w} {b : ι → ℕ} {is : List ι} {m out : Memory w}
    {rs : List (Report w)} (h : Runs r b is m out rs) {x : ℕ}
    (hx : ∀ i ∈ is, (r i).Outside x) : out x = m x := by
  induction h with
  | nil => rfl
  | @cons i is _ _ _ _ _ step _ ih =>
    exact (ih fun j hj => hx j (List.mem_cons_of_mem _ hj)).trans (step.frame (hx i List.mem_cons_self))

theorem Runs.cost {r : ι → Row w} {b : ι → ℕ} {is : List ι} {m out : Memory w}
    {rs : List (Report w)} (h : Runs r b is m out rs) {Q : ℕ} (hq : ∀ i ∈ is, (r i).count.val ≤ Q) :
    rs.length ≤ is.length*(5+5*Q) ∧ (rs.map Report.probes).sum ≤ is.length*(10+21*Q) ∧
      (rs.map (fun t => t.events.length+1)).sum ≤ is.length*(54+112*Q) := by
  induction h with
  | nil => simp
  | @cons i is _ _ _ _ _ step _ ih =>
    obtain ⟨ac,ap,ai⟩ := step.cost
    obtain ⟨bc,bp,bi⟩ := ih fun j hj => hq j (List.mem_cons_of_mem _ hj)
    have := hq i List.mem_cons_self
    simp only [List.length_append,List.length_cons,List.map_append,List.sum_append]
    rw [Nat.add_mul,Nat.add_mul,Nat.add_mul,one_mul,one_mul,one_mul]
    omega

/-- Scan actual workers with disjoint output rows. The returned images coexist
in a single final memory and the read-only term table remains usable throughout. -/
theorem scan {r : ι → Row w} {b : ι → ℕ} (ready : Memory w → Prop)
    (space : ∀ i, Workspace (r i).total (r i).dst (r i).bank 1 (r i).count.val)
    (apart : ∀ i, (r i).total.val < (r i).dst.val ∨ (r i).dst.val+(r i).count.val ≤ (r i).total.val)
    (separate : ∀ {i j}, i ≠ j → ∀ x, ¬ (r i).Outside x → (r j).Outside x)
    (keep : ∀ i m out, ready m → (∀ x, (r i).Outside x → out x = m x) → ready out)
    (worker : ∀ i m, ready m → ∃ out rs, Run (r i) (b i) m out rs)
    (is : List ι) (m : Memory w) (hready : ready m) (nodup : is.Nodup) :
    ∃ out rs, Runs r b is m out rs ∧ ready out ∧ ∀ i ∈ is, Image (r i) (b i) out := by
  induction is generalizing m with
  | nil => exact ⟨m,[],.nil _,hready,by simp⟩
  | cons i is ih =>
    obtain ⟨next,head,run⟩ := worker i m hready
    have nd := List.nodup_cons.mp nodup
    obtain ⟨out,tail,done,hr,stored⟩ := ih next (keep i _ _ hready fun _ hx => run.frame hx) nd.2
    refine ⟨out,head++tail,.cons run done,hr,fun j hj => ?_⟩
    rcases List.mem_cons.mp hj with rfl | hj
    · apply (run.image (space j) (apart j)).keep
      intro x hx
      exact done.frame fun k hk => separate (i := j) (j := k) (fun e => nd.1 (e.symm ▸ hk)) x hx
    · exact stored j hj


variable {n A : ℕ}

/-- The dense term rectangle precedes the absolute-ID width rectangle.
Interval records follow in dense order, leaving the term rows read-only. -/
structure Allocation (w n A : ℕ) where
  /-- First address of the selected term records, stored in dense motif order. -/
  termBase : ℕ
  /-- Reserved word count between consecutive dense term records. -/
  termStride : ℕ
  /-- First address of the surviving-width table indexed by absolute old arc and supply role. -/
  widthBase : ℕ
  /-- Injectively map a dense motif ordinal to its absolute old CD arc number for locating its
  widths. -/
  absolute : Fin n ↪ Fin A
  /-- The subdivision count assigned to each of the four supply roles. -/
  subdiv : Fin 4 → ℕ
  /-- Selector-bit count supplied to the worker when it reads a selected term's supply
  coordinate. -/
  selectors : Word w
  /-- The selected layout side used to choose the four supply coordinates from each term. -/
  layout : Bool

namespace Allocation

variable (D : Allocation w n A)

/-- A surviving row identified by its dense motif ordinal and one of four supply roles. -/
abbrev Id (n : ℕ) := Fin n × Fin 4

/-- Words reserved for a surviving-width row, using the sum of the four role subdivision
counts. -/
def stride := ∑ t, D.subdiv t
/-- Words reserved for each dense role's total and interval workspace, five plus seven times
the width-row stride. -/
def recordStride := 5+7*D.stride
/-- Exclusive end of all absolute arc/role width rows and starting address for the dense
interval records. -/
def widthEnd := D.widthBase+(A*4)*D.stride
/-- Exclusive end of the full allocation, after the width table and all dense motif/role
interval records. -/
def last := D.widthEnd+(n*4)*D.recordStride

/-- Flatten the absolute old arc number and role into a single index of the width table. -/
def absoluteKey (i : Id n) : Fin (A*4) := finProdFinEquiv (D.absolute i.1,i.2)
/-- Flatten the dense motif ordinal and role into a single index of the interval-record table. -/
def denseKey (i : Id n) : Fin (n*4) := finProdFinEquiv i
/-- Starting address of the selected term at a given dense motif ordinal. -/
def termStart (i : Fin n) := D.termBase+i.val*D.termStride
/-- Starting address of the surviving widths for the given motif's absolute old arc and role. -/
def widthStart (i : Id n) := D.widthBase+(D.absoluteKey i).val*D.stride
/-- Starting address of the total and interval workspace for a given dense motif and role. -/
def recordStart (i : Id n) := D.widthEnd+(denseKey i).val*D.recordStride

/-- Term records have room for ten fields and precede the widths, all roles have positive
subdivisions, and the allocation and eight supply coordinates fit in words. -/
structure Fits : Prop where
  termStride : 10 ≤ D.termStride
  terms : D.termBase+n*D.termStride ≤ D.widthBase
  positive : ∀ t, 0 < D.subdiv t
  room : D.last < 2^w
  roles : 8 < 2^w

/-- Build the physical operands for a motif/role sweep, placing its total first in the dense
record and its interval workspace immediately afterward. -/
def row (i : Id n) : Row w :=
  let total := Fin.ofNat _ (D.recordStart i)
  ⟨Fin.ofNat _ (D.termStart i.1),supplyData (Fin.ofNat _ (D.layout.toNat*4+i.2.val)) D.selectors total,
    Fin.ofNat _ (D.subdiv i.2),Fin.ofNat _ (D.widthStart i),Fin.ofNat _ (D.recordStart i+1)⟩

private theorem sub_le (i : Fin 4) : D.subdiv i ≤ D.stride :=
  Finset.single_le_sum (fun j _ => Nat.zero_le (D.subdiv j)) (Finset.mem_univ _)

private theorem width_stop (i : Id n) : D.widthStart i + D.stride ≤ D.widthEnd := by
  have h := Nat.mul_le_mul_right D.stride (D.absoluteKey i).isLt
  rw [Nat.succ_mul] at h
  dsimp [widthStart,widthEnd]; omega

private theorem record_stop (i : Id n) : D.recordStart i + D.recordStride ≤ D.last := by
  have h := Nat.mul_le_mul_right D.recordStride (denseKey i).isLt
  rw [Nat.succ_mul] at h
  dsimp [recordStart,last]; omega

theorem term_stop (h : D.Fits) (i : Fin n) : D.termStart i+10 ≤ D.widthBase := by
  have hcap := Nat.mul_le_mul_right D.termStride i.isLt
  rw [Nat.succ_mul] at hcap
  have := h.termStride
  have := h.terms
  dsimp [termStart]; omega

private theorem width_lt (h : D.Fits) (i : Id n) : D.widthStart i < 2^w := by
  have hstop := D.width_stop i
  have hl : D.widthEnd ≤ D.last := Nat.le_add_right ..
  exact ((Nat.le_add_right ..).trans (hstop.trans hl)).trans_lt h.room

private theorem record_fit (h : D.Fits) (i : Id n) : D.recordStart i+1 < 2^w := by
  have := D.record_stop i
  have := h.room
  simp only [recordStride] at *; omega

theorem row_vals (h : D.Fits) (i : Id n) :
    let r := D.row i
    r.term.val = D.termStart i.1 ∧ r.total.val = D.recordStart i ∧ r.bank.val = D.recordStart i+1 ∧
      r.dst.val = D.widthStart i ∧ r.count.val = D.subdiv i.2 := by
  have hs := D.sub_le i.2
  have hb := D.term_stop h i.1
  have h₁ := D.width_stop i
  have h₂ : D.widthBase ≤ D.widthStart i := Nat.le_add_right ..
  have h₃ : D.widthEnd ≤ D.last := Nat.le_add_right ..
  have h₄ := D.record_fit h i
  have h₅ := h.room
  exact ⟨Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt h₄,
    Nat.mod_eq_of_lt (D.width_lt h i),Nat.mod_eq_of_lt (by omega)⟩

private theorem local_stop (i : Id n) : stop (D.recordStart i+1) 1 (D.subdiv i.2) ≤
    D.recordStart i+D.recordStride := by
  have := D.sub_le i.2
  simp [stop,frameHead,recordStride]; omega

theorem space (h : D.Fits) (i : Id n) :
    Workspace (D.row i).total (D.row i).dst (D.row i).bank 1 (D.row i).count.val := by
  obtain ⟨_,ht,hb,hd,hc⟩ := D.row_vals h i
  have hs := D.sub_le i.2
  have hw := D.width_stop i
  have hr := D.record_stop i
  have he : D.widthEnd ≤ D.recordStart i := Nat.le_add_right ..
  have hf := h.room
  have hl := D.local_stop i
  constructor
  · rw [hb,hc]; omega
  · rw [ht]; omega
  · rw [hd,hc]; omega
  · left; rw [ht,hb]
  · left; rw [hd,hb,hc]; omega

theorem apart (h : D.Fits) (i : Id n) :
    (D.row i).total.val < (D.row i).dst.val ∨
      (D.row i).dst.val+(D.row i).count.val ≤ (D.row i).total.val := by
  obtain ⟨_,ht,_,hd,hc⟩ := D.row_vals h i
  right
  rw [ht,hd,hc]
  exact (Nat.add_le_add_left (D.sub_le i.2) _).trans ((D.width_stop i).trans (Nat.le_add_right ..))

private theorem key_injective : Function.Injective D.absoluteKey := by
  intro i j he
  have h := finProdFinEquiv.injective he
  exact Prod.ext (D.absolute.injective (Prod.mk.inj h).1) (Prod.mk.inj h).2

private theorem outside_iff (h : D.Fits) (i : Id n) (x : ℕ) :
    (D.row i).Outside x ↔ (x < D.widthStart i ∨ D.widthStart i+D.subdiv i.2 ≤ x) ∧
      (x < D.recordStart i ∨ stop (D.recordStart i+1) 1 (D.subdiv i.2) ≤ x) := by
  obtain ⟨_,ht,hb,hd,hc⟩ := D.row_vals h i
  simp only [Row.Outside,ht,hb,hd,hc,stop,frameHead,one_mul]
  omega

theorem separate (h : D.Fits) {i j : Id n} (hne : i ≠ j) (x : ℕ)
    (hi : ¬ (D.row i).Outside x) : (D.row j).Outside x := by
  rw [D.outside_iff h i] at hi
  rw [D.outside_iff h j]
  have hkey : (D.absoluteKey i).val ≠ (D.absoluteKey j).val :=
    fun e => hne (D.key_injective (Fin.ext e))
  have hden : (denseKey i).val ≠ (denseKey j).val :=
    fun e => hne (finProdFinEquiv.injective (Fin.ext e))
  have hw := rows_separate (width := D.stride) hkey
  have hr := rows_separate (width := D.recordStride) hden
  have hwi := D.width_stop i
  have hwj := D.width_stop j
  have hci := D.sub_le i.2
  have hcj := D.sub_le j.2
  have hri := D.local_stop i
  have hrj := D.local_stop j
  dsimp only [widthStart,recordStart] at *
  omega

/-- The two rectangles cover every address touched by any surviving row. -/
theorem rowOutside (h : D.Fits) (i : Id n) (x : ℕ) (hx : x < D.widthBase ∨ D.last ≤ x) :
    (D.row i).Outside x := by
  rw [D.outside_iff h i]
  have hw : D.widthBase ≤ D.widthStart i := Nat.le_add_right ..
  have hr : D.widthBase ≤ D.recordStart i := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have he : D.widthEnd ≤ D.last := Nat.le_add_right ..
  have h₁ := D.width_stop i
  have h₂ := D.sub_le i.2
  have h₃ := D.local_stop i
  have h₄ := D.record_stop i
  omega

theorem termOutside (h : D.Fits) (i : Id n) (j : Fin n) (x : ℕ) (hx : x < D.termStart j+10) :
    (D.row i).Outside x := by
  rw [D.outside_iff h i]
  have hterm := D.term_stop h j
  have hw : D.widthBase ≤ D.widthStart i := Nat.le_add_right ..
  have hr : D.widthBase ≤ D.recordStart i := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  exact ⟨Or.inl (by omega),Or.inl (by omega)⟩

end Allocation

end CompressorRecords.ShrinkSliceSweep

end VPVNP
end Computability
end OAI
