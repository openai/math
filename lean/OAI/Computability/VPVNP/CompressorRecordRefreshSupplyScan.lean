import OAI.Computability.VPVNP.CompressorRecordRefreshNewSlots
import OAI.Computability.VPVNP.DegreeRefreshPass
import OAI.Computability.VPVNP.CompressorTermRecord

/-!
# Reading the chosen supply widths of every refresh block

A term record stores its grid row, repetition count, and integer payload widths in
port/expander-slot order. The internal arcs in the degree refresh have additional selector
fields, one per repetition. This pass reads the chosen term at the source's block and
writes the total width to the supply column in the site order used by the slot emitter.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.SupplyScan

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open Compression Compression.Refresh Compression.DegreeRefresh NewSlots
open scoped Fin.CommRing

variable {bits : ℕ}

/-- The seven supply-scan operands give port and lane counts, expander degree, term base and
stride, selector width, and supply base. -/
def params (D R h : ℕ) (termBase : BurstRAM.Word bits) (stride selectors : ℕ)
    (supplyBase : BurstRAM.Word bits) : Fin 7 → BurstRAM.Word bits :=
  ![word D,word R,word h,termBase,word stride,word selectors,supplyBase]

/-- The cursor ranges over all site/expander-slot pairs in supply-table order. -/
def visit : List (Op 8 7) :=
  [.stateWord 0, .publicWord 1 0, .publicWord 2 1, .publicWord 3 2,
   .binary .div 4 0 3, .binary .mod 5 0 3, .binary .div 6 4 2, .binary .mod 4 4 2,
   .binary .mod 7 6 1, .binary .div 6 6 1, .binary .mul 6 6 2, .binary .add 6 6 4,
   .publicWord 4 4, .binary .mul 6 6 4, .publicWord 4 3, .binary .add 6 4 6,
   .constant 4 1, .binary .add 4 6 4, .read 4 4, .publicWord 2 5, .binary .mul 4 4 2,
   .binary .mul 7 7 3, .binary .add 7 7 5, .constant 2 2, .binary .add 7 7 2,
   .binary .add 7 6 7, .read 7 7, .binary .add 4 7 4, .publicWord 6 6,
   .binary .add 6 6 0, .write 6 4, .constant 7 1, .binary .add 0 0 7]

variable (p : Fin 7 → BurstRAM.Word bits)

/-- Recover the promoted site from a supply cursor by dividing out the expander slot. -/
def site (i : BurstRAM.Word bits) := BinaryOp.div.eval i (p 2)
/-- Recover the packed old vertex and promoted port by dividing out the residual lane. -/
def vertexPort (i : BurstRAM.Word bits) := BinaryOp.div.eval (site p i) (p 1)
/-- Compute the selected term's block ordinal from the old vertex and residual lane, discarding
the promoted port. -/
def block (i : BurstRAM.Word bits) :=
  BinaryOp.div.eval (vertexPort p i) (p 0) * p 1 + BinaryOp.mod.eval (site p i) (p 1)
/-- Index the selected payload coordinate by promoted port and local expander slot. -/
def coordinate (i : BurstRAM.Word bits) :=
  BinaryOp.mod.eval (vertexPort p i) (p 0) * p 2 + BinaryOp.mod.eval i (p 2)
/-- First word of the fixed-stride term record for the cursor's block. -/
def header (i : BurstRAM.Word bits) := p 3 + block p i * p 4
/-- Address of the selected port-and-slot payload width after the term record's two header
words. -/
def payload (i : BurstRAM.Word bits) := header p i + (coordinate p i + 2)
/-- Compute the internal width as the stored payload width plus the repetition count times the
selector width. -/
def value (m : Memory bits) (i : BurstRAM.Word bits) :=
  m (payload p i).val + m (header p i+1).val * p 5

/-- The 33-event visit reads the repetition count and payload width and publishes the resulting
internal width. -/
def events (m : Memory bits) (i : BurstRAM.Word bits) : List (Event bits) :=
  [.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,
   .tick,.tick,.tick,.tick,.read (header p i+1) (m (header p i+1).val),.tick,.tick,.tick,
   .tick,.tick,.tick,.tick,.read (payload p i) (m (payload p i).val),.tick,.tick,.tick,
   .write (p 6+i) (value p m i),.tick,.tick]

theorem events_work (m : Memory bits) (i : BurstRAM.Word bits) :
    (events p m i).length = 33 ∧ countProbes (events p m i) = 3 := ⟨rfl,rfl⟩

theorem events_after (m : Memory bits) (i : BurstRAM.Word bits) :
    after m (events p m i) = writeMemory m (p 6+i) (value p m i) := rfl

set_option maxRecDepth 4096 in
private theorem visit_trace (m : Memory bits) (i : BurstRAM.Word bits) (rs : Regs bits 8) :
    ∃ out, trace p i visit rs m = some (events p m i,out,writeMemory m (p 6+i) (value p m i)) ∧
      out 0 = i+1 := by
  simp (config := {decide := true}) [visit, events, value, header, payload, block, coordinate,
    site, vertexPort, trace, Op.effect, BinaryOp.eval, Function.update]

theorem visit_native (m : Memory bits) (i : BurstRAM.Word bits) :
    let M := (template visit 0).instantiate bits p
    execute M.program 34 (M.program.start i) m [] = some ⟨events p m i,some (i+1)⟩ := by
  obtain ⟨out, ht, hret⟩ := visit_trace p m i (fun _ => 0)
  let M := (template visit 0).instantiate bits p
  change execute M.program (1 + visit.length) ⟨M.entry, i, fun _ => 0, fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace, ht]; simp [hret]

/-- The term fields used by the pass lie outside the output column. -/
def Apart (n : ℕ) : Prop :=
  ∀ i j : BurstRAM.Word bits, i.val < n → j.val < n →
    (header p i+1).val ≠ (p 6+j).val ∧ (payload p i).val ≠ (p 6+j).val

/-- The address is outside every supply destination whose cursor is less than the specified
count. -/
def Outside (n addr : ℕ) : Prop :=
  ∀ j : BurstRAM.Word bits, j.val < n → addr ≠ (p 6+j).val

/-- Materialized width rows and the memory frame through the given cursor. -/
structure Prefix (initial m : Memory bits) (k : ℕ) : Prop where
  rows : ∀ i : BurstRAM.Word bits, i.val < k → m (p 6+i).val = value p initial i
  frame : ∀ addr, Outside p k addr → m addr = initial addr

private theorem step (initial m : Memory bits) {n : ℕ} (apart : Apart p n) (i : BurstRAM.Word bits)
    (hi : i.val < n) (cur : Prefix p initial m i.val) :
    Prefix p initial (writeMemory m (p 6+i) (value p m i)) (i.val+1) := by
  have same : value p m i = value p initial i := by
    rw [value, cur.frame _ (fun j hj => (apart i j hi (hj.trans hi)).2),
      cur.frame _ (fun j hj => (apart i j hi (hj.trans hi)).1)]
    rfl
  constructor
  · intro j hj
    by_cases eq : j = i
    · subst j; simpa [writeMemory] using same
    · have neq : (p 6+j).val ≠ (p 6+i).val := fun h => eq (add_left_cancel (Fin.ext h))
      rw [writeMemory, ite_eq_right neq]
      exact cur.rows j (by have := Fin.val_ne_of_ne eq; omega)
  · intro addr outside
    rw [writeMemory, ite_eq_right (outside i (by omega))]
    exact cur.frame addr (fun j hj => outside j (Nat.lt_succ_of_lt hj))

/-- Native visits extend any prefix in order, preserving all term records. -/
theorem scan_run (initial m : Memory bits) (n k calls : ℕ) (fit : n ≤ 2^bits)
    (apart : Apart p n) (cur : Prefix p initial m k) (room : k+calls ≤ n) :
    let M := (template visit 0).instantiate bits p
    ∃ rs, runSegment M.program 34 (some (Fin.ofNat (2^bits) k)) m (List.replicate calls []) = some rs ∧
      Prefix p initial (after m (eventLog rs)) (k+calls) ∧ rs.length = calls ∧
      ∀ r ∈ rs, r.events.length = 33 ∧ countProbes r.events = 3 := by
  let M := (template visit 0).instantiate bits p
  induction calls generalizing k m with
  | zero => exact ⟨[],rfl,cur,rfl,by simp⟩
  | succ s ih =>
    let i := Fin.ofNat (2^bits) k
    have hv : i.val = k := Nat.mod_eq_of_lt (by omega)
    have next := step p initial m apart i (by omega) (hv ▸ cur)
    have hnext : i+1 = Fin.ofNat (2^bits) (k+1) := by
      apply Fin.ext; rw [Fin.val_add, Fin.val_one', hv, Nat.add_mod_mod]; rfl
    let r : Report bits := ⟨events p m i,some (i+1)⟩
    obtain ⟨rs,run,rows,hl,hw⟩ := ih (writeMemory m (p 6+i) (value p m i)) (k+1) (hv ▸ next) (by omega)
    have hm : after m (eventLog (r :: rs)) = after (writeMemory m (p 6+i) (value p m i)) (eventLog rs) := by
      change List.foldl BurstRAM.update m (events p m i ++ eventLog rs) = _
      rw [List.foldl_append]; rfl
    refine ⟨r :: rs, ?_, ?_, by simp [hl], ?_⟩
    · change runSegment M.program 34 (some i) m (List.replicate (s+1) []) = _
      rw [List.replicate_succ, runSegment, visit_native p m i]
      simp only [M,r,events_after,hnext,run,Option.map_some]
    · simpa [hm, Nat.add_assoc, Nat.add_comm 1 s] using rows
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact events_work p m i
      · exact hw q hq

private theorem scan_cost {rs : List (Report bits)} (hw : ∀ r ∈ rs, countProbes r.events = 3) :
    RAMBuckets.cost Report.probes rs = 4*rs.length := by
  induction rs with
  | nil => simp [RAMBuckets.cost]
  | cons r rs ih =>
    change (1+countProbes r.events)+RAMBuckets.cost Report.probes rs = _
    rw [hw r (List.mem_cons_self ..), ih (fun q h => hw q (List.mem_cons_of_mem _ h)),
      List.length_cons, Nat.mul_succ]
    omega

section Dyadic

open SpectralGeometry MotifConversion

variable {a g a₀ dH : ℕ} {K : Type*} [_root_.Field K] {c₁ c₂ : ℝ}
  (X : State a (a+g)) (E : RegularArcGraph (Fin (2^a)) dH) (hdH : 0 < dH)
  (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock K (expanderSupply E hdH conn) (2^a₀) c₁ c₂)
  (choice : DyadicRefreshChoice X E hdH conn F)
  (termBase : BurstRAM.Word bits) (stride : ℕ) (supplyBase : BurstRAM.Word bits)

local notation "Nₛ" => Fintype.card X.Base * 2^a * 2^g
local notation "O" => sites (D := 2^a) X.baseIndex (bitWordFinEquiv g)
local notation "Iₛ" => blockSupplyWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) E hdH conn F choice
local notation "demand" => blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X)
local notation "pub" => params (2^a) (2^g) dH termBase stride F.selectorBits supplyBase

/-- Term records are indexed by base vertex and residual lane. -/
def recordBase (s : X.Base × BitWord g) : BurstRAM.Word bits :=
  termBase + word ((X.baseIndex s.1).val * 2^g + (bitWordFinEquiv g s.2).val) * word stride

/-- The two physical fields consumed from each selected term. The outer vector uses
the port/expander-slot order of the term writer. -/
structure TermFields (m : Memory bits) : Prop where
  fits : ∀ s, (recordBase X termBase stride s).val + 2 + 2^a * dH < 2^bits
  repetitions : ∀ s, m ((recordBase X termBase stride s).val+1) = word (MotifConversion.repetitions F (demand s))
  payload : ∀ s (e : Fin (2^a) × Fin dH),
    m ((recordBase X termBase stride s).val+2+e.1.val*dH+e.2.val) = word ((choice s).val e)

private theorem finPair_val {n m : ℕ} (i : Fin n) (j : Fin m) :
    (finProdFinEquiv (i,j)).val = i.val*m + j.val := by
  change j.val+m*i.val = _; ring

/-- The natural-number fields of the batch term reader, in its supply-coordinate order,
suffice to construct the word-valued inputs of this scan. -/
theorem TermFields.ofValues (m : Memory bits)
    (fit : ∀ s, (recordBase X termBase stride s).val+2+2^a*dH < 2^bits)
    (rep : ∀ s, (m ((recordBase X termBase stride s).val+1)).val = MotifConversion.repetitions F (demand s))
    (vec : ∀ s (i : Fin (2^a*dH)), (m ((recordBase X termBase stride s).val+2+i.val)).val =
      (choice s).val (finProdFinEquiv.symm i)) : TermFields X E hdH conn F choice termBase stride m := by
  have toWord (x : BurstRAM.Word bits) (v : ℕ) (h : x.val = v) : x = word v :=
    Fin.ext (h.trans (Nat.mod_eq_of_lt (h ▸ x.isLt)).symm)
  refine ⟨fit,fun s => toWord _ _ (rep s),fun s e => toWord _ _ ?_⟩
  have h := vec s (finProdFinEquiv e)
  rw [Equiv.symm_apply_apply] at h
  rw [show (finProdFinEquiv e).val = e.1.val*dH+e.2.val from finPair_val e.1 e.2] at h
  simpa only [Nat.add_assoc] using h

/-- Read the two fields from a physical table of the actual native term memory images.
Each block can have a different input memory, row, and selected repetition count. -/
theorem TermFields.ofRecordMemory (m : Memory bits) (prior : X.Base × BitWord g → Memory bits)
    (row u : X.Base × BitWord g → BurstRAM.Word bits)
    (fit : ∀ s, (recordBase X termBase stride s).val+2+2^a*dH < 2^bits)
    (rep : ∀ s, (u s).val = MotifConversion.repetitions F (demand s))
    (record : ∀ s addr, let b := recordBase X termBase stride s
      b.val ≤ addr → addr < b.val+2+2^a*dH →
      m addr = TermRecord.recordMemory (prior s) b (row s) (u s) finProdFinEquiv.symm (choice s).val addr) :
    TermFields X E hdH conn F choice termBase stride m := by
  have fields (s) := TermRecord.recordMemory_fields (prior s) (recordBase X termBase stride s)
    (row s) (u s) finProdFinEquiv.symm (choice s).val (fit s)
  constructor
  · exact fit
  · intro s
    rw [record s _ (by omega) (by omega), (fields s).2.1, ← rep s]
    exact Fin.ext (Nat.mod_eq_of_lt (u s).isLt).symm
  · intro s e
    let i := finProdFinEquiv e
    have hi : i.val = e.1.val*dH + e.2.val := finPair_val e.1 e.2
    have idx : (recordBase X termBase stride s).val+2+e.1.val*dH+e.2.val =
        (recordBase X termBase stride s).val+2+i.val := by omega
    rw [idx, record s _ (by omega) (by have := i.isLt; omega), (fields s).2.2.1 i]
    simp [i]

/-- Dimension and output-index bounds for the sweep. -/
structure Fits (bits : ℕ) : Prop where
  ports : 2^a < 2^bits
  lanes : 2^g < 2^bits
  degree : dH < 2^bits
  rows : Nₛ*dH ≤ 2^bits

private theorem unpack {x d : BurstRAM.Word bits} {hi lo : ℕ} (h : x.val = hi*d.val+lo) (hl : lo < d.val) :
    (BinaryOp.div.eval x d).val = hi ∧ (BinaryOp.mod.eval x d).val = lo := by
  have hd : 0 < d.val := Nat.zero_lt_of_lt hl
  have hq : x.val / d.val = hi := by rw [h, Nat.mul_comm hi, Nat.mul_add_div hd, Nat.div_eq_of_lt hl, Nat.add_zero]
  exact ⟨(Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)).trans hq,
    (Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt x.isLt)).trans (h ▸ Nat.mul_add_mod_of_lt hl)⟩

/-- The runtime quotient/remainder operations recover the block number and payload
coordinate from the site/slot cursor. -/
private theorem addresses (dims : Fits (dH := dH) X bits)
    (s : (X.Base × BitWord g) × Fin (2^a)) (k : Fin dH) :
    let i : BurstRAM.Word bits := word ((O s).val*dH+k.val)
    header pub i = recordBase X termBase stride s.1 ∧ coordinate pub i = word (s.2.val*dH+k.val) := by
  let i : BurstRAM.Word bits := word ((O s).val*dH+k.val)
  have hlt : (O s).val*dH+k.val < Nₛ*dH := finPair_val (O s) k ▸ (finProdFinEquiv (O s,k)).isLt
  have hv : i.val = (O s).val*dH+k.val := Nat.mod_eq_of_lt (hlt.trans_le dims.rows)
  have h₀ : (pub 0).val = 2^a := Nat.mod_eq_of_lt dims.ports
  have h₁ : (pub 1).val = 2^g := Nat.mod_eq_of_lt dims.lanes
  have h₂ : (pub 2).val = dH := Nat.mod_eq_of_lt dims.degree
  have hk := unpack (d := pub 2) (by simpa only [h₂] using hv) (by rw [h₂]; exact k.isLt)
  have hs : (site pub i).val = ((X.baseIndex s.1.1).val * 2^a + s.2.val)*(pub 1).val +
      (bitWordFinEquiv g s.1.2).val := by rw [site, hk.1, sites_val, h₁]
  have hl := unpack hs (by rw [h₁]; exact (bitWordFinEquiv g s.1.2).isLt)
  have hb := unpack (d := pub 0) (by simpa only [h₀] using hl.1) (by rw [h₀]; exact s.2.isLt)
  have block_eq : block pub i = word ((X.baseIndex s.1.1).val*2^g + (bitWordFinEquiv g s.1.2).val) := by
    apply Fin.ext
    rw [block, vertexPort, Fin.val_add, Fin.val_mul, hb.1, hl.2, h₁, Nat.mod_add_mod]
    rfl
  refine ⟨?_,?_⟩
  · change pub 3 + block pub i * pub 4 = _
    rw [block_eq]; rfl
  · apply Fin.ext
    change (coordinate pub i).val = _ % _
    rw [coordinate, vertexPort, Fin.val_add, Fin.val_mul, hb.2, hk.2, h₂, Nat.mod_add_mod]

private theorem physical_addresses (dims : Fits (dH := dH) X bits)
    (s : (X.Base × BitWord g) × Fin (2^a)) (k : Fin dH)
    (fit : (recordBase X termBase stride s.1).val+2+2^a*dH < 2^bits) :
    let i : BurstRAM.Word bits := word ((O s).val*dH+k.val)
    (header pub i+1).val = (recordBase X termBase stride s.1).val+1 ∧
    (payload pub i).val = (recordBase X termBase stride s.1).val+2+s.2.val*dH+k.val := by
  let i : BurstRAM.Word bits := word ((O s).val*dH+k.val)
  let b := recordBase X termBase stride s.1
  change b.val+2+2^a*dH < 2^bits at fit
  have hk : s.2.val*dH+k.val < 2^a*dH := finPair_val s.2 k ▸ (finProdFinEquiv (s.2,k)).isLt
  have h : (b+1).val = b.val+1 := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2^bits by omega), Nat.mod_eq_of_lt (by omega)]
  have hp : (b + (word (s.2.val*dH+k.val) + 2)).val = b.val+2+s.2.val*dH+k.val := by
    have htwo : (2 : BurstRAM.Word bits).val = 2 := Nat.mod_eq_of_lt (show 2 < 2^bits by omega)
    have hidx : s.2.val*dH+k.val < 2^bits := by omega
    have hidx' : s.2.val*dH+k.val+2 < 2^bits := by omega
    have haddr : b.val+(s.2.val*dH+k.val+2) < 2^bits := by omega
    rw [Fin.val_add, Fin.val_add, Fin.val_ofNat, htwo, Nat.mod_eq_of_lt hidx,
      Nat.mod_eq_of_lt hidx', Nat.mod_eq_of_lt haddr]
    omega
  obtain ⟨hblock,hcoord⟩ := addresses X E hdH conn F termBase stride supplyBase dims s k
  change (header pub i+1).val = _ ∧ (header pub i+(coordinate pub i+2)).val = _
  rw [hblock, hcoord]
  exact ⟨h,hp⟩

/-- A strided term region and a disjoint contiguous supply region satisfy the separation
needed by the physical sweep. Either order of the two regions is allowed. -/
theorem apart_of_intervals (dims : Fits (dH := dH) X bits) (rowFits : 2+2^a*dH ≤ stride)
    (termFit : termBase.val + (Fintype.card X.Base * 2^g)*stride < 2^bits)
    (outFit : supplyBase.val + Nₛ*dH ≤ 2^bits)
    (sep : termBase.val + (Fintype.card X.Base * 2^g)*stride ≤ supplyBase.val ∨
      supplyBase.val + Nₛ*dH ≤ termBase.val) : Apart pub (Nₛ*dH) := by
  intro i j hi hj
  let pos := (finProdFinEquiv (m := Nₛ) (n := dH)).symm ⟨i.val,hi⟩
  let s := (O).symm pos.1
  let k := pos.2
  let key := (X.baseIndex s.1.1).val*2^g + (bitWordFinEquiv g s.1.2).val
  have hkey : key < Fintype.card X.Base * 2^g := by
    simpa only [key, finPair_val] using (finProdFinEquiv (X.baseIndex s.1.1,bitWordFinEquiv g s.1.2)).isLt
  have hroom := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hkey)
  rw [Nat.succ_mul] at hroom
  have hb : (recordBase X termBase stride s.1).val = termBase.val + key*stride := by
    change (termBase.val + ((key % 2^bits)*(stride % 2^bits)) % 2^bits) % 2^bits = _
    rw [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
  have idx : (O s).val*dH+k.val = i.val := by
    have hh : (finProdFinEquiv pos).val = i.val := congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨i.val,hi⟩)
    rw [show (finProdFinEquiv pos).val = pos.1.val*dH+pos.2.val from finPair_val ..] at hh
    simpa only [s,k,Equiv.apply_symm_apply] using hh
  have hid : word ((O s).val*dH+k.val) = i := by rw [idx]; exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hout : (pub 6 + j).val = supplyBase.val+j.val :=
    Nat.mod_eq_of_lt (show supplyBase.val + j.val < 2^bits by omega)
  have hrow : (recordBase X termBase stride s.1).val+2+2^a*dH < 2^bits := by omega
  have hk : s.2.val*dH+k.val < 2^a*dH := finPair_val s.2 k ▸ (finProdFinEquiv (s.2,k)).isLt
  obtain ⟨hrep,hpay⟩ := physical_addresses X E hdH conn F termBase stride supplyBase dims s k hrow
  rw [hid] at hrep hpay
  rw [hrep,hpay,hout,hb]
  constructor <;> omega

/-- Each computed value is the actual selected supply width including selector bits. -/
theorem read_supply (m : Memory bits) (terms : TermFields X E hdH conn F choice termBase stride m)
    (dims : Fits (dH := dH) X bits) (s : (X.Base × BitWord g) × Fin (2^a)) (k : Fin dH) :
    value pub m (word ((O s).val*dH+k.val)) = word (Iₛ s.1 (s.2,k)) := by
  obtain ⟨hrep,hpay⟩ := physical_addresses X E hdH conn F termBase stride supplyBase dims s k (terms.fits s.1)
  rw [value,hrep,hpay,terms.payload s.1 (s.2,k),terms.repetitions]
  apply Fin.ext
  change ((word ((choice s.1).val (s.2,k)) : BurstRAM.Word bits) + word (repetitions F (demand s.1)) *
    word F.selectorBits).val = (((choice s.1).val (s.2,k)) + repetitions F (demand s.1)*F.selectorBits) % _
  simp [Fin.val_add, Fin.val_mul, word, Nat.mod_add_mod, Nat.mod_mul_mod]

/-- Full table for the expander slots of the selected branch, with one native call and
three probes per row, and the exact frame for the shared memory. -/
theorem supply_pass (m : Memory bits) (terms : TermFields X E hdH conn F choice termBase stride m)
    (dims : Fits (dH := dH) X bits) (apart : Apart pub (Nₛ*dH))
    (widthFit : ∀ (s : (X.Base × BitWord g) × Fin (2^a)) (k : Fin dH), Iₛ s.1 (s.2,k) < 2^bits) :
    let M := (template visit 0).instantiate bits pub
    ∃ rs, runSegment M.program 34 (some 0) m (List.replicate (Nₛ*dH) []) = some rs ∧
      (∀ s (k : Fin dH), ((after m (eventLog rs)) (supplyBase + word ((O s).val*dH+k.val)).val).val = Iₛ s.1 (s.2,k)) ∧
      (∀ addr, Outside pub (Nₛ*dH) addr → after m (eventLog rs) addr = m addr) ∧
      RAMBuckets.cost Report.probes rs = 4*(Nₛ*dH) ∧ rs.length = Nₛ*dH ∧
      ∀ r ∈ rs, r.events.length = 33 ∧ countProbes r.events = 3 := by
  have init : Prefix pub m m 0 := ⟨fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ => rfl⟩
  obtain ⟨rs,run,done,hl,hw⟩ := scan_run pub m m (Nₛ*dH) 0 (Nₛ*dH) dims.rows apart init (by simp)
  refine ⟨rs,run,?_,by simpa using done.frame,(scan_cost (fun r h => (hw r h).2)).trans (by rw [hl]),hl,hw⟩
  intro s k
  let i : BurstRAM.Word bits := word ((O s).val*dH+k.val)
  have hk : (O s).val*dH+k.val < Nₛ*dH := finPair_val (O s) k ▸ (finProdFinEquiv (O s,k)).isLt
  have hi : i.val < Nₛ*dH := (Nat.mod_le ..).trans_lt hk
  have stored := done.rows i (by simpa only [Nat.zero_add] using hi)
  change ((after m (eventLog rs)) (pub 6+i).val).val = _
  rw [stored, read_supply X E hdH conn F choice termBase stride supplyBase m terms dims s k]
  exact Nat.mod_eq_of_lt (widthFit s k)

end Dyadic
end CompressorRecords.PortRefresh.SupplyScan

end VPVNP
end Computability
end OAI
