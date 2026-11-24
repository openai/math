import OAI.Computability.VPVNP.CompressorRecordRefreshOldWidths
import OAI.Computability.VPVNP.LaneReindex

/-!
# Constructing the degree-refresh bundle directory

The degree refresh in Appendix E enumerates bundles by base arc and residual lane.
The base slot table contains the destination arc and the old binary displacement.
One native call unpacks these words, translates the lane, and writes the destination
bundle number, the port shift and the initial concatenation offset.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh

open Compression BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {V : Type} {a g n bits : ℕ}

/-- Enumerate each base arc's bundles in increasing order of the remaining lane. -/
def bundleOrder (g : ℕ) (base : V × Fin (2^a) ≃ Fin n) :
    (V × BitWord g) × Fin (2^a) ≃ Fin (n * 2^g) :=
  let perm : (V × BitWord g) × Fin (2^a) ≃ (V × Fin (2^a)) × BitWord g :=
    ⟨fun ((x,l),j) => ((x,j),l), fun ((x,j),l) => ((x,l),j), fun _ => rfl, fun _ => rfl⟩
  perm.trans ((base.prodCongr (bitWordFinEquiv g)).trans finProdFinEquiv)

theorem bundleOrder_val (g : ℕ) (base : V × Fin (2^a) ≃ Fin n)
    (b : (V × BitWord g) × Fin (2^a)) :
    (bundleOrder g base b).val = (base (b.1.1,b.2)).val * 2^g + (bitWordFinEquiv g b.1.2).val := by
  change (bitWordFinEquiv g b.1.2).val + 2^g * (base (b.1.1,b.2)).val = _
  rw [Nat.mul_comm, Nat.add_comm]

namespace BundleDirectory

variable (X : LiftedSlots V (2^a) (BitWord a × BitWord g)) (base : V × Fin (2^a) ≃ Fin n)
  (p : Fin 8 → Word bits)

/-- Parameter zero is the lane count. Tables one and five are the old base target and
displacement. Tables two, three and four are the output columns shared with the segment scan. -/
def visit : List (Op 9 8) :=
  [.stateWord 0, .publicWord 1 0, .binary .div 2 0 1, .binary .mod 3 0 1,
   .publicWord 4 1, .binary .add 4 4 2, .read 5 4,
   .publicWord 4 5, .binary .add 4 4 2, .read 6 4,
   .binary .div 7 6 1, .binary .mod 6 6 1, .binary .bitXor 3 3 6,
   .binary .mul 5 5 1, .binary .add 5 5 3,
   .publicWord 4 2, .binary .add 4 4 0, .write 4 5,
   .publicWord 4 3, .binary .add 4 4 0, .write 4 7,
   .constant 6 0, .publicWord 4 4, .binary .add 4 4 0, .write 4 6,
   .constant 8 1, .binary .add 0 0 8]

/-- Read a word at the indexed offset from a refresh column's public base address. -/
abbrev cell := @RefreshRAM.cell

/-- Decode a bundle ordinal to its old base arc by dividing out the residual lanes. -/
def sourceArc (i : Word bits) := BinaryOp.div.eval i (p 0)

/-- Read the old base arc's packed binary displacement from the shift column. -/
def shiftWord (m : Memory bits) (i : Word bits) := cell p m 5 (sourceArc p i)

/-- Extract the high-order port shift from the packed displacement by dividing by the residual
lane count. -/
def portShift (m : Memory bits) (i : Word bits) := BinaryOp.div.eval (shiftWord p m i) (p 0)

/-- Encode the destination bundle from the old base mate and the residual lane translated by
XOR. -/
def targetWord (m : Memory bits) (i : Word bits) :=
  cell p m 1 (sourceArc p i) * p 0 + BinaryOp.bitXor.eval (BinaryOp.mod.eval i (p 0))
    (BinaryOp.mod.eval (shiftWord p m i) (p 0))

/-- Write the translated bundle number and port shift, and initialize the bundle's running
width total to zero. -/
def update (m : Memory bits) (i : Word bits) : Memory bits :=
  writeMemory (writeMemory (writeMemory m (p 2 + i) (targetWord p m i))
    (p 3 + i) (portShift p m i)) (p 4 + i) 0

/-- The 27-event directory visit reads the old mate and shift and writes the target, port
shift, and zero total. -/
def events (m : Memory bits) (i : Word bits) : List (Event bits) :=
  let e := sourceArc p i
  [.tick, .tick, .tick, .tick, .tick, .tick, .read (p 1 + e) (cell p m 1 e),
   .tick, .tick, .read (p 5 + e) (cell p m 5 e), .tick, .tick, .tick, .tick, .tick,
   .tick, .tick, .write (p 2 + i) (targetWord p m i),
   .tick, .tick, .write (p 3 + i) (portShift p m i),
   .tick, .tick, .tick, .write (p 4 + i) 0, .tick, .tick]

theorem events_work (m : Memory bits) (i : Word bits) :
    (events p m i).length = 27 ∧ countProbes (events p m i) = 5 := ⟨rfl,rfl⟩

theorem events_after (m : Memory bits) (i : Word bits) : after m (events p m i) = update p m i := rfl

set_option maxRecDepth 4096 in
private theorem visit_trace (m : Memory bits) (i : Word bits) (rs : Regs bits 9) :
    ∃ out, trace p i visit rs m = some (events p m i, out, update p m i) ∧ out 0 = i + 1 := by
  simp (config := {decide := true}) [visit, events, update, sourceArc, shiftWord, portShift,
    targetWord, cell, RefreshRAM.cell, trace, Op.effect, BinaryOp.eval, Function.update]
  rfl

/-- The actual table executes from its normal entry and advances the persistent bundle cursor. -/
theorem visit_native (m : Memory bits) (i : Word bits) :
    let M := (template visit 0).instantiate bits p
    execute M.program 28 (M.program.start i) m [] = some ⟨events p m i, some (i + 1)⟩ := by
  obtain ⟨out, ht, hret⟩ := visit_trace p m i (fun _ => 0)
  let M := (template visit 0).instantiate bits p
  change execute M.program (1 + visit.length) ⟨M.entry, i, fun _ => 0, fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace, ht]
  simp [hret]

/-- The base displacement is stored as a port in the high bits and a residual-lane shift
in the low bits. These columns are shared by all the lanes of a base arc. -/
structure BaseTables (m : Memory bits) : Prop where
  lanes : (p 0).val = 2^g
  target : ∀ e, (cell p m 1 (Fin.ofNat _ (base e).val)).val = (base (X.base.target e)).val
  displacement : ∀ e, (cell p m 5 (Fin.ofNat _ (base e).val)).val =
    (bitWordFinEquiv a (X.displacement e).1).val * 2^g + (bitWordFinEquiv g (X.displacement e).2).val

/-- The old graph's ordinary binary displacement cell supplies the packed displacement
required by the directory, after splitting the old lane into port and residual coordinates. -/
theorem BaseTables.ofOld (G : LiftedSlots V (2^a) (BitWord (a+g))) (m : Memory bits)
    (hl : (p 0).val = 2^g)
    (ht : ∀ e, (cell p m 1 (Fin.ofNat _ (base e).val)).val = (base (G.base.target e)).val)
    (hs : ∀ e, (cell p m 5 (Fin.ofNat _ (base e).val)).val =
      (bitWordFinEquiv (a+g) (G.displacement e)).val) :
    BaseTables (relane G (splitBitWord a g)) base p m :=
  ⟨hl, ht, fun e => (hs e).trans (splitBitWord_number a g (G.displacement e))⟩

private theorem unpack {x d : Word bits} {hi lo : ℕ} (h : x.val = hi * d.val + lo) (hl : lo < d.val) :
    (BinaryOp.div.eval x d).val = hi ∧ (BinaryOp.mod.eval x d).val = lo := by
  have hd : 0 < d.val := Nat.zero_lt_of_lt hl
  have hq : x.val / d.val = hi := by
    rw [h, Nat.mul_comm hi, Nat.mul_add_div hd, Nat.div_eq_of_lt hl, Nat.add_zero]
  have hr : x.val % d.val = lo := by rw [h, Nat.mul_add_mod_of_lt hl]
  exact ⟨(Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)).trans hq,
    (Nat.mod_eq_of_lt ((Nat.mod_lt _ hd).trans d.isLt)).trans hr⟩

/-- Decoding an actual source bundle yields precisely its translated target and port shift. -/
theorem translated_row (m : Memory bits) (rep : BaseTables X base p m) (fit : n * 2^g ≤ 2^bits)
    (b : (V × BitWord g) × Fin (2^a)) (i : Word bits) (hi : i.val = (bundleOrder g base b).val) :
    (targetWord p m i).val = (bundleOrder g base (bundleTarget X b)).val ∧
    (portShift p m i).val = (bitWordFinEquiv a (X.displacement (b.1.1,b.2)).1).val := by
  obtain ⟨⟨x,l⟩,j⟩ := b
  let e := (x,j)
  have hs := unpack (d := p 0) (x := i) (by simpa only [rep.lanes, bundleOrder_val] using hi)
    (by simpa only [rep.lanes] using (bitWordFinEquiv g l).isLt)
  have he : sourceArc p i = Fin.ofNat _ (base e).val := by
    apply Fin.ext
    exact hs.1.trans (Nat.mod_eq_of_lt (hs.1 ▸ (sourceArc p i).isLt)).symm
  have sh : (shiftWord p m i).val =
      (bitWordFinEquiv a (X.displacement e).1).val * (p 0).val +
        (bitWordFinEquiv g (X.displacement e).2).val := by
    rw [shiftWord, he, rep.displacement, rep.lanes]
  have ds := unpack sh (by simpa only [rep.lanes] using (bitWordFinEquiv g (X.displacement e).2).isLt)
  refine ⟨?_,ds.1⟩
  have hx (u v : Word bits) : (BinaryOp.bitXor.eval u v).val = u.val ^^^ v.val :=
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow u.isLt v.isLt)
  have ht := (bundleOrder g base (bundleTarget X ((x,l),j))).isLt.trans_le fit
  rw [bundleTarget_apply, bundleOrder_val, bitWordFinEquiv_add_val] at ht ⊢
  rw [targetWord, Fin.val_add, Fin.val_mul, he, rep.target, hx, hs.2, ds.2, rep.lanes,
    Nat.mod_add_mod, Nat.mod_eq_of_lt ht]

/-- The two base columns have one entry per old base arc. Each output column has
one entry per bundle. Only overlaps involving a write need to be ruled out. -/
structure Layout (p : Fin 8 → Word bits) (n lanes : ℕ) : Prop where
  fits : n * lanes ≤ 2^bits
  apart : ∀ (t u : Fin 8) (x i : Word bits), 1 ≤ t.val → t.val ≤ 5 → 2 ≤ u.val → u.val ≤ 4 →
    x.val < (if t = 1 ∨ t = 5 then n else n * lanes) → i.val < n * lanes →
    ((p t + x).val = (p u + i).val ↔ t = u ∧ x = i)

/-- Equal-capacity regions in the existing refresh layout satisfy the weaker
bounds for the two read-only base tables. -/
theorem Layout.ofRegions (h : RefreshRAM.Regions p (n * 2^g)) : Layout p n (2^g) := by
  refine ⟨h.fits, fun t u x i ht _ hu _ hx hi => ?_⟩
  apply h.apart t u (by rintro rfl; simp at ht) (by rintro rfl; simp at hu) x i _ hi
  split at hx
  · exact hx.trans_le (Nat.le_mul_of_pos_right n (Nat.two_pow_pos g))
  · exact hx

/-- Addresses outside the output columns through a given cursor. -/
def Outside (k addr : ℕ) : Prop :=
  ∀ i : Word bits, i.val < k →
    addr ≠ (p 2 + i).val ∧ addr ≠ (p 3 + i).val ∧ addr ≠ (p 4 + i).val

/-- The constructed rows through the cursor, together with the surviving base tables. -/
structure Prefix (m : Memory bits) (k : ℕ) : Prop where
  inputs : BaseTables X base p m
  rows : ∀ b, (bundleOrder g base b).val < k →
    let i : Word bits := Fin.ofNat _ (bundleOrder g base b).val
    (cell p m 2 i).val = (bundleOrder g base (bundleTarget X b)).val ∧
      (cell p m 3 i).val = (bitWordFinEquiv a (X.displacement (b.1.1,b.2)).1).val ∧ cell p m 4 i = 0

private theorem cell_update {lanes : ℕ} (layout : Layout p n lanes) (m : Memory bits)
    (i : Word bits) (hi : i.val < n * lanes) (t : Fin 8) (x : Word bits)
    (ht₁ : 1 ≤ t.val) (ht₅ : t.val ≤ 5) (hx : x.val < (if t = 1 ∨ t = 5 then n else n * lanes)) :
    cell p (update p m i) t x =
      if t = 4 ∧ x = i then 0 else if t = 3 ∧ x = i then portShift p m i
      else if t = 2 ∧ x = i then targetWord p m i else cell p m t x := by
  simp only [update, cell, RefreshRAM.cell, writeMemory,
    layout.apart t 4 x i ht₁ ht₅ (by decide) (by decide) hx hi,
    layout.apart t 3 x i ht₁ ht₅ (by decide) (by decide) hx hi,
    layout.apart t 2 x i ht₁ ht₅ (by decide) (by decide) hx hi]

private theorem step (layout : Layout p n (2^g)) (m : Memory bits) (i : Word bits)
    (hi : i.val < n * 2^g) (cur : Prefix X base p m i.val) :
    Prefix X base p (update p m i) (i.val+1) := by
  have cellEq := cell_update p layout m i hi
  have hbase (e : V × Fin (2^a)) : (Fin.ofNat (2^bits) (base e).val).val < n :=
    (Nat.mod_le ..).trans_lt (base e).isLt
  constructor
  · refine ⟨cur.inputs.lanes, fun e => ?_, fun e => ?_⟩
    · rw [cellEq 1 _ (by decide) (by decide) (by simpa using hbase e)]
      simpa using cur.inputs.target e
    · rw [cellEq 5 _ (by decide) (by decide) (by simpa using hbase e)]
      simpa using cur.inputs.displacement e
  · intro b hb
    let j := Fin.ofNat (2^bits) (bundleOrder g base b).val
    have hj : j.val = (bundleOrder g base b).val := Nat.mod_eq_of_lt ((bundleOrder g base b).isLt.trans_le layout.fits)
    have hjn : j.val < n * 2^g := hj ▸ (bundleOrder g base b).isLt
    change (cell p _ 2 j).val = _ ∧ (cell p _ 3 j).val = _ ∧ cell p _ 4 j = 0
    rw [cellEq 2 j (by decide) (by decide) (by simpa using hjn),
        cellEq 3 j (by decide) (by decide) (by simpa using hjn),
        cellEq 4 j (by decide) (by decide) (by simpa using hjn)]
    by_cases hji : j = i
    · have correct := translated_row X base p m cur.inputs layout.fits b i (hji ▸ hj)
      simpa [hji] using correct
    · have hne : j.val ≠ i.val := Fin.val_ne_of_ne hji
      simp [hji]; exact cur.rows b (by omega)

/-- The native scan from an arbitrary prefix extends that prefix by its call count.
Memory outside the output rows through the final cursor keeps its incoming value. -/
theorem scan_run (layout : Layout p n (2^g)) (m : Memory bits) (k calls : ℕ)
    (cur : Prefix X base p m k) (room : k + calls ≤ n * 2^g) :
    let M := (template visit 0).instantiate bits p
    ∃ rs, runSegment M.program 28 (some (Fin.ofNat (2^bits) k)) m (List.replicate calls []) = some rs ∧
      Prefix X base p (after m (eventLog rs)) (k + calls) ∧
      (∀ z, Outside p (k + calls) z → after m (eventLog rs) z = m z) ∧
      rs.length = calls ∧ ∀ r ∈ rs, r.events.length = 27 ∧ countProbes r.events = 5 := by
  let M := (template visit 0).instantiate bits p
  induction calls generalizing m k with
  | zero => exact ⟨[], rfl, cur, fun _ _ => rfl, rfl, by simp⟩
  | succ s ih =>
    let i := Fin.ofNat (2^bits) k
    have hv : i.val = k := Nat.mod_eq_of_lt (by have := layout.fits; omega)
    have hi : i.val < n * 2^g := by omega
    have next := step X base p layout m i hi (hv ▸ cur)
    have hnext : i + 1 = Fin.ofNat (2^bits) (k+1) := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one', hv, Nat.add_mod_mod]
      rfl
    let r : Report bits := ⟨events p m i, some (i+1)⟩
    obtain ⟨rs,run,rows,frame,hl,hw⟩ := ih (update p m i) (k+1) (hv ▸ next) (by omega)
    have hm : after m (eventLog (r :: rs)) = after (update p m i) (eventLog rs) := by
      change List.foldl BurstRAM.update m (events p m i ++ eventLog rs) = _
      rw [List.foldl_append]; rfl
    refine ⟨r :: rs, ?_, ?_, ?_, by simp [hl], ?_⟩
    · change runSegment M.program 28 (some i) m (List.replicate (s+1) []) = _
      rw [List.replicate_succ, runSegment, visit_native p m i]
      simp only [M, r, events_after, hnext, run, Option.map_some]
    · simpa [hm, Nat.add_assoc, Nat.add_comm 1 s] using rows
    · intro z hz
      rw [hm, frame z (by simpa only [Nat.add_assoc, Nat.add_comm 1 s] using hz)]
      obtain ⟨h₂,h₃,h₄⟩ := hz i (by omega)
      simp [update, writeMemory, h₂, h₃, h₄]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact events_work p m i
      · exact hw q hq

private theorem pass_cost {rs : List (Report bits)} (hw : ∀ r ∈ rs, countProbes r.events = 5) :
    RAMBuckets.cost (fun r : Report bits => countProbes r.events) rs = 6 * rs.length := by
  induction rs with
  | nil => simp [RAMBuckets.cost]
  | cons r rs ih =>
    rw [RAMBuckets.cost, hw r (List.mem_cons_self ..), ih (fun q h => hw q (List.mem_cons_of_mem _ h)),
      List.length_cons, Nat.mul_succ]
    omega

/-- Complete directory initialization from the old base slot tables. It costs six calls
plus probes per bundle and writes only the target, shift and total arrays. -/
theorem directory_pass (layout : Layout p n (2^g)) (m : Memory bits) (old : BaseTables X base p m) :
    let M := (template visit 0).instantiate bits p
    ∃ rs, runSegment M.program 28 (some 0) m (List.replicate (n * 2^g) []) = some rs ∧
      Prefix X base p (after m (eventLog rs)) (n * 2^g) ∧
      (∀ z, Outside p (n * 2^g) z → after m (eventLog rs) z = m z) ∧
      RAMBuckets.cost (fun r : Report bits => countProbes r.events) rs = 6 * (n * 2^g) ∧
      rs.length = n * 2^g ∧ ∀ r ∈ rs, r.events.length = 27 ∧ countProbes r.events = 5 := by
  have init : Prefix X base p m 0 := ⟨old, fun b h => ((bundleOrder g base b).val.not_lt_zero h).elim⟩
  obtain ⟨rs,run,rows,frame,hl,hw⟩ := scan_run X base p layout m 0 (n * 2^g) init (by simp)
  exact ⟨rs,run,by simpa using rows,by simpa using frame,
    (pass_cost (fun r h => (hw r h).2)).trans (by rw [hl]),hl,hw⟩

/-- Every bundle read by a live source segment is inside the constructed directory. -/
theorem liveBundle_lt (q : Fin 8 → Word bits) (hd : (q 0).val = 2^a) {b : Word bits}
    (live : RefreshRAM.LiveBundle q (n * 2^g * 2^a) b) : b.val < n * 2^g := by
  obtain ⟨i,hi,rfl⟩ := live
  change (i.val / (q 0).val) % (2^bits) < n * 2^g
  exact (Nat.mod_le ..).trans_lt (hd ▸ (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos a)).mpr hi)

/-- The constructed directory and gathered widths give exactly the initial state of the
external segment scan. Only totals at live bundle numbers need initialization. -/
theorem Prefix.external_start (q : Fin 8 → Word bits) (m : Memory bits)
    (w : (V × Fin (2^a)) × (BitWord a × BitWord g) → ℕ)
    (done : Prefix X base p m (n * 2^g)) (hd : (q 0).val = 2^a)
    (targetBase : q 2 = p 2) (shiftBase : q 3 = p 3) (totalBase : q 4 = p 4)
    (old : ∀ i : Word bits, i.val < n * 2^g * 2^a →
      cell q m 1 i = (graphInput X (bundleOrder g base) w).width i) :
    RefreshRAM.AtCursor q (n * 2^g * 2^a) (graphInput X (bundleOrder g base) w) m 0 := by
  let ord := bundleOrder g base
  have rows (i : Word bits) (live : RefreshRAM.LiveBundle q (n * 2^g * 2^a) i) :
      cell q m 2 i = (graphInput X ord w).target i ∧
        cell q m 3 i = (graphInput X ord w).shift i ∧ cell q m 4 i = 0 := by
    have hi := liveBundle_lt q hd live
    let b := ord.symm ⟨i.val,hi⟩
    have hid : (ord b).val = i.val := congrArg Fin.val (ord.apply_symm_apply ⟨i.val,hi⟩)
    have hiw : Fin.ofNat (2^bits) (ord b).val = i := by rw [hid]; exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
    obtain ⟨target, shift, total⟩ := done.rows b (ord b).isLt
    change (cell p m 2 (Fin.ofNat _ (ord b).val)).val = (ord (bundleTarget X b)).val at target
    change (cell p m 3 (Fin.ofNat _ (ord b).val)).val = _ at shift
    change cell p m 4 (Fin.ofNat _ (ord b).val) = 0 at total
    rw [hiw] at target shift total
    change m (q 2+i).val = _ ∧ m (q 3+i).val = _ ∧ m (q 4+i).val = 0
    rw [targetBase, shiftBase, totalBase]
    simp only [graphInput, dite_eq_left hi]
    exact ⟨Fin.ext (target.trans ((Nat.mod_eq_of_lt (target ▸ (cell p m 2 i).isLt)).symm)),
      Fin.ext (shift.trans ((Nat.mod_eq_of_lt (shift ▸ (cell p m 3 i).isLt)).symm)), total⟩
  exact RefreshRAM.AtCursor.start old (fun i live => (rows i live).1) (fun i live => (rows i live).2.1)
    (fun i live => (rows i live).2.2)

end BundleDirectory
end CompressorRecords.PortRefresh

end VPVNP
end Computability
end OAI
