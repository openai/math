import OAI.Computability.VPVNP.CompressorDescriptorSpace
import OAI.Computability.VPVNP.CompressorRecordRefreshAllocation
import OAI.Computability.VPVNP.CompressorRecordsSchedule
import OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe
import OAI.Computability.VPVNP.LiveAuxiliaryHeaders

/-!
# Copying the six incidence columns into the next level

The worker copies one external word per call. Each column starts at cursor zero
and stops after its populated rows. The three base columns therefore copy only
base ports, even when the actual columns have many more lane positions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.CopyIncidence

open BurstRAM BurstRAM.PrivateRAM Compression PrimedStackRAM PhaseRecipe
open scoped Fin.CommRing

variable {w a l : ℕ}

/-- The scheduled worker that copies one external incidence word per call. -/
abbrev copyPass : Schedule.Pass := ⟨_,_,_,template LiveAuxiliaryHeaders.copyWord 7⟩

/-- The copy worker's public bank, containing zero followed by the source and destination
column bases. -/
def copyPublic (src dst : Word w) : Fin 3 → Word w := ![0, src, dst]

/-- Schedule a tagged column copy from cursor zero to the supplied stop using the source and
destination address expressions. -/
def copyPhase {g : ℕ} (hg : 3 ≤ g) (tag : ℕ) (stop src dst : Expr) : Phase g :=
  Phase.ofParams hg tag (.lit 0) stop ![.lit 0, src, dst]

/-- The copy cursor adds a word offset to each array head. -/
def cell (base : Word w) (j : ℕ) : ℕ := (base + (j : Word w)).val

private abbrev program (src dst : Word w) := (copyPass.table.instantiate w (copyPublic src dst)).program

/-- The report returned by the native one-word copy. -/
def row (src dst : Word w) (j : ℕ) (m : Memory w) : Report w :=
  (execute (program src dst) 12 ((program src dst).start (j : Word w)) m []).getD ⟨[],none⟩

private theorem row_spec (src dst : Word w) (j : ℕ) (m : Memory w) :
    let r := row src dst j m
    execute (program src dst) 12 ((program src dst).start (j : Word w)) m [] = some r ∧
    r.result = some ((j+1 : ℕ) : Word w) ∧
    after m r.events = writeMemory m (dst+(j : Word w)) (m (cell src j)) ∧
    r.events.length = 11 ∧ r.probes = 2 ∧ choiceBits r.events = [] := by
  obtain ⟨es,he,hm,hlen,hprobes,hchoices⟩ :=
    LiveAuxiliaryHeaders.copyWord_native (copyPublic src dst) (j : Word w) m
  change execute (program src dst) 12 ((program src dst).start (j : Word w)) m [] = _ at he
  have hrow : row src dst j m = ⟨es,some ((j : Word w)+1)⟩ := by
    unfold row
    rw [he]
    rfl
  dsimp only
  rw [hrow]
  refine ⟨he,by simp,?_,hlen,hprobes,hchoices⟩
  simpa [copyPublic,cell] using hm

/-- Chronological reports of one column, beginning at an arbitrary row. -/
def scan (src dst : Word w) : ℕ → ℕ → Memory w → List (Report w)
  | _, 0, _ => []
  | k, n+1, m =>
    let r := row src dst k m
    r :: scan src dst (k+1) n (after m r.events)

private theorem scan_after (src dst : Word w) (k n : ℕ) (m : Memory w) :
    after m (eventLog (scan src dst k (n+1) m)) =
      after (after m (row src dst k m).events)
        (eventLog (scan src dst (k+1) n (after m (row src dst k m).events))) :=
  List.foldl_append

/-- Twelve units of private fuel suffice. Each call has eleven events,
two probes and no branch choices. Its charge includes one unit for the call. -/
theorem scan_native (src dst : Word w) (k n : ℕ) (m : Memory w) :
    let P := (copyPass.table.instantiate w (copyPublic src dst)).program
    let rs := scan src dst k n m
    runSegment P 12 (some (k : Word w)) m (List.replicate n []) = some rs ∧
    endState (some (k : Word w)) rs = some ((k+n : ℕ) : Word w) ∧
    rs.length = n ∧ (∀ r ∈ rs, r.events.length = 11 ∧ r.probes = 2 ∧ choiceBits r.events = []) ∧
    RAMBuckets.cost Report.probes rs = 3*n := by
  induction n generalizing k m with
  | zero => exact ⟨rfl,rfl,rfl,by simp [scan],rfl⟩
  | succ n ih =>
    let r := row src dst k m
    obtain ⟨he,hs,_,work⟩ := row_spec src dst k m
    obtain ⟨hr,hend,hl,hw,hc⟩ := ih (k+1) (after m r.events)
    dsimp only
    refine ⟨?_,?_,?_,?_,?_⟩
    · rw [List.replicate_succ,runSegment,he]
      change (runSegment (program src dst) 12 r.result _ _).map (r :: ·) = _
      rw [show r.result = _ from hs,hr]; rfl
    · change endState r.result _ = _
      rw [hs,hend,show k+1+n = k+(n+1) by omega]
    · exact congrArg Nat.succ hl
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | h
      · exact work
      · exact hw _ h
    · change 1+r.probes+RAMBuckets.cost _ _ = _
      rw [hc,show r.probes = 2 from work.2.1]; omega

theorem scan_outside (src dst : Word w) (k n : ℕ) (m : Memory w) (addr : ℕ)
    (away : ∀ j, k ≤ j → j < k+n → addr ≠ cell dst j) :
    after m (eventLog (scan src dst k n m)) addr = m addr := by
  induction n generalizing k m with
  | zero => rfl
  | succ n ih =>
    rw [scan_after, ih _ _ (fun j hj h ↦ away j (by omega) (by omega)), (row_spec ..).2.2.1]
    exact ite_eq_right (away k le_rfl (by omega))

private theorem cell_inj (base : Word w) {i j : ℕ} (hi : i < 2^w) (hj : j < 2^w)
    (eqn : cell base i = cell base j) : i = j := by
  have h : (i : Word w) = (j : Word w) := add_left_cancel (Fin.ext eqn : base+(i : Word w) = base+(j : Word w))
  have v : i % (2^w) = j % (2^w) := congrArg Fin.val h
  simpa only [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using v

theorem scan_read (src dst : Word w) (k n : ℕ) (m : Memory w) (fit : k+n ≤ 2^w)
    (apart : ∀ i j, k ≤ i → i < k+n → k ≤ j → j < k+n → cell src i ≠ cell dst j)
    (i : ℕ) (lo : k ≤ i) (hi : i < k+n) :
    after m (eventLog (scan src dst k n m)) (cell dst i) = m (cell src i) := by
  induction n generalizing k m with
  | zero => omega
  | succ n ih =>
    rw [scan_after]
    by_cases e : i = k
    · subst i
      rw [scan_outside _ _ _ _ _ _ (fun j hj h eqn ↦ by
        have := cell_inj dst (by omega) (by omega) eqn
        omega), (row_spec ..).2.2.1]
      exact ite_eq_left rfl
    · rw [ih _ _ (by omega) (fun i j hi hi' hj hj' ↦ apart i j (by omega) (by omega) (by omega) (by omega))
        (by omega) (by omega), (row_spec ..).2.2.1]
      exact ite_eq_right (apart i k lo hi le_rfl (by omega))


/-- If the destination rows avoid the tag and active frame, every call
retains the dispatch parameters and satisfies the exclusive cursor guard. -/
theorem scan_valid {d : ℕ} (C : Schedule.Catalog d) (worker : Fin d) (ports : Schedule.Ports w)
    (pub : Fin (C worker).params → Word w) (bound src dst : Word w) (k n : ℕ) (m : Memory w)
    (stop : k+n = bound.val) (ready : Schedule.Ready C worker ports pub bound m)
    (away : ∀ j, k ≤ j → j < k+n → cell dst j ≠ ports.tag.val ∧
      ∀ i : Fin ((C worker).params+1), cell dst j ≠ cell ports.activeFrame i.val) :
    Schedule.ValidTrace C worker ports pub bound (k : Word w) m (scan src dst k n m) := by
  induction n generalizing k m with
  | zero =>
    have h : (k : Word w) = bound := Fin.ext (by
      change k % (2^w) = bound.val
      simp only [Nat.add_zero] at stop
      rw [stop,Nat.mod_eq_of_lt bound.isLt])
    exact ⟨ready,h.ge⟩
  | succ n ih =>
    have hk : k < bound.val := by omega
    have hlt : (k : Word w) < bound := by
      change k % (2^w) < bound.val
      rwa [Nat.mod_eq_of_lt (hk.trans bound.isLt)]
    have safe := away k le_rfl (by omega)
    have keep (v : ℕ) (h : cell dst k ≠ v) :
        after m (row src dst k m).events v = m v := by
      rw [(row_spec ..).2.2.1]
      exact ite_eq_right h.symm
    refine ⟨ready,hlt,((k+1 : ℕ) : Word w),(row_spec ..).2.1,ih _ _ (by omega) ?_ ?_⟩
    · refine ⟨(keep _ safe.1).trans ready.1,?_,?_⟩
      · exact (keep _ (by simpa [cell] using safe.2 0)).trans ready.2.1
      · funext i
        exact (keep _ (safe.2 i.succ)).trans (congrFun ready.2.2 i)
    · exact fun j hj h ↦ away j (by omega) (by omega)

/-- The populated length of an incidence column, counting base ports for the first three
columns and actual ports for the other three. -/
def rows (X : State a l) (c : Fin 6) : ℕ :=
  if c.val < 3 then Fintype.card X.Base * 2^a else X.positions * 2^a

/-- Only live cells of the six arrays participate in the separation hypotheses.
The source may lie on either side of any destination column. -/
structure Regions (X : State a l) (T U : IncidenceDirectory w) : Prop where
  fits : ∀ c, rows X c ≤ 2^w
  source : ∀ c d i j, i < rows X c → j < rows X d → cell (T.column c) i ≠ cell (U.column d) j
  destination : ∀ c d i j, c ≠ d → i < rows X c → j < rows X d →
    cell (U.column c) i ≠ cell (U.column d) j

private theorem cell_val (base : Word w) {n j : ℕ} (room : base.val+n ≤ 2^w) (hj : j < n) :
    cell base j = base.val+j := by
  have hv : (j : Word w).val = j := Nat.mod_eq_of_lt (by omega)
  rw [cell,Fin.val_add,hv,Nat.mod_eq_of_lt (by omega)]

/-- Natural disjoint half-open intervals give the word-address conditions,
including at the largest address representable by a machine word. -/
theorem Regions.of_intervals (X : State a l) (T U : IncidenceDirectory w)
    (roomT : ∀ c, (T.column c).val + rows X c ≤ 2^w)
    (roomU : ∀ c, (U.column c).val + rows X c ≤ 2^w)
    (apart : ∀ c d, (T.column c).val + rows X c ≤ (U.column d).val ∨
      (U.column d).val + rows X d ≤ (T.column c).val)
    (distinct : ∀ c d, c ≠ d → (U.column c).val + rows X c ≤ (U.column d).val ∨
      (U.column d).val + rows X d ≤ (U.column c).val) : Regions X T U := by
  constructor
  · intro c; have := roomU c; omega
  · intro c d i j hi hj
    rw [cell_val _ (roomT c) hi,cell_val _ (roomU d) hj]
    have := apart c d
    omega
  · intro c d i j hcd hi hj
    rw [cell_val _ (roomU c) hi,cell_val _ (roomU d) hj]
    have := distinct c d hcd
    omega

private theorem actual_rows (X : State a l) :
    X.positions * 2^a = Fintype.card X.Base * 2^l * 2^a := by
  rw [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv l),Fintype.card_fin]

theorem rows_le_slots (X : State a l) (c : Fin 6) : rows X c ≤ X.positions * 2^a := by
  unfold rows
  split
  · rw [actual_rows]
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos l))
  · exact le_rfl

/-- The native degree-refresh output can occupy either side of the canonical
level directory. Each column has room for the new state's actual slots,
and the copy scan uses the shorter base-port count in its first three columns. -/
theorem Regions.refresh_to_level (X : State a l) (P : PortRefresh.Allocation.Plan)
    (L : DescriptorSpace.Layout) (level : Fin L.levels)
    (scratchRoom : P.stop ≤ 2^w) (levelRoom : DescriptorSpace.endAddress L < 2^w)
    (scratchCapacity : X.positions * 2^a ≤ P.capacity)
    (levelCapacity : X.positions * 2^a ≤ DescriptorSpace.slotCapacity L)
    (apart : P.stop ≤ DescriptorSpace.incidenceStart L level ∨
      DescriptorSpace.incidenceStart L level + 6*(X.positions * 2^a) ≤ P.next) :
    Regions X (P.output w) (DescriptorSpace.packedIncidence L w level (X.positions * 2^a)) := by
  let n := X.positions * 2^a
  let start := DescriptorSpace.incidenceStart L level
  let U := DescriptorSpace.packedIncidence L w level n
  have room : start + 6*n < 2^w := DescriptorSpace.packed_incidence_room L levelRoom level levelCapacity
  have fit : n ≤ 2^w := by omega
  have layout : U.Layout X := by
    change (DescriptorSpace.packedIncidence L w level (X.positions * 2^a)).Layout X
    rw [actual_rows]
    exact DescriptorSpace.packed_layout L X level levelRoom (by rwa [← actual_rows])
  have dest (c : Fin 6) (j : ℕ) (hj : j < n) :
      start ≤ cell (U.column c) j ∧ cell (U.column c) j < start + 6*n := by
    have hc := Nat.mul_le_mul_right n c.isLt
    rw [Nat.succ_mul] at hc
    have hbase : (U.column c).val = start + c.val*n := by
      rw [show U = DescriptorSpace.packedIncidence L w level n from rfl,DescriptorSpace.packed_column]
      exact Nat.mod_eq_of_lt (by change start+c.val*n < _; omega)
    rw [cell_val _ (by rw [hbase]; omega : (U.column c).val+n ≤ 2^w) hj,hbase]
    constructor <;> omega
  refine ⟨fun c ↦ (rows_le_slots X c).trans fit,?_,?_⟩
  · intro c d i j hi hj
    have hi' : i < n := hi.trans_le (rows_le_slots X c)
    have hj' : j < n := hj.trans_le (rows_le_slots X d)
    have hw : (i : Word w).val = i := Nat.mod_eq_of_lt (hi'.trans_le fit)
    have hs := P.column_interval scratchRoom c (i : Word w) (by rw [hw]; exact hi'.trans_le scratchCapacity)
    have hd := dest d j hj'
    change P.next ≤ cell ((P.output w).column c) i ∧ cell ((P.output w).column c) i < P.stop at hs
    change P.stop ≤ start ∨ start + 6*n ≤ P.next at apart
    change cell ((P.output w).column c) i ≠ cell (U.column d) j
    omega
  · intro c d i j hcd hi hj eqn
    have slot (t : Fin 6) (k : ℕ) (hk : k < rows X t) : (k : Word w).val < Fintype.card X.Base * 2^l * 2^a := by
      have h : k < n := hk.trans_le (rows_le_slots X t)
      rw [← actual_rows]
      exact (Nat.mod_le ..).trans_lt h
    exact hcd (((layout.apart c d (i : Word w) (j : Word w) (slot c i hi) (slot d j hj)).mp eqn).1)

variable (X : State a l) (T U : IncidenceDirectory w)

/-- The complete copy scan for one incidence column between the source and destination level
directories. -/
def columnScan (c : Fin 6) (m : Memory w) :=
  scan (T.column c) (U.column c) 0 (rows X c) m

/-- Execute each column in sequence, feeding its actual final memory to
the next worker. Each column has a fresh zero cursor and public operands. -/
def reports : List (Fin 6) → Memory w → List (Report w)
  | [], _ => []
  | c :: cs, m =>
    let rs := columnScan X T U c m
    rs ++ reports cs (after m (eventLog rs))

private theorem reports_after (c : Fin 6) (cs : List (Fin 6)) (m : Memory w) :
    let out := after m (eventLog (columnScan X T U c m))
    after m (eventLog (reports X T U (c::cs) m)) = after out (eventLog (reports X T U cs out)) := by
  simp only [reports,eventLog,List.flatMap_append,after,List.foldl_append]

/-- Each worker call sequence runs with its own two column heads. -/
inductive Runs : List (Fin 6) → Memory w → List (Report w) → Prop
  | nil (m) : Runs [] m []
  | cons (c : Fin 6) {cs m rs more}
      (native : runSegment (program (T.column c) (U.column c)) 12 (some 0) m
        (List.replicate (rows X c) []) = some rs)
      (next : Runs cs (after m (eventLog rs)) more) : Runs (c::cs) m (rs++more)

theorem reports_run (cs : List (Fin 6)) (m : Memory w) :
    Runs X T U cs m (reports X T U cs m) := by
  induction cs generalizing m with
  | nil => exact .nil m
  | cons c cs ih =>
    exact .cons c (scan_native (T.column c) (U.column c) 0 (rows X c) m).1 (ih _)

theorem reports_outside (cs : List (Fin 6)) (m : Memory w) (v : ℕ)
    (away : ∀ c ∈ cs, ∀ j, j < rows X c → v ≠ cell (U.column c) j) :
    after m (eventLog (reports X T U cs m)) v = m v := by
  induction cs generalizing m with
  | nil => rfl
  | cons c cs ih =>
    rw [reports_after,ih _ (fun d hd ↦ away d (.tail _ hd))]
    exact scan_outside _ _ _ _ _ _ (fun j _ hj ↦ away c (.head _) j (by simpa using hj))

theorem reports_read (reg : Regions X T U) (cs : List (Fin 6)) (m : Memory w)
    (c : Fin 6) (hc : c ∈ cs) (j : ℕ) (hj : j < rows X c) :
    after m (eventLog (reports X T U cs m)) (cell (U.column c) j) = m (cell (T.column c) j) := by
  induction cs generalizing m with
  | nil => simp at hc
  | cons d ds ih =>
    rw [reports_after]
    by_cases h : c ∈ ds
    · rw [ih _ h]
      exact scan_outside _ _ _ _ _ _ (fun i _ hi ↦ reg.source c d j i hj (by simpa using hi))
    · have he : c = d := (List.mem_cons.mp hc).resolve_right h
      subst d
      rw [reports_outside X T U ds _ _ (fun d hd i hi ↦ reg.destination c d j i
        (fun e ↦ h (e ▸ hd)) hj hi)]
      exact scan_read _ _ _ _ _ (by simpa using reg.fits c)
        (fun i t _ hi _ ht ↦ reg.source c c i t (by simpa using hi) (by simpa using ht)) j
        (Nat.zero_le j) (by simpa using hj)

theorem reports_work (cs : List (Fin 6)) (m : Memory w) :
    let rs := reports X T U cs m
    rs.length = (cs.map (rows X)).sum ∧ RAMBuckets.cost Report.probes rs = 3*(cs.map (rows X)).sum ∧
    ∀ r ∈ rs, r.events.length = 11 ∧ r.probes = 2 ∧ choiceBits r.events = [] := by
  induction cs generalizing m with
  | nil => exact ⟨rfl,rfl,by simp [reports]⟩
  | cons c cs ih =>
    let rs := columnScan X T U c m
    obtain ⟨_,_,hl,hw,hcost⟩ := scan_native (T.column c) (U.column c) 0 (rows X c) m
    obtain ⟨ht,hct,hwt⟩ := ih (after m (eventLog rs))
    dsimp only
    simp only [reports,List.map_cons,List.sum_cons,List.length_append,RAMBuckets.cost_append,List.mem_append]
    exact ⟨congrArg₂ (·+·) hl ht, (congrArg₂ (·+·) hcost hct).trans (Nat.mul_add ..).symm,
      fun r h ↦ h.elim (hw r) (hwt r)⟩

/-- The six column indices in the order used to copy the full incidence directory. -/
def allColumns : List (Fin 6) := [0,1,2,3,4,5]

private theorem mem_allColumns (c : Fin 6) : c ∈ allColumns := by fin_cases c <;> decide

private theorem full_count : (allColumns.map (rows X)).sum =
    3*(Fintype.card X.Base * 2^a) + 3*(X.positions * 2^a) := by
  change _ + (_ + (_ + (_ + (_ + (_ + 0))))) = _
  dsimp [allColumns,rows]
  omega

/-- The scratch incidence state is transferred in six actual native segments.
All populated destination cells represent the same graph, including inverse
ports, displacements and widths. The charge is three units per copied cell. -/
theorem copy_directory (m : Memory w) (reg : Regions X T U) (rep : T.Represents X m) :
    let rs := reports X T U allColumns m
    let out := after m (eventLog rs)
    let N := 3*(Fintype.card X.Base * 2^a) + 3*(X.positions * 2^a)
    Runs X T U allColumns m rs ∧ U.Represents X out ∧ rs.length = N ∧
    RAMBuckets.cost Report.probes rs = 3*N ∧
    (∀ r ∈ rs, r.events.length = 11 ∧ r.probes = 2 ∧ choiceBits r.events = []) ∧
    ∀ v, (∀ c j, j < rows X c → v ≠ cell (U.column c) j) → out v = m v := by
  intro rs out N
  have readback (c : Fin 6) (j : ℕ) (hj : j < rows X c) :=
    reports_read X T U reg allColumns m c (mem_allColumns c) j hj
  have base (c : Fin 6) (hc : c.val < 3) (e : X.Base × Fin (2^a)) :
      out (U.column c + IncidenceDirectory.basePort X e).val =
      m (T.column c + IncidenceDirectory.basePort X e).val := by
    rw [IncidenceDirectory.basePort_number]
    exact readback c _ (by simp only [rows,ite_eq_left hc]; exact (IncidenceDirectory.baseOrder X e).isLt)
  have actual (c : Fin 6) (hc : 3 ≤ c.val) (e : (X.Base × BitWord l) × Fin (2^a)) :
      out (U.column c + IncidenceDirectory.actualPort X e).val =
      m (T.column c + IncidenceDirectory.actualPort X e).val := by
    rw [IncidenceDirectory.actualPort_number]
    apply readback
    rw [rows,ite_eq_right (Nat.not_lt.mpr hc),State.positions,Fintype.card_prod,
      Fintype.card_congr (bitWordFinEquiv l),Fintype.card_fin]
    exact (IncidenceDirectory.actualOrder X e).isLt
  have hrep : U.Represents X out := ⟨fun e ↦ (base 0 (by decide) e).trans (rep.baseOut e),
    fun e ↦ (base 1 (by decide) e).trans (rep.baseIn e),
    fun e ↦ (base 2 (by decide) e).trans (rep.shift e),
    fun e ↦ (actual 3 (by decide) e).trans (rep.actualOut e),
    fun e ↦ (actual 4 (by decide) e).trans (rep.actualIn e),
    fun e ↦ (actual 5 (by decide) e).trans (rep.width e)⟩
  obtain ⟨hlen,hcost,hwork⟩ := reports_work X T U allColumns m
  rw [full_count] at hlen hcost
  exact ⟨reports_run ..,hrep,hlen,hcost,hwork,fun v hv ↦ reports_outside X T U allColumns m v (fun c _ ↦ hv c)⟩

end CompressorRecords.CopyIncidence

end VPVNP
end Computability
end OAI
