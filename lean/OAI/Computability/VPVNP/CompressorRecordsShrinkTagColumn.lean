import OAI.Computability.VPVNP.CompressorRecordIncidenceLayout
import OAI.Computability.VPVNP.CompressorRecordsOrdinalFootprint
import OAI.Computability.VPVNP.RAMChoicePrefix
import OAI.Computability.VPVNP.CompressorRecordsShrink

/-!
# Extracting the shrinking tag increments from the displacement column

Before the greedy tag scan, each base port contributes the tag component of its
old displacement. The worker skips the residual lane bits by division, takes
the low tag bits, and writes a separate column in base-port order. A final call
initializes the zero operand used for absent increments.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkTagColumn

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression
open scoped Fin.CommRing

variable {w a g : ℕ}

/-- Both workers use the same frame throughout the two phases. -/
def publicWords (src dst zero divisor modulus : Word w) : Fin 5 → Word w :=
  ![src, dst, zero, divisor, modulus]

/-- Build the workers' shared parameters from the incidence displacement column, tag
destination, zero cell, residual-lane radix and tag radix. -/
def params (T : IncidenceDirectory w) (a g : ℕ) (dst zero : Word w) : Fin 5 → Word w :=
  publicWords T.shift dst zero (CursorRAM.encode w (2^g)) (CursorRAM.encode w (2^(Shrink.J a)))

/-- Read one base port's displacement, divide out its residual lane, write the remaining low
tag bits, and advance the port cursor. -/
def extractOps : List (Op 4 5) :=
  [.stateWord 0, .publicWord 1 0, .binary .add 1 1 0, .read 2 1,
   .publicWord 3 3, .binary .div 2 2 3, .publicWord 3 4, .binary .mod 2 2 3,
   .publicWord 1 1, .binary .add 1 1 0, .write 1 2, .constant 3 1, .binary .add 0 0 3]

/-- Write zero to the operand cell used for absent tag increments and set the return cursor to
one. -/
def zeroOps : List (Op 4 5) :=
  [.publicWord 1 2, .constant 2 0, .write 1 2, .constant 0 1]

/-- The scheduled worker that extracts one tag increment from the displacement column per call. -/
abbrev extractPass : Schedule.Pass := ⟨_, _, _, template extractOps 0⟩
/-- The scheduled worker that initializes the absent-increment operand after the tag extraction
scan. -/
abbrev zeroPass : Schedule.Pass := ⟨_, _, _, template zeroOps 0⟩

/-- Natural address of an indexed column entry, obtained by adding its index to the base in
word arithmetic. -/
def cell (base : Word w) (i : ℕ) : ℕ := (base + (i : Word w)).val

/-- Recover the displacement's tag component by dividing by the residual radix and reducing
modulo the tag radix. -/
def extract (p : Fin 5 → Word w) (x : Word w) : Word w :=
  BinaryOp.mod.eval (BinaryOp.div.eval x (p 3)) (p 4)

/-- Report for one port visit, recording the displacement read, tag increment write, and next
cursor. -/
def row (p : Fin 5 → Word w) (i : Word w) (m : Memory w) : Report w :=
  let x := m (p 0+i).val
  ⟨[.tick, .tick, .tick, .read (p 0+i) x, .tick, .tick, .tick, .tick, .tick, .tick,
    .write (p 1+i) (extract p x), .tick, .tick], some (i+1)⟩

/-- Report of the final zero-initialization call, with one external write and return cursor
one. -/
def zeroRow (p : Fin 5 → Word w) : Report w :=
  ⟨[.tick, .tick, .write (p 2) 0, .tick], some 1⟩

theorem row_after (p : Fin 5 → Word w) (i : Word w) (m : Memory w) :
    after m (row p i m).events = writeMemory m (p 1+i) (extract p (m (p 0+i).val)) := rfl

theorem zero_after (p : Fin 5 → Word w) (m : Memory w) :
    after m (zeroRow p).events = writeMemory m (p 2) 0 := rfl

theorem row_native (p : Fin 5 → Word w) (i : Word w) (m : Memory w) :
    let P := (extractPass.table.instantiate w p).program
    execute P 14 (P.start i) m [] = some (row p i m) := by
  let M := (template extractOps 0).instantiate w p
  change execute M.program (1+extractOps.length) ⟨M.entry, i, fun _ ↦ 0, fun _ ↦ 0⟩ m [] = _
  rw [execute_template]
  simp (config := {decide := true}) [extractOps, run, Op.run, Op.effect, Function.update, BinaryOp.eval,
    row, extract, Report.prepend]

theorem zero_native (p : Fin 5 → Word w) (i : Word w) (m : Memory w) :
    let P := (zeroPass.table.instantiate w p).program
    execute P 5 (P.start i) m [] = some (zeroRow p) := by
  let M := (template zeroOps 0).instantiate w p
  change execute M.program (1+zeroOps.length) ⟨M.entry, i, fun _ ↦ 0, fun _ ↦ 0⟩ m [] = _
  rw [execute_template]
  simp (config := {decide := true}) [zeroOps, run, Op.run, Op.effect, Function.update, zeroRow,
    Report.prepend]

/-- Reports from the actual, successively updated external memory. -/
def scan (p : Fin 5 → Word w) : ℕ → ℕ → Memory w → List (Report w)
  | _, 0, _ => []
  | i, n+1, m =>
    let r := row p (i : Word w) m
    r :: scan p (i+1) n (after m r.events)

/-- The reports for all base ports in order starting at zero, followed by the report that
initializes the zero operand. -/
def reports (p : Fin 5 → Word w) (B : ℕ) (m : Memory w) := scan p 0 B m ++ [zeroRow p]

theorem scan_native (p : Fin 5 → Word w) (i n : ℕ) (m : Memory w) :
    let P := (extractPass.table.instantiate w p).program
    runSegment P 14 (some (i : Word w)) m (List.replicate n []) = some (scan p i n m) := by
  induction n generalizing i m with
  | zero => rfl
  | succ n ih =>
    dsimp only
    rw [List.replicate_succ, runSegment, row_native]
    change (runSegment _ _ (some ((i : Word w)+1)) _ _).map _ = _
    rw [← Nat.cast_add_one, ih]
    rfl

theorem scan_work (p : Fin 5 → Word w) (i n : ℕ) (m : Memory w) :
    let rs := scan p i n m
    rs.length = n ∧ RAMBuckets.cost Report.probes rs = 3*n ∧
    ∀ r ∈ rs, r.events.length = 13 ∧ r.probes = 2 ∧ choiceBits r.events = [] := by
  induction n generalizing i m with
  | zero => exact ⟨rfl, rfl, by simp [scan]⟩
  | succ n ih =>
    let r := row p (i : Word w) m
    obtain ⟨hl,hc,hw⟩ := ih (i+1) (after m r.events)
    refine ⟨congrArg Nat.succ hl, ?_, ?_⟩
    · change 1+2+RAMBuckets.cost _ _ = _
      rw [hc]; omega
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | ht
      · exact ⟨rfl,rfl,rfl⟩
      · exact hw _ ht

private theorem scan_after (p : Fin 5 → Word w) (i n : ℕ) (m : Memory w) :
    after m (eventLog (scan p i (n+1) m)) =
      after (after m (row p (i : Word w) m).events)
        (eventLog (scan p (i+1) n (after m (row p (i : Word w) m).events))) :=
  List.foldl_append

theorem scan_outside (p : Fin 5 → Word w) (i n : ℕ) (m : Memory w) (v : ℕ)
    (away : ∀ j, i ≤ j → j < i+n → v ≠ cell (p 1) j) :
    after m (eventLog (scan p i n m)) v = m v := by
  induction n generalizing i m with
  | zero => rfl
  | succ n ih =>
    rw [scan_after, ih _ _ (fun j lo hi ↦ away j (by omega) (by omega)), row_after]
    exact ite_eq_right (away i le_rfl (by omega))

/-- The shift columns do not overlap. The final zero cell is distinct from
all populated output rows. -/
structure Regions (p : Fin 5 → Word w) (B : ℕ) : Prop where
  fits : B ≤ 2^w
  source : ∀ i j : ℕ, i < B → j < B → cell (p 0) i ≠ cell (p 1) j
  zero : ∀ i : ℕ, i < B → cell (p 1) i ≠ (p 2).val

private theorem cell_inj (base : Word w) {i j : ℕ} (hi : i < 2^w) (hj : j < 2^w)
    (e : cell base i = cell base j) : i = j := by
  have h : (i : Word w) = (j : Word w) :=
    add_left_cancel (Fin.ext e : base+(i : Word w) = base+(j : Word w))
  have hv : i % (2^w) = j % (2^w) := congrArg Fin.val h
  simpa only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hv

theorem scan_read {p : Fin 5 → Word w} {B : ℕ} (reg : Regions p B)
    (i n : ℕ) (m : Memory w) (bound : i+n ≤ B) (j : ℕ) (lo : i ≤ j) (hi : j < i+n) :
    after m (eventLog (scan p i n m)) (cell (p 1) j) = extract p (m (cell (p 0) j)) := by
  induction n generalizing i m with
  | zero => omega
  | succ n ih =>
    rw [scan_after]
    rcases eq_or_lt_of_le lo with rfl | h
    · rw [scan_outside _ _ _ _ _ (fun k hk hlt eqn ↦ by
        have he := cell_inj (p 1) (by have := reg.fits; omega) (by have := reg.fits; omega) eqn
        omega), row_after]
      exact ite_eq_left rfl
    · rw [ih _ _ (by omega) (by omega) (by omega), row_after]
      exact congrArg (extract p) (ite_eq_right (reg.source j i (by omega) (by omega)))

private theorem after_reports (p : Fin 5 → Word w) (B : ℕ) (m : Memory w) :
    after m (eventLog (reports p B m)) = writeMemory (after m (eventLog (scan p 0 B m))) (p 2) 0 := by
  simp only [reports, eventLog, List.flatMap_append, after, List.foldl_append]
  rfl

/-- Complete native execution, memory contents, and external charge of the two phases. -/
structure Result (p : Fin 5 → Word w) (B : ℕ) (m : Memory w) : Prop where
  extractRun : let P := (extractPass.table.instantiate w p).program
    runSegment P 14 (some 0) m (List.replicate B []) = some (scan p 0 B m)
  zeroRun : let P := (zeroPass.table.instantiate w p).program
    runSegment P 5 (some 0) (after m (eventLog (scan p 0 B m))) [[]] = some [zeroRow p]
  readback : ∀ i, i < B → after m (eventLog (reports p B m)) (cell (p 1) i) = extract p (m (cell (p 0) i))
  zero : after m (eventLog (reports p B m)) (p 2).val = 0
  preserve : ∀ v, v ≠ (p 2).val → (∀ i, i < B → v ≠ cell (p 1) i) → after m (eventLog (reports p B m)) v = m v
  calls : (reports p B m).length = B+1
  cost : RAMBuckets.cost Report.probes (reports p B m) = 3*B+2
  work : ∀ r ∈ reports p B m, r.events.length ≤ 13 ∧ r.probes ≤ 2 ∧ choiceBits r.events = []

theorem scan_result (p : Fin 5 → Word w) (B : ℕ) (m : Memory w) (reg : Regions p B) : Result p B m := by
  obtain ⟨hl,hc,hw⟩ := scan_work p 0 B m
  constructor
  · simpa using scan_native p 0 B m
  · dsimp only
    rw [runSegment, zero_native]
    rfl
  · intro i hi
    rw [after_reports, writeMemory, ite_eq_right (reg.zero i hi)]
    exact scan_read reg 0 B m (by omega) i (by omega) (by omega)
  · rw [after_reports, writeMemory, ite_eq_left rfl]
  · intro v hv h
    rw [after_reports, writeMemory, ite_eq_right hv]
    exact scan_outside p 0 B m v (fun j _ hlt ↦ h j (by omega))
  · simp [reports, hl]
  · rw [reports, RAMBuckets.cost_append, hc]
    rfl
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨he,hp,hb⟩ := hw r hr
      exact ⟨he.le,hp.le,hb⟩
    · rcases List.mem_singleton.mp hr with rfl
      exact ⟨show 4 ≤ 13 by decide,show 1 ≤ 2 by decide,rfl⟩

/-- The tag is the binary field directly above the residual lane. -/
theorem packedTagNumber {a g : ℕ} (x : BitWord (packingLaneBits a g)) :
    (bitWordFinEquiv _ x).val / 2^g % 2^(Shrink.J a) =
      (bitWordFinEquiv _ (packingFields a g x).2.2.1).val := by
  rw [Shrink.packingFields_number]
  let high := Shrink.join a (bitWordFinEquiv _ (packingFields a g x).1).val
    (bitWordFinEquiv _ (packingFields a g x).2.1).val
  let tag := bitWordFinEquiv _ (packingFields a g x).2.2.1
  let lane := bitWordFinEquiv _ (packingFields a g x).2.2.2
  change (high * 2^(Shrink.J a + g) + (tag.val * 2^g + lane.val)) / 2^g % 2^(Shrink.J a) = tag.val
  rw [show high * 2^(Shrink.J a + g) + (tag.val * 2^g + lane.val) =
    2^g * (high * 2^(Shrink.J a) + tag.val) + lane.val by rw [pow_add]; ring,
    Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt lane.isLt, Nat.add_zero]
  exact Nat.mul_add_mod_of_lt tag.isLt

theorem radices_fit {a g w : ℕ} (h : packingLaneBits a g ≤ w) :
    2^g < 2^w ∧ 2^(Shrink.J a) < 2^w ∧ Shrink.J a ≤ w := by
  change (2 * 2^a + 1) + (a + (Shrink.J a + g)) ≤ w at h
  exact ⟨Nat.pow_lt_pow_right Nat.one_lt_two (by omega), Nat.pow_lt_pow_right Nat.one_lt_two (by omega),
    by omega⟩

private theorem extract_val (p : Fin 5 → Word w) (x : Word w) :
    (extract p x).val = x.val / (p 3).val % (p 4).val := by
  have h := (Nat.div_le_self x.val (p 3).val).trans_lt x.isLt
  simp only [extract, BinaryOp.eval, Fin.val_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt h)]

/-- The emitted increments are exactly the tag fields used by the ordered
shrinking construction, with an initialized external zero operand. -/
theorem extract_directory (X : State a (packingLaneBits a g)) (T : IncidenceDirectory w)
    (dst zero : Word w) (m : Memory w) (rep : T.Represents X m)
    (fullFit : packingLaneBits a g ≤ w)
    (reg : Regions (params T a g dst zero) (Fintype.card X.Base * 2^a)) :
    let p := params T a g dst zero
    let B := Fintype.card X.Base * 2^a
    Result p B m ∧ ∀ e : X.Base × Fin (2^a),
      after m (eventLog (reports p B m)) (dst+IncidenceDirectory.basePort X e).val =
        tagWord (radices_fit fullFit).2.2 ((packingFields a g) (X.slots.displacement e)).2.2.1 := by
  let p := params T a g dst zero
  have hr := scan_result p _ m reg
  refine ⟨hr, ?_⟩
  intro e
  let i := IncidenceDirectory.baseOrder X e
  have hs : cell (p 0) i.val = (T.shift+IncidenceDirectory.basePort X e).val := by
    rw [IncidenceDirectory.basePort_number]; rfl
  have hd : cell (p 1) i.val = (dst+IncidenceDirectory.basePort X e).val := by
    rw [IncidenceDirectory.basePort_number]; rfl
  rw [← hd, hr.readback _ i.isLt, hs, rep.shift]
  apply Fin.ext
  rw [extract_val, tagWord_val]
  obtain ⟨hg,hj,_⟩ := radices_fit fullFit
  have hx := (bitWordFinEquiv _ (X.slots.displacement e)).isLt.trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) fullFit)
  change (_ % 2^w) / (2^g % 2^w) % (2^(Shrink.J a) % 2^w) = _
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hg, Nat.mod_eq_of_lt hj]
  exact packedTagNumber _

section Dispatcher

open OrdinalRun Schedule SourceTransport

/-- The actual word addresses used by an indexed column, including wrapping heads. -/
def InColumn (base : Word w) (B x : ℕ) : Prop := ∃ i < B, x = cell base i

private theorem row_footprints (p : Fin 5 → Word w) (m : Memory w) {i B : ℕ} (hi : i < B) :
    Reads (InColumn (p 0) B) (row p (i : Word w) m).events ∧
      Writes (InColumn (p 1) B) (row p (i : Word w) m).events := by
  constructor <;> intro a v h
  · obtain ⟨rfl,_⟩ := (by simpa [row] using h : a = p 0+(i : Word w) ∧ v = _)
    exact ⟨i,hi,rfl⟩
  · obtain ⟨rfl,_⟩ := (by simpa [row] using h : a = p 1+(i : Word w) ∧ v = _)
    exact ⟨i,hi,rfl⟩

/-- The shift scan reads only old base displacements and writes only extracted tags. -/
theorem scan_footprints (p : Fin 5 → Word w) (B : ℕ) (m : Memory w) :
    Reads (InColumn (p 0) B) (eventLog (scan p 0 B m)) ∧
      Writes (InColumn (p 1) B) (eventLog (scan p 0 B m)) := by
  let P := (extractPass.table.instantiate w p).program
  let cursor (i : ℕ) : Word w := i
  apply OrdinalRun.footprint P 14 cursor B (fun _ _ => True) _ _ _ 0 _ m _ (by simp) trivial
    (scan_native p 0 B m)
  intro j hj m _ bits r h
  have eqn := (execute_prefix_unique (row_native p (cursor j) m)
    (show execute P 14 (P.start (cursor j)) m ([] ++ bits) = some r from h)).2
  subst r
  obtain ⟨rd,wr⟩ := row_footprints p m hj
  exact ⟨by simp [cursor,row],trivial,rd,wr⟩

/-- The zero initializer has no read dependency and writes just its own cell. -/
theorem zero_footprints (p : Fin 5 → Word w) :
    Reads (fun _ => False) (eventLog [zeroRow p]) ∧
      Writes (fun x => x = (p 2).val) (eventLog [zeroRow p]) := by
  constructor <;> intro a v h
  · simp [eventLog, zeroRow] at h
  · obtain ⟨rfl,_⟩ := (by simpa [eventLog,zeroRow] using h : a = p 2 ∧ v = 0)
    rfl

variable {d : ℕ} (C : Catalog d) (worker : Fin d) (ports : Ports w)

/-- The installed frame stays ready through all rows and the final cursor closes the worker. -/
theorem scan_valid (pub : Fin (C worker).params → Word w) (p : Fin 5 → Word w) (B : ℕ) (m : Memory w)
    (fit : B < 2^w) (ready : Ready C worker ports pub (B : Word w) m)
    (apart : ∀ x, ControlCell (C worker).params ports x → ¬ InColumn (p 1) B x) :
    ValidTrace C worker ports pub (B : Word w) 0 m (scan p 0 B m) ∧
      Preserved (C worker).params ports m (after m (eventLog (scan p 0 B m))) := by
  let P := (extractPass.table.instantiate w p).program
  let cursor (i : ℕ) : Word w := i
  have active (i : ℕ) (hi : i < B) : cursor i < cursor B := by
    change i%(2^w) < B%(2^w)
    rwa [Nat.mod_eq_of_lt (hi.trans fit), Nat.mod_eq_of_lt fit]
  have advance (j : ℕ) (hj : j < B) (mem : Memory w) (_ : True) (bits : List Bool) (r : Report w)
      (h : execute P 14 (P.start (cursor j)) mem bits = some r) :
      r.result = some (cursor (j+1)) ∧ True ∧ Preserved (C worker).params ports mem (after mem r.events) := by
    have eqn := (execute_prefix_unique (row_native p (cursor j) mem)
      (show execute P 14 (P.start (cursor j)) mem ([] ++ bits) = some r from h)).2
    subst r
    exact ⟨by simp [cursor,row], trivial,
      fun x hx ↦ after_outside mem (row_footprints p mem hj).2 (apart x hx)⟩
  obtain ⟨trace,_,keep⟩ := OrdinalRun.validTrace C worker ports P 14 pub (cursor B) cursor B
    (fun _ _ => True) active le_rfl advance 0 _ m _ (by simp) trivial ready (scan_native p 0 B m)
  exact ⟨trace,keep⟩

/-- Guard and frame correctness of the single zero write after the shift scan. -/
theorem zero_valid (pub : Fin (C worker).params → Word w) (p : Fin 5 → Word w) (m : Memory w)
    (fit : 1 < 2^w) (ready : Ready C worker ports pub 1 m)
    (apart : ∀ x, ControlCell (C worker).params ports x → x ≠ (p 2).val) :
    ValidTrace C worker ports pub 1 0 m [zeroRow p] ∧
      Preserved (C worker).params ports m (after m (eventLog [zeroRow p])) := by
  have keep : Preserved (C worker).params ports m (after m (zeroRow p).events) :=
    fun x hx ↦ by rw [zero_after]; exact ite_eq_right (apart x hx)
  have lt : (0 : Word w) < 1 := by
    change 0 < 1%(2^w)
    rw [Nat.mod_eq_of_lt fit]; decide
  exact ⟨⟨ready,lt,1,rfl,ready_of_preserved C worker ports ready keep,le_rfl⟩,keep⟩

end Dispatcher

end CompressorRecords.ShrinkTagColumn

end VPVNP
end Computability
end OAI
