import OAI.Computability.VPVNP.CompressorRecordsBundleRank

/-!
# Fixed-degree rank worker indexed by the old outgoing port

The burst call loads the port's classified owner, its key, and its owner's
count. It scans a fixed number of cells in the owner's key row. A saturating
countdown masks the unused tail of a thick row, so the initial contents of the
tail cells are immaterial. The resulting rank is written at the old port's
absolute address, and the returned cursor advances to the next port.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRankRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- Straight-line instructions for the old-port rank worker, with nine private registers and
six public operands. -/
abbrev Ops := List (Op 9 6)

/-- Read the classified owner of old port `i` from the owner column addressed by public operand
zero. -/
def owner (p : Fin 6 → Word w) (m : Memory w) (i : Word w) := m (p 0+i).val
/-- Read the key of old port `i` that the worker compares with keys belonging to the same
owner. -/
def pivot (p : Fin 6 → Word w) (m : Memory w) (i : Word w) := m (p 1+i).val
/-- Read the number of valid entries in the old port owner's key row from the count column. -/
def lengthAt (p : Fin 6 → Word w) (m : Memory w) (i : Word w) := m (p 4+owner p m i).val
/-- Address of the first key in the old port owner's row, computed from the key-array base,
owner index and row stride. -/
def start (p : Fin 6 → Word w) (m : Memory w) (i : Word w) := p 2+owner p m i*p 3

private def samples (m : Memory w) (ptr : Word w) : ℕ → List (Word w)
  | 0 => []
  | n+1 => m ptr.val :: samples m (ptr+1) n

/-- Sample `cap` consecutive key words beginning at the old port owner's row, including any
unused tail cells. -/
def row (p : Fin 6 → Word w) (m : Memory w) (i : Word w) (cap : ℕ) :=
  samples m (start p m i) cap

private theorem word_succ (k : ℕ) : Fin.ofNat (2^w) (k+1) = Fin.ofNat _ k+1 := by
  apply Fin.ext
  simp [Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod]

private theorem samples_eq_ofFn (m : Memory w) (ptr : Word w) (n : ℕ) :
    samples m ptr n = List.ofFn (fun j : Fin n ↦ m (ptr + Fin.ofNat _ j.val).val) := by
  induction n generalizing ptr with
  | zero => rfl
  | succ n ih =>
    rw [samples, List.ofFn_succ, ih]
    simp only [Fin.val_zero, Fin.ofNat_zero, add_zero, Fin.val_succ, word_succ]
    congr 2
    funext j
    rw [add_right_comm, add_assoc]

theorem row_eq_map (p : Fin 6 → Word w) (m : Memory w) (i : Word w) (cap : ℕ) :
    row p m i cap = (List.range cap).map fun j ↦ m (start p m i + Fin.ofNat _ j).val := by
  rw [row, samples_eq_ofFn]
  apply List.ext_getElem <;> simp

/-- Rank of the old port's key as a machine word. Count strictly smaller keys in the sampled
row prefix limited by the owner's stored count. -/
def result (p : Fin 6 → Word w) (m : Memory w) (i : Word w) (cap : ℕ) : Word w :=
  Fin.ofNat _ (((row p m i cap).take (lengthAt p m i).val).countP fun x ↦ decide (x < pivot p m i))

private def setup : Ops :=
  [.stateWord 0, .publicWord 6 0, .binary .add 6 6 0, .read 8 6,
   .publicWord 6 1, .binary .add 6 6 0, .read 2 6,
   .publicWord 6 4, .binary .add 6 6 8, .read 3 6,
   .publicWord 6 3, .binary .mul 1 8 6, .publicWord 6 2,
   .binary .add 1 6 1, .constant 5 1]

private def step : Ops :=
  [.read 6 1, .binary .add 6 6 5, .binary .div 6 2 6, .binary .div 6 6 6,
   .binary .div 7 3 3, .binary .sub 3 3 7, .binary .mul 6 7 6,
   .binary .add 4 4 6, .binary .add 1 1 5]

private def walk : ℕ → Ops
  | 0 => []
  | n+1 => step ++ walk n

private def finish : Ops :=
  [.publicWord 6 5, .binary .add 6 6 0, .write 6 4, .binary .add 0 0 5]

/-- One straight-line template for all old ports of the same fixed degree. -/
def visit (cap : ℕ) : Ops := setup ++ walk cap ++ finish

theorem visit_length (cap : ℕ) : (visit cap).length = 19 + 9*cap := by
  have h (n : ℕ) : (walk n).length = 9*n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [walk, step, ih]; omega
  simp [visit, setup, finish, h]; omega

private abbrev div (x y : Word w) := BinaryOp.div.eval x y

private theorem div_val (x y : Word w) : (div x y).val = x.val / y.val :=
  Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)

private theorem active (x : Word w) : div x x = if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · simp [hx, div, BinaryOp.eval]
  · rw [ite_eq_right hx]
    change Fin.ofNat _ (x.val / x.val) = _
    rw [Nat.div_self (Nat.pos_of_ne_zero (fun h ↦ hx (Fin.ext h)))]
    rfl

private theorem lessIndicator (x pivot : Word w) :
    div (div pivot (x+1)) (div pivot (x+1)) = if x < pivot then 1 else 0 := by
  rw [active]
  have hs : (x+1).val = (x.val+1) % (2^w) := by
    simp [Fin.val_add, Nat.add_mod_mod]
  by_cases h : x < pivot
  · have lt : x.val < pivot.val := h
    have hs' := Nat.mod_eq_of_lt (show x.val+1 < 2^w by have := pivot.isLt; omega)
    have hn : div pivot (x+1) ≠ 0 := by
      intro hz
      have := congrArg Fin.val hz
      rw [div_val, hs, hs'] at this
      exact (Nat.ne_of_gt (Nat.div_pos lt (Nat.zero_lt_succ _))) this
    simp [h, hn]
  · have le : pivot.val ≤ x.val := le_of_not_gt h
    have hz : div pivot (x+1) = 0 := by
      apply Fin.ext
      rw [div_val, hs]
      by_cases fit : x.val+1 < 2^w
      · rw [Nat.mod_eq_of_lt fit, Nat.div_eq_of_lt (by omega)]; rfl
      · have top : x.val+1 = 2^w := by have := x.isLt; omega
        rw [top, Nat.mod_self, Nat.div_zero]; rfl
    simp [h, hz]

private def preEvents (p : Fin 6 → Word w) (m : Memory w) (i : Word w) : List (Event w) :=
  [.tick,.tick,.tick,.read (p 0+i) (owner p m i),.tick,.tick,.read (p 1+i) (pivot p m i),
   .tick,.tick,.read (p 4+owner p m i) (lengthAt p m i),.tick,.tick,.tick,.tick,.tick]

private theorem setup_trace (p : Fin 6 → Word w) (m : Memory w) (i : Word w) :
    ∃ r, trace p i setup (fun _ ↦ 0) m = some (preEvents p m i,r,m) ∧
      r 0 = i ∧ r 1 = start p m i ∧ r 2 = pivot p m i ∧ r 3 = lengthAt p m i ∧
      r 4 = 0 ∧ r 5 = 1 := by
  simp (config := {decide := true}) [setup, preEvents, owner, pivot, start, lengthAt,
    trace, Op.effect, BinaryOp.eval, Function.update]
  rfl

private def walkEvents (m : Memory w) (ptr : Word w) : ℕ → List (Event w)
  | 0 => []
  | n+1 => [.read ptr (m ptr.val),.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick] ++ walkEvents m (ptr+1) n

private theorem step_trace (p : Fin 6 → Word w) (m : Memory w) (i : Word w)
    (r : Regs w 9) (h1 : r 5 = 1) :
    let live := if r 3 = 0 then 0 else (1 : Word w)
    let lt := if m (r 1).val < r 2 then (1 : Word w) else 0
    ∃ s, trace p i step r m =
      some ([.read (r 1) (m (r 1).val),.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick],s,m) ∧
      s 0 = r 0 ∧ s 1 = r 1+1 ∧ s 2 = r 2 ∧ s 3 = r 3-live ∧
      s 4 = r 4+live*lt ∧ s 5 = 1 := by
  dsimp only
  simp (config := {decide := true}) [step, trace, Op.effect, Function.update, h1,
    BinaryOp.eval] at *
  refine ⟨active (r 3), ?_⟩
  change div (r 3) (r 3) * div (div (r 2) (m (r 1).val + 1)) (div (r 2) (m (r 1).val + 1)) = _
  rw [active, lessIndicator]
  split <;> simp_all

private theorem walk_trace (p : Fin 6 → Word w) (m : Memory w) (i : Word w)
    (cap : ℕ) (r : Regs w 9) (hone : r 5 = 1) :
    ∃ s, trace p i (walk cap) r m = some (walkEvents m (r 1) cap,s,m) ∧
      s 0 = r 0 ∧ s 5 = 1 ∧ s 4 = r 4 +
        Fin.ofNat _ (((samples m (r 1) cap).take (r 3).val).countP fun x ↦ decide (x < r 2)) := by
  induction cap generalizing r with
  | zero => exact ⟨r, rfl, rfl, hone, by simp [samples]⟩
  | succ n ih =>
    obtain ⟨s, hs, h0, hptr, hpiv, hrem, hacc, hu⟩ := step_trace p m i r hone
    obtain ⟨t, ht, h0', hu', hv⟩ := ih s hu
    refine ⟨t, ?_, h0'.trans h0, hu', ?_⟩
    · simp [walk, trace_append, hs, ht, walkEvents, hptr]
    rw [hv, hacc, hptr, hpiv, hrem]
    by_cases hr : r 3 = 0
    · simp [hr]
    · obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (fun h ↦ hr (Fin.ext h))
      have hleft : (r 3-1).val = k := by rw [Fin.val_sub_one_of_ne_zero hr, hk]; omega
      simp only [hr, ite_false, hleft, samples, hk, List.take_succ_cons, one_mul, List.countP_cons]
      by_cases hlt : m (r 1).val < r 2
      · simp only [hlt, decide_true, ite_true, word_succ]
        ac_rfl
      · simp [hlt]

private def finalEvents (p : Fin 6 → Word w) (i rank : Word w) : List (Event w) :=
  [.tick,.tick,.write (p 5+i) rank,.tick]

private theorem finish_trace (p : Fin 6 → Word w) (m : Memory w) (i : Word w) (r : Regs w 9)
    (h0 : r 0 = i) (hu : r 5 = 1) :
    ∃ s, trace p i finish r m = some (finalEvents p i (r 4),s,writeMemory m (p 5+i) (r 4)) ∧
      s 0 = i+1 := by
  simp (config := {decide := true}) [finish, trace, Op.effect, BinaryOp.eval,
    finalEvents, Function.update, h0, hu]

private theorem walk_stats (m : Memory w) (ptr : Word w) (cap : ℕ) (tail : List (Event w)) :
    countProbes (walkEvents m ptr cap ++ tail) = cap + countProbes tail ∧
      (walkEvents m ptr cap ++ tail).length = 9*cap + tail.length ∧
      after m (walkEvents m ptr cap ++ tail) = after m tail := by
  induction cap generalizing ptr with
  | zero => simp [walkEvents]
  | succ n ih =>
    obtain ⟨hp,hl,hm⟩ := ih (ptr+1)
    refine ⟨?_, ?_, hm⟩
    · change 1 + countProbes (walkEvents m (ptr+1) n ++ tail) = _; omega
    · change (walkEvents m (ptr+1) n ++ tail).length + 9 = _; omega

/-- Actual native execution on arbitrary external words, including unused row
cells equal to the largest representable word. -/
theorem run_one (p : Fin 6 → Word w) (m : Memory w) (i : Word w) (cap : ℕ) :
    let M := (template (visit cap) 0).instantiate w p
    ∃ es, execute M.program (1+(visit cap).length) (M.program.start i) m [] = some ⟨es,some (i+1)⟩ ∧
      after m es = writeMemory m (p 5+i) (result p m i cap) ∧ countProbes es = cap+4 ∧
      es.length = (visit cap).length := by
  obtain ⟨r,hs,h0,hptr,hpiv,hrem,hacc,hu⟩ := setup_trace p m i
  obtain ⟨s,hw,hs0,hsu,hs4⟩ := walk_trace p m i cap r hu
  obtain ⟨t,hf,hret⟩ := finish_trace p m i s (hs0.trans h0) hsu
  have heq : s 4 = result p m i cap := by simpa only [result,row,hptr,hpiv,hrem,hacc,zero_add] using hs4
  rw [heq] at hf
  let tail := finalEvents p i (result p m i cap)
  obtain ⟨hp,hl,hm⟩ := walk_stats m (r 1) cap tail
  refine ⟨preEvents p m i ++ (walkEvents m (r 1) cap ++ tail), ?_, hm, ?_, ?_⟩
  · change execute ((template (visit cap) 0).instantiate w p).program (1+(visit cap).length)
      ⟨_, i, fun _ ↦ 0, fun _ ↦ 0⟩ m [] = _
    rw [execute_template, run_eq_trace, visit, trace_append, trace_append, hs]
    simp [hw,hf,hret,List.append_assoc,tail]
  · change 1+(1+(1+countProbes (walkEvents m (r 1) cap ++ tail))) = _
    change countProbes (walkEvents m (r 1) cap ++ tail) = cap+1 at hp
    omega
  · rw [List.length_append, visit_length, hl]
    change 15+(9*cap+4) = _
    omega

end CompressorRecords.PortRankRAM

end VPVNP
end Computability
end OAI
