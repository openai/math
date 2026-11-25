import OAI.ThreeFlat.RAM.ExpressionScan
import OAI.ThreeFlat.RAM.ContractionMemory
import OAI.ThreeFlat.BitNetwork.OrderedGlue

namespace OAI
/-! # Resolving one postorder child record stream in the native RAM

A fixed six-word header stores the child table address, destination address,
child-pin wiring table address, old and new pin counts, and the offset of
the child's private bits in its parent. Input and output pointers use the
same `BitLayout` as the final trivalent evaluator.
-/

namespace ThreeFlat.RAM.HistoryJoinScan

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr

variable {w k : ℕ}

structure Header (α : Type*) where
  source : α
  dest : α
  pins : α
  oldPins : α
  newPins : α
  offset : α

def fetch (b : Word w) (m : Memory w) : Header (Word w) :=
  ⟨m (b+0).val,m (b+1).val,m (b+2).val,m (b+3).val,m (b+4).val,m (b+5).val⟩

def readWord (v : Header (Word w)) (m : Memory w) (addr : Word w) : Word w :=
  let delta := addr - v.dest
  let raw := m (v.source+delta).val
  let col := BinaryOp.eval .mod delta 4
  if col < 3 then
    if raw < 2 then raw
    else if raw < 2+v.oldPins then m (v.pins+(raw-2)).val
    else raw-v.oldPins+v.newPins+v.offset
  else raw

private def readHeader (base : Fin k) (j : Word w) : Term w k 1 :=
  (Term.binary .add (Term.parameter base).load (.literal j)).load

/-- There is one program text over all stage sizes and all six values in the header. -/
def term (base : Fin k) : Term w k 1 :=
  let delta := Term.binary .sub (.result 0) (readHeader base 1)
  let raw := (Term.binary .add (readHeader base 0) delta).load
  let col := Term.binary .mod delta (.literal 4)
  let mapped := (Term.binary .add (readHeader base 2) (Term.binary .sub raw (.literal 2))).load
  let shifted := Term.binary .add (Term.binary .add (Term.binary .sub raw (readHeader base 3))
    (readHeader base 4)) (readHeader base 5)
  let source := Term.select .lt raw (.literal 2) raw
    (Term.select .lt raw (Term.binary .add (.literal 2) (readHeader base 3)) mapped shifted)
  Term.select .lt col (.literal 3) source raw

theorem eval_term (base : Fin k) (params : Fin k → Word w) (m : Memory w) (vs : Fin 1 → Word w) :
    (term base).eval params m vs = readWord (fetch (m (params base).val) m) m (vs 0) := by
  let v := fetch (m (params base).val) m
  let delta := vs 0 - v.dest
  let raw := m (v.source + delta).val
  let col := BinaryOp.eval .mod delta 4
  simp only [term,readHeader,Term.eval_select,Term.eval_load,Term.eval_binary,Term.eval_parameter,Term.eval_literal,Term.eval]
  change (if Comparison.lt.test col 3 then
    (if Comparison.lt.test raw 2 then raw else
      if Comparison.lt.test raw (2+v.oldPins) then m (v.pins+(raw-2)).val else raw-v.oldPins+v.newPins+v.offset)
    else raw) = _
  change _ = (if col < 3 then (if raw < 2 then raw else
    if raw < 2+v.oldPins then m (v.pins+(raw-2)).val else raw-v.oldPins+v.newPins+v.offset) else raw)
  simp only [Comparison.test,decide_eq_true_eq]

/-- Source memory needed on the taken branches is precisely the six-word
header, the previous table, and the row's translated pin if it has one. -/
theorem readWord_frame (base a : Word w) (m m' : Memory w)
    (control : ∀ j : Fin 6, m' (base + Fin.ofNat _ j.val).val = m (base + Fin.ofNat _ j.val).val)
    (source : let v := fetch base m; m' (v.source+(a-v.dest)).val = m (v.source+(a-v.dest)).val)
    (mapEq : let v := fetch base m; let x := m (v.source+(a-v.dest)).val;
      ¬x < 2 → x < 2+v.oldPins → m' (v.pins+(x-2)).val = m (v.pins+(x-2)).val) :
    readWord (fetch base m') m' a = readWord (fetch base m) m a := by
  have eq : fetch base m' = fetch base m := by
    simp only [fetch]
    congr 1
    all_goals first | exact control 0 | exact control 1 | exact control 2 | exact control 3 |
      exact control 4 | exact control 5
  rw [eq]
  dsimp only [readWord]
  dsimp only at source mapEq
  rw [source]
  split
  · split
    · rfl
    · split
      · apply mapEq <;> assumption
      · rfl
  · rfl

/-- Addresses read by the child stream and its pin map lie outside the output interval. -/
structure Separate (header : Word w) (lo hi : ℕ) (m : Memory w) : Prop where
  control : ∀ j : Fin 6, let u := (header + Fin.ofNat _ j.val).val; u < lo ∨ hi ≤ u
  source : ∀ a : Word w, lo ≤ a.val → a.val < hi →
    let v := fetch header m; let u := (v.source + (a-v.dest)).val; u < lo ∨ hi ≤ u
  pins : ∀ a : Word w, lo ≤ a.val → a.val < hi → let v := fetch header m
    let x := m (v.source+(a-v.dest)).val; ¬x < 2 → x < 2+v.oldPins →
    let u := (v.pins+(x-2)).val; u < lo ∨ hi ≤ u

set_option maxRecDepth 4096 in
theorem term_binds (base : Fin k) : (term (w := w) base).binds = 125 := by
  simp only [term,readHeader,Term.load,Term.binary,Term.select,Term.literal,Term.parameter,
    Term.binds_letThen,Term.binds_rename,Term.binds]

/-- Running the installed deterministic instruction table emits a whole child
into its parent with at most 254 instructions per output word. -/
theorem generate {p r : ℕ} (M : Machine w p r k) (R : Fin 4 ↪ Fin r) (L : DescriptorScan.Labels p)
    (base : Fin k) (loc : Fin (term (w := w) base).labels → Fin p)
    (tmp : Fin (term (w := w) base).binds ↪ Fin r) (fresh : ∀ i j, R i ≠ tmp j)
    (entry : loc (term base).first = L.describe) (installed : DescriptorScan.Installed M R L)
    (rom : ∀ i, M.code (loc i) = (term base).emit loc (fun _ => R 0) tmp (R 2) L.store i)
    (m : Memory w) (c : Config w p r) (n : ℕ) (start : c.pc = L.guard) (unit : c.reg (R 3) = 1)
    (length : (c.reg (R 0)).val + n = (c.reg (R 1)).val)
    (ctrl : (M.publicData base).val < (c.reg (R 0)).val ∨ (c.reg (R 1)).val ≤ (M.publicData base).val)
    (sep : Separate (m (M.publicData base).val) (c.reg (R 0)).val (c.reg (R 1)).val m) :
    let word := fun a : ℕ => readWord (fetch (m (M.publicData base).val) m) m (Fin.ofNat _ a)
    ∃ steps ≤ 1+n*254, ∃ out : Config w p r, out.pc = L.exit ∧
      advance M.program steps c m = some (out, fillSegment (c.reg (R 0)).val n word m) := by
  intro word
  let e := term (w := w) base
  have desc := DescriptorScan.describes_expression M R L e loc tmp fresh entry rom
    (c.reg (R 0)).val (c.reg (R 1)).val m word (by
      intro a mem lo hi frame
      rw [eval_term, frame _ ctrl]
      change readWord (fetch _ mem) mem a = readWord (fetch _ m) m (Fin.ofNat _ a.val)
      have eq : Fin.ofNat (2^w) a.val = a := Fin.ext (Nat.mod_eq_of_lt a.isLt)
      rw [eq]
      apply readWord_frame
      · intro j; exact frame _ (sep.control j)
      · exact frame _ (sep.source a lo hi)
      · dsimp only
        intro small bound
        exact frame _ (sep.pins a lo hi small bound))
  have ok : DescriptorScan.scanInvariant R (c.reg (R 0)).val (c.reg (R 1)).val m c m :=
    ⟨unit, le_rfl, rfl, fun _ _ => rfl⟩
  have run := DescriptorScan.generate M R L installed e.steps word _ desc n c m start ok length
  simpa only [e, Term.steps_eq, term_binds] using run

/-- Natural-number counterpart of the pointer transformation. -/
def translate (p P off : ℕ) (mapPin : ℕ → ℕ) (raw : ℕ) : ℕ :=
  if raw < 2 then raw else if raw < 2+p then mapPin (raw-2) else raw-p+P+off

/-- The arithmetic used in the copy loop gives exactly the flat network's
ordered source pointer, including the global hidden prefix. -/
theorem translate_source {F : Type*} {m p h : ℕ} {arity : Fin m → ℕ}
    (N : (i : Fin m) → BitNetwork F (arity i))
    (wire : (i : Fin m) → Fin (arity i) → BitSource h p)
    (i : Fin m) (mapPin : ℕ → ℕ)
    (map_ok : ∀ j, mapPin j.val = BitLayout.sourceAddress
      (BitNetwork.Ordered.resolve N wire i (.pin j))) (s : BitSource (N i).internal (arity i)) :
    translate (arity i) p (h + ∑ j : Fin i.val, (N (Fin.castLE i.isLt.le j)).internal)
      mapPin (BitLayout.sourceAddress s) =
    BitLayout.sourceAddress (BitNetwork.Ordered.resolve N wire i s) := by
  cases s with
  | constant b => cases b <;> rfl
  | pin j =>
    have lo : ¬2+j.val < 2 := by omega
    have hi : 2+j.val < 2+arity i := by omega
    simpa [translate, BitLayout.sourceAddress, lo, hi] using map_ok j
  | hidden j =>
    change translate (arity i) p (h + ∑ z : Fin i.val, (N (Fin.castLE i.isLt.le z)).internal)
      mapPin (2+arity i+j.val) = (2+p) + (BitNetwork.Ordered.privateEquiv (h:=h) N (.inr ⟨i,j⟩)).val
    rw [BitNetwork.Ordered.private_offset]
    unfold translate
    have lo : ¬2+arity i+j.val < 2 := by omega
    have hi : ¬2+arity i+j.val < 2+arity i := by omega
    simp only [ite_eq_right lo,ite_eq_right hi]
    omega

end ThreeFlat.RAM.HistoryJoinScan

end OAI
