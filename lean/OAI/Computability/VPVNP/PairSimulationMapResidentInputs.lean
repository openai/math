import OAI.Computability.VPVNP.PairNodeChildLoop

/-!
# Reading the map list and term pointers of a shrinking site

Four consecutive level words give the map-count head, dense-ID table head,
term head, and term stride. Every packed site's count is its row capacity
(6dQ), so the count already read supplies the row stride. The next
fragment splits one ID into its motif and party and reads the first word
of the motif's term record, the demand-grid ordinal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapResidentInputs

open BurstRAM PrivateRAM NodeArguments.ChildScan
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.nil ReadPrefix.tick ReadPrefix.read ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices

variable {w p r k : ℕ}

/-- Registers zero and one hold the old level header and packed site ordinal.
Registers two and three receive the half-open map-ID range, and four and
five the term-table base and stride. Registers eight to ten are scratch. -/
def headerCode (pc : Fin 16 → Fin p) (reg : Fin 11 ↪ Fin r) (done : Fin p) :
    Fin 16 → Instr w p r k :=
  ![.constant (reg 9) 17 (pc 1), .binary .add (reg 9) (reg 9) (reg 9) (pc 2),
    .binary .add (reg 9) (reg 0) (reg 9) (pc 3),
    .readExternal (reg 2) (reg 9) (pc 4), .binary .add (reg 2) (reg 2) (reg 1) (pc 5),
    .readExternal (reg 3) (reg 2) (pc 6), .constant (reg 10) 1 (pc 7),
    .binary .add (reg 9) (reg 9) (reg 10) (pc 8), .readExternal (reg 2) (reg 9) (pc 9),
    .binary .mul (reg 8) (reg 1) (reg 3) (pc 10), .binary .add (reg 2) (reg 2) (reg 8) (pc 11),
    .binary .add (reg 3) (reg 2) (reg 3) (pc 12), .binary .add (reg 9) (reg 9) (reg 10) (pc 13),
    .readExternal (reg 4) (reg 9) (pc 14), .binary .add (reg 9) (reg 9) (reg 10) (pc 15),
    .readExternal (reg 5) (reg 9) done]

theorem resize_headerCode (pc : Fin 16 → Fin p) (reg : Fin 11 ↪ Fin r) (done : Fin p) (i : Fin 16) :
    (headerCode (w := 5) (k := k) pc reg done i).resize w = headerCode pc reg done i := by
  fin_cases i <;> rfl

/-- The header scan is linked to the first map-list guard. -/
def HeaderLinked (M : Machine w p r k) (pc : Fin 16 → Fin p) (reg : Fin 11 ↪ Fin r)
    (done : Fin p) : Prop := ∀ i, M.code (pc i) = headerCode pc reg done i

/-- The count word at this packed site. -/
def count (m : Memory w) (level site : Word w) : Word w := m (m (level + 34).val + site).val

/-- First cell of this site's packed map-ID row. -/
def rowStart (m : Memory w) (level site : Word w) : Word w :=
  m (level + 35).val + site * count m level site

private def fetch (m : Memory w) (addr : Word w) := Event.read addr (m addr.val)

/-- The header trace includes the indirect count read and the four pointer
or stride words. All reads come from the supplied external memory. -/
def headerEvents (m : Memory w) (level site : Word w) : List (Event w) :=
  [.tick, .tick, .tick, fetch m (level+34), .tick, fetch m (m (level+34).val + site),
   .tick, .tick, fetch m (level+35), .tick, .tick, .tick, .tick, fetch m (level+36),
   .tick, fetch m (level+37)]

theorem headerCost (m : Memory w) (level site : Word w) :
    (headerEvents m level site).length = 16 ∧ countProbes (headerEvents m level site) = 5 ∧
      choiceBits (headerEvents m level site) = [] := ⟨rfl,rfl,rfl⟩

/-- The entry scan preserves all registers outside its seven destinations. -/
def HeaderFrame (reg : Fin 11 ↪ Fin r) (j : Fin r) : Prop :=
  j ≠ reg 2 ∧ j ≠ reg 3 ∧ j ≠ reg 4 ∧ j ≠ reg 5 ∧ j ≠ reg 8 ∧ j ≠ reg 9 ∧ j ≠ reg 10

/-- Cursor bounds and term lookup data actually read for the enclosing loop. -/
structure HeaderResult (reg : Fin 11 ↪ Fin r) (done : Fin p) (m : Memory w) (c d : Config w p r) :
    Prop where
  pc : d.pc = done
  cursor : d.reg (reg 2) = rowStart m (c.reg (reg 0)) (c.reg (reg 1))
  stop : d.reg (reg 3) = rowStart m (c.reg (reg 0)) (c.reg (reg 1)) +
    count m (c.reg (reg 0)) (c.reg (reg 1))
  term : d.reg (reg 4) = m (c.reg (reg 0) + 36).val
  stride : d.reg (reg 5) = m (c.reg (reg 0) + 37).val
  one : d.reg (reg 10) = 1
  frame : ∀ a, HeaderFrame reg a → d.reg a = c.reg a
  memory : d.privateMem = c.privateMem
  persistent : d.persistent = c.persistent

variable {M : Machine w p r k} {reg : Fin 11 ↪ Fin r} {done : Fin p}

private theorem headerStep {pc : Fin 16 → Fin p} (hl : HeaderLinked M pc reg done) (i : Fin 16)
    {c : Config w p r} (h : c.pc = pc i) :
    M.program.step c = (headerCode pc reg done i).run M.publicData c := by
  simp [Machine.program, h, hl i]

private theorem next_word (x : Word w) (n : ℕ) :
    x + (n : Word w) + 1 = x + ((n + 1 : ℕ) : Word w) := by simp [add_assoc]

/-- The header fragment has fixed instruction and probe counts on all
external words, including an empty row. -/
theorem header_native {pc : Fin 16 → Fin p} (hl : HeaderLinked M pc reg done)
    (m : Memory w) (c : Config w p r) (hc : c.pc = pc 0) :
    ∃ d, Prefix M m c d [] (headerEvents m (c.reg (reg 0)) (c.reg (reg 1))) ∧
      HeaderResult reg done m c d := by
  have path := ReadPrefix.tick (headerStep hl 0 hc)
    (ReadPrefix.tick (headerStep hl 1 rfl)
    (ReadPrefix.tick (headerStep hl 2 rfl)
    (ReadPrefix.read (m := m) _ (headerStep hl 3 rfl)
    (ReadPrefix.tick (headerStep hl 4 rfl)
    (ReadPrefix.read _ (headerStep hl 5 rfl)
    (ReadPrefix.tick (headerStep hl 6 rfl)
    (ReadPrefix.tick (headerStep hl 7 rfl)
    (ReadPrefix.read _ (headerStep hl 8 rfl)
    (ReadPrefix.tick (headerStep hl 9 rfl)
    (ReadPrefix.tick (headerStep hl 10 rfl)
    (ReadPrefix.tick (headerStep hl 11 rfl)
    (ReadPrefix.tick (headerStep hl 12 rfl)
    (ReadPrefix.read _ (headerStep hl 13 rfl)
    (ReadPrefix.tick (headerStep hl 14 rfl)
    (ReadPrefix.read _ (headerStep hl 15 rfl) (ReadPrefix.nil _))))))))))))))))
  let last {d : Config w p r} {es : List (Event w)} (_ : ReadPrefix M m c es d) := d
  have h17 : (17 : Word w) + 17 = 34 := (Nat.cast_add (R := Word w) 17 17).symm
  have h34 : c.reg (reg 0) + 34 + 1 = c.reg (reg 0) + 35 := next_word _ 34
  have h35 : c.reg (reg 0) + 35 + 1 = c.reg (reg 0) + 36 := next_word _ 35
  have h36 : c.reg (reg 0) + 36 + 1 = c.reg (reg 0) + 37 := next_word _ 36
  refine ⟨last path, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · intro fuel tail
    simpa (config := {decide := true}) only [headerEvents, fetch, last, Config.put,
      Function.update_apply, reg.injective.eq_iff, ↓reduceIte, BinaryOp.eval, h17, h34, h35, h36,
      List.nil_append] using ReadPrefix.execute path fuel tail
  all_goals try
    solve | simp (config := {decide := true}) [rowStart, count, last, Config.put,
      reg.injective.eq_iff, BinaryOp.eval, *]
  rintro a ⟨h₂,h₃,h₄,h₅,h₈,h₉,h₁₀⟩
  simp [last, Config.put, Function.update_of_ne, h₂,h₃,h₄,h₅,h₈,h₉,h₁₀]

/-- Fetch the current map ID, divide it by six to obtain motif and party,
and read the first word of that motif's selected term. The row cursor
is advanced by the enclosing loop. -/
def itemCode (pc : Fin 7 → Fin p) (reg : Fin 11 ↪ Fin r) (done : Fin p) :
    Fin 7 → Instr w p r k :=
  ![.readExternal (reg 6) (reg 2) (pc 1), .constant (reg 9) 6 (pc 2),
    .binary .mod (reg 7) (reg 6) (reg 9) (pc 3),
    .binary .div (reg 6) (reg 6) (reg 9) (pc 4),
    .binary .mul (reg 8) (reg 6) (reg 5) (pc 5),
    .binary .add (reg 8) (reg 4) (reg 8) (pc 6), .readExternal (reg 9) (reg 8) done]

theorem resize_itemCode (pc : Fin 7 → Fin p) (reg : Fin 11 ↪ Fin r) (done : Fin p) (i : Fin 7) :
    (itemCode (w := 3) (k := k) pc reg done i).resize w = itemCode pc reg done i := by
  fin_cases i <;> rfl

/-- The item reader returns directly to the native motif/party dispatch. -/
def ItemLinked (M : Machine w p r k) (pc : Fin 7 → Fin p) (reg : Fin 11 ↪ Fin r)
    (done : Fin p) : Prop := ∀ i, M.code (pc i) = itemCode pc reg done i

/-- The address calculated by the native division, multiply and add. -/
def termAddr (m : Memory w) (cursor term stride : Word w) : Word w :=
  term + BinaryOp.div.eval (m cursor.val) 6 * stride

/-- The item probe sequence is independent of the entered control table. -/
def itemEvents (m : Memory w) (cursor term stride : Word w) : List (Event w) :=
  [fetch m cursor, .tick, .tick, .tick, .tick, .tick, fetch m (termAddr m cursor term stride)]

theorem itemCost (m : Memory w) (cursor term stride : Word w) :
    (itemEvents m cursor term stride).length = 7 ∧
      countProbes (itemEvents m cursor term stride) = 2 ∧
      choiceBits (itemEvents m cursor term stride) = [] :=
  ⟨rfl,rfl,rfl⟩

/-- Outputs for one map, including the term-row base needed by the field reader. -/
structure ItemResult (reg : Fin 11 ↪ Fin r) (done : Fin p) (m : Memory w) (c d : Config w p r) :
    Prop where
  pc : d.pc = done
  motif : d.reg (reg 6) = BinaryOp.div.eval (m (c.reg (reg 2)).val) 6
  party : d.reg (reg 7) = BinaryOp.mod.eval (m (c.reg (reg 2)).val) 6
  term : d.reg (reg 8) = termAddr m (c.reg (reg 2)) (c.reg (reg 4)) (c.reg (reg 5))
  grid : d.reg (reg 9) = m (termAddr m (c.reg (reg 2)) (c.reg (reg 4)) (c.reg (reg 5))).val
  frame : ∀ a, (∀ i : Fin 11, 6 ≤ i.val → i.val ≤ 9 → a ≠ reg i) → d.reg a = c.reg a
  memory : d.privateMem = c.privateMem
  persistent : d.persistent = c.persistent

private theorem itemStep {pc : Fin 7 → Fin p} (hl : ItemLinked M pc reg done) (i : Fin 7)
    {c : Config w p r} (h : c.pc = pc i) :
    M.program.step c = (itemCode pc reg done i).run M.publicData c := by
  simp [Machine.program, h, hl i]

/-- Both item probes and the complete continuation state on arbitrary memory. -/
theorem item_native {pc : Fin 7 → Fin p} (hl : ItemLinked M pc reg done)
    (m : Memory w) (c : Config w p r) (hc : c.pc = pc 0) :
    ∃ d, Prefix M m c d [] (itemEvents m (c.reg (reg 2)) (c.reg (reg 4)) (c.reg (reg 5))) ∧
      ItemResult reg done m c d := by
  have path := ReadPrefix.read (m := m) _ (itemStep hl 0 hc)
    (ReadPrefix.tick (itemStep hl 1 rfl) (ReadPrefix.tick (itemStep hl 2 rfl)
    (ReadPrefix.tick (itemStep hl 3 rfl) (ReadPrefix.tick (itemStep hl 4 rfl)
    (ReadPrefix.tick (itemStep hl 5 rfl)
    (ReadPrefix.read _ (itemStep hl 6 rfl) (ReadPrefix.nil _)))))))
  let last {d : Config w p r} {es : List (Event w)} (_ : ReadPrefix M m c es d) := d
  refine ⟨last path, ?_, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · intro fuel tail
    simpa (config := {decide := true}) [itemEvents, fetch, last, termAddr, Config.put,
      reg.injective.eq_iff, BinaryOp.eval] using ReadPrefix.execute path fuel tail
  all_goals try
    solve | simp (config := {decide := true}) [last, termAddr, Config.put, reg.injective.eq_iff,
      BinaryOp.eval]
  intro a h
  simp [last, Config.put, Function.update_of_ne (h 6 (by decide) (by decide)),
    Function.update_of_ne (h 7 (by decide) (by decide)),
    Function.update_of_ne (h 8 (by decide) (by decide)),
    Function.update_of_ne (h 9 (by decide) (by decide))]

/-- The four published level fields in ordinary external-memory coordinates. -/
structure Published (m : Memory w) (level counts ids term : Word w) (stride : ℕ) : Prop where
  countsAt : m (level.val + 34) = counts
  idsAt : m (level.val + 35) = ids
  termAt : m (level.val + 36) = term
  strideAt : m (level.val + 37) = (stride : Word w)

private theorem val_add_nat (x : Word w) (n : ℕ) (fit : x.val + n < 2 ^ w) :
    (x + (n : Word w)).val = x.val + n := by
  rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : n < 2 ^ w), Nat.mod_eq_of_lt fit]

private theorem word_val (x : Word w) : (x.val : Word w) = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)

/-- The term publisher and the later data-head publisher retain the two
previously written map heads. The data-head publisher also retains both
words written by the term publisher. -/
theorem Published.of_head_frames {before terms last : Memory w} {level counts ids term : Word w}
    {stride : ℕ} (countWord : before (level.val + 34) = counts)
    (rowWord : before (level.val + 35) = ids)
    (termWord : terms (level.val + 36) = term)
    (strideWord : terms (level.val + 37) = (stride : Word w))
    (termFrame : ∀ x < level.val + 36, terms x = before x)
    (dataFrame : ∀ x < level.val + 40, last x = terms x) :
    Published last level counts ids term stride :=
  ⟨(dataFrame _ (by omega)).trans ((termFrame _ (by omega)).trans countWord),
    (dataFrame _ (by omega)).trans ((termFrame _ (by omega)).trans rowWord),
    (dataFrame _ (by omega)).trans termWord, (dataFrame _ (by omega)).trans strideWord⟩

/-- Later updates elsewhere in memory preserve the directory descriptor. -/
theorem Published.retain {m last : Memory w} {level counts ids term : Word w} {stride : ℕ}
    (pub : Published m level counts ids term stride)
    (keep : ∀ n, 34 ≤ n → n ≤ 37 → last (level.val + n) = m (level.val + n)) :
    Published last level counts ids term stride :=
  ⟨(keep 34 (by decide) (by decide)).trans pub.countsAt,
    (keep 35 (by decide) (by decide)).trans pub.idsAt,
    (keep 36 (by decide) (by decide)).trans pub.termAt,
    (keep 37 (by decide) (by decide)).trans pub.strideAt⟩

/-- Readback at a fitted header and count cell. Row cursor arithmetic is
word arithmetic, so the exclusive row end may coincide with the modulus. -/
theorem HeaderResult.readback {reg : Fin 11 ↪ Fin r} {done : Fin p}
    {m : Memory w} {c d : Config w p r} (h : HeaderResult reg done m c d)
    (counts ids term : Word w) (stride n : ℕ)
    (pub : Published m (c.reg (reg 0)) counts ids term stride)
    (headerFit : (c.reg (reg 0)).val + 37 < 2 ^ w)
    (countFit : counts.val + (c.reg (reg 1)).val < 2 ^ w)
    (value : (m (counts.val + (c.reg (reg 1)).val)).val = n) :
    let start := ids.val + (c.reg (reg 1)).val * n
    d.reg (reg 2) = (start : Word w) ∧ d.reg (reg 3) = ((start+n : ℕ) : Word w) ∧
      d.reg (reg 4) = term ∧ d.reg (reg 5) = (stride : Word w) := by
  let level := c.reg (reg 0)
  let site := c.reg (reg 1)
  have addr (i : ℕ) (hi : i ≤ 37) : (level + (i : Word w)).val = level.val + i :=
    val_add_nat level i (by change level.val + 37 < 2 ^ w at headerFit; omega)
  have countAddr : (counts + site).val = counts.val + site.val := by
    simpa only [word_val] using val_add_nat counts site.val countFit
  have hc : count m level site = (n : Word w) := by
    unfold count
    have h34 : (level + 34).val = level.val + 34 := addr 34 (by decide)
    rw [h34, pub.countsAt, countAddr, ← value, word_val]
  have row : rowStart m level site = ((ids.val + site.val*n : ℕ) : Word w) := by
    unfold rowStart
    have h35 : (level + 35).val = level.val + 35 := addr 35 (by decide)
    rw [h35, pub.idsAt, hc]
    simp only [Nat.cast_add, Nat.cast_mul, word_val]
  refine ⟨h.cursor.trans row, h.stop.trans ?_, h.term.trans ?_, h.stride.trans ?_⟩
  · change rowStart m level site + count m level site = _
    rw [row, hc]
    exact (Nat.cast_add ..).symm
  · exact (congrArg m (addr 36 (by decide))).trans pub.termAt
  · exact (congrArg m (addr 37 (by decide))).trans pub.strideAt

/-- On a genuine resident occurrence, native division and remainder recover
the motif ordinal and the six-valued party without truncation. The grid word
is read at the ordinary, fitted address in the selected term table. -/
theorem ItemResult.readback {reg : Fin 11 ↪ Fin r} {done : Fin p}
    {m : Memory w} {c d : Config w p r} (h : ItemResult reg done m c d)
    (ordinal : ℕ) (party : Fin 6) (base stride : ℕ) (h6 : 6 < 2 ^ w)
    (idAt : (m (c.reg (reg 2)).val).val = ordinal * 6 + party.val)
    (hbase : c.reg (reg 4) = (base : Word w)) (hstride : c.reg (reg 5) = (stride : Word w))
    (room : base + ordinal * stride < 2 ^ w) :
    (d.reg (reg 6)).val = ordinal ∧ (d.reg (reg 7)).val = party.val ∧
      (d.reg (reg 8)).val = base + ordinal * stride ∧
      d.reg (reg 9) = m (base + ordinal * stride) := by
  let id := m (c.reg (reg 2)).val
  have div : (BinaryOp.div.eval id 6).val = ordinal := by
    change id.val / (6 : Word w).val % (2 ^ w) = ordinal
    rw [show (6 : Word w).val = 6 from Nat.mod_eq_of_lt h6,
      Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt id.isLt)]
    change id.val = ordinal*6 + party.val at idAt
    rw [idAt]
    have := party.isLt
    omega
  have modEq : (BinaryOp.mod.eval id 6).val = party.val := by
    change id.val % (6 : Word w).val % (2 ^ w) = party.val
    rw [show (6 : Word w).val = 6 from Nat.mod_eq_of_lt h6,
      Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt id.isLt)]
    change id.val = ordinal*6 + party.val at idAt
    rw [idAt]
    have := party.isLt
    omega
  have hdiv : BinaryOp.div.eval id 6 = (ordinal : Word w) := by rw [← div, word_val]
  have ht : (termAddr m (c.reg (reg 2)) (c.reg (reg 4)) (c.reg (reg 5))).val =
      base + ordinal * stride := by
    change (c.reg (reg 4) + BinaryOp.div.eval id 6 * c.reg (reg 5)).val = _
    rw [hbase, hstride, hdiv, ← Nat.cast_mul, ← Nat.cast_add]
    exact Nat.mod_eq_of_lt room
  exact ⟨(congrArg Fin.val h.motif).trans div, (congrArg Fin.val h.party).trans modEq,
    (congrArg Fin.val h.term).trans ht, h.grid.trans (congrArg m ht)⟩

/-- Fixed slots occupied by both readers in the pair worker. -/
abbrev Address := Fin 16 ⊕ Fin 7

/-- The readers share the surrounding eleven public words and have no
private public-parameter bank of their own. Their exits link to the map
guard and selected map evaluator. -/
def text (place : Address → Fin p) (reg : Fin 11 ↪ Fin r) (guard dispatch : Fin p) :
    Address → Instr 5 p r 11
  | .inl i => headerCode (place ∘ Sum.inl) reg guard i
  | .inr i => itemCode (place ∘ Sum.inr) reg dispatch i

/-- Placing the fixed instruction slots supplies both native reader links. -/
theorem linked (M : Machine w p r 11) (place : Address → Fin p) (reg : Fin 11 ↪ Fin r)
    (guard dispatch : Fin p)
    (code : ∀ a, M.code (place a) = (text place reg guard dispatch a).resize w) :
    HeaderLinked M (place ∘ Sum.inl) reg guard ∧ ItemLinked M (place ∘ Sum.inr) reg dispatch := by
  constructor
  · intro i
    exact (code (.inl i)).trans (resize_headerCode ..)
  · intro i
    apply (code (.inr i)).trans
    fin_cases i <;> rfl

end PairSimulation.MapResidentInputs

end VPVNP
end Computability
end OAI
