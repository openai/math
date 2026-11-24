import OAI.Computability.VPVNP.MacaulayIndexISA
import OAI.Computability.VPVNP.MacaulayRowIndex

/-!
# Fixed binary control for a shifted coefficient row

The two input words hold the exponent blocks of the source monomial and
the coefficient column. They can use different radices. The program checks
every coordinate, reports equality and divisibility, and returns any requested
digit of the residual. Marking one label before scaling covers multiplication
by that label. A scalar multiplier also covers the Frobenius query.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.ExponentISA

open BurstRAM BurstRAM.PrivateRAM RAMTape.RegisterTable ISA

/-- Input registers store the source radix, column radix, multiplier, marked
coordinate and requested coordinate. Both coordinates use one-based numbers,
with zero disabling the mark or the requested output. -/
structure Parameters where
  /-- Radix used to extract a variable exponent from the source monomial. -/
  sourceBase : ℕ
  /-- Radix used to extract a variable exponent from the column monomial. -/
  columnBase : ℕ
  /-- Factor applied to each source exponent after adding the possible one-variable shift. -/
  scale : ℕ
  /-- One-based coordinate at which to increase the source exponent by one before scaling. Zero
  disables the shift. -/
  mark : ℕ
  /-- One-based coordinate of the exponent difference to retain. Zero requests no output digit. -/
  request : ℕ

/-- Register values maintained while comparing the shifted and scaled source exponents with the
column exponents. -/
structure Work where
  /-- Number of exponent digits still to compare. It also gives the one-based coordinate of the
  next low radix digit. -/
  remaining : ℕ
  /-- Unprocessed part of the source radix block after removing the low digits already visited. -/
  source : ℕ
  /-- Unprocessed part of the column radix block after removing the low digits already visited. -/
  column : ℕ
  /-- Stored column exponent minus the shifted source exponent at the requested coordinate,
  truncated at zero. -/
  residual : ℕ := 0
  /-- Running conjunction of the coordinatewise inequalities needed for the shifted and scaled
  source monomial to divide the column. -/
  divides : Bool := true
  /-- Running conjunction of the exponent equalities for the shifted and scaled source and the
  column. -/
  same : Bool := true
  /-- Current source exponent after the optional one-coordinate shift and scaling. -/
  sourceDigit : ℕ := 0
  /-- Current exponent extracted from the low digit of the column block. -/
  columnDigit : ℕ := 0

/-- Registers 5--12 hold the work record, and the last two hold one and zero. -/
def registers (w : ℕ) (p : Parameters) (s : Work) (j : Fin 15) : Word w :=
  word w <| match j.val with
  | 0 => p.sourceBase
  | 1 => p.columnBase
  | 2 => p.scale
  | 3 => p.mark
  | 4 => p.request
  | 5 => s.remaining
  | 6 => s.source
  | 7 => s.column
  | 8 => s.residual
  | 9 => s.divides.toNat
  | 10 => s.same.toNat
  | 11 => s.sourceDigit
  | 12 => s.columnDigit
  | 13 => 1
  | _ => 0

/-- Fixed 18-instruction register table that compares the two exponent blocks and retains the
requested residual digit. -/
def table : Template 18 15 0 where
  literalWidth := 1
  entry := 0
  code j := match j.val with
  | 0 => .jumpEq 5 14 17 1
  | 1 => .binary .mod 11 6 0 2
  | 2 => .binary .mod 12 7 1 3
  | 3 => .jumpEq 5 3 4 5
  | 4 => .binary .add 11 11 13 5
  | 5 => .binary .mul 11 2 11 6
  | 6 => .jumpLt 12 11 7 8
  | 7 => .constant 9 0 8
  | 8 => .jumpEq 11 12 10 9
  | 9 => .constant 10 0 10
  | 10 => .jumpEq 5 4 11 14
  | 11 => .jumpLt 12 11 12 13
  | 12 => .constant 8 0 14
  | 13 => .binary .sub 8 12 11 14
  | 14 => .binary .div 6 6 0 15
  | 15 => .binary .div 7 7 1 16
  | 16 => .binary .sub 5 5 13 0
  | _ => .accept

/-- Constraints used at the physical arithmetic and comparison instructions. -/
structure Fits (p : Parameters) (w : ℕ) : Prop where
  one_lt : 1 < 2^w
  source_pos : 0 < p.sourceBase
  column_pos : 0 < p.columnBase
  source_lt : p.sourceBase < 2^w
  column_lt : p.columnBase < 2^w
  scale_lt : p.scale < 2^w
  product_lt : p.scale*p.sourceBase < 2^w
  mark_lt : p.mark < 2^w
  request_lt : p.request < 2^w

/-- Execution of the exponent-comparison table for exactly n steps between the two indicated
control locations and work records. -/
abbrev Trace (w : ℕ) (p : Parameters) (n : ℕ) (pc : Fin 18) (s : Work) (pc' : Fin 18) (s' : Work) :=
  Runs table (Fin.elim0 : Fin 0 → Word w) 0 n pc (registers w p s) pc' (registers w p s')

private abbrev Block (w : ℕ) (p : Parameters) (n : ℕ) (pc : Fin 18) (s : Work) (pc' : Fin 18) (s' : Work) :=
  ∃ k ≤ n, Trace w p k pc s pc' s'

private theorem chain {w n m : ℕ} {p : Parameters} {pc pc' pc'' : Fin 18} {s t u : Work}
    (a : Block w p n pc s pc' t) (b : Block w p m pc' t pc'' u) : Block w p (n+m) pc s pc'' u := by
  obtain ⟨j,hj,hr⟩ := a
  obtain ⟨k,hk,hs⟩ := b
  exact ⟨_, Nat.add_le_add hj hk, hr.trans hs⟩

private theorem word_lt {w a b : ℕ} (ha : a < 2^w) (hb : b < 2^w) :
    word w a < word w b ↔ a < b := by simp [word, Fin.lt_def, Nat.mod_eq_of_lt, ha, hb]

private theorem eval_mul (w a b : ℕ) :
    BinaryOp.mul.eval (word w a) (word w b) = word w (a*b) := by
  apply Fin.ext
  simp only [BinaryOp.eval, word, Fin.val_mul, Fin.val_ofNat]
  exact (Nat.mul_mod ..).symm

private theorem eval_sub {w a b : ℕ} (ha : a < 2^w) (hb : b < 2^w) (hle : b ≤ a) :
    BinaryOp.sub.eval (word w a) (word w b) = word w (a-b) := by
  have hword : word w b ≤ word w a := le_of_not_gt (fun h => hle.not_gt ((word_lt ha hb).mp h))
  apply Fin.ext
  change (word w a - word w b).val = _
  rw [Fin.sub_val_of_le hword]
  simp [word, Nat.mod_eq_of_lt, ha, hb, (Nat.sub_le a b).trans_lt ha]

private theorem write_eq {w : ℕ} (p : Parameters) (s s' : Work) (i : Fin 15) (v : Word w)
    (hi : registers w p s' i = v) (hrest : ∀ j ≠ i, registers w p s j = registers w p s' j) :
    Function.update (registers w p s) i v = registers w p s' := by
  funext j
  by_cases h : j = i
  · subst j; simp [hi]
  · simp [Function.update_of_ne h, hrest j h]

local macro "writeReg" : tactic => `(tactic|
  (simp only [Option.some.injEq, Prod.mk.injEq, true_and]
   apply write_eq
   · rfl
   · intro j hj; fin_cases j <;> first | rfl | exact (hj rfl).elim))

private abbrev wordStep (w : ℕ) (p : Parameters) (j : Fin 18) (s : Work) :=
  step (table.code j) Fin.elim0 (0 : Word w) (registers w p s)

/-- Extract the low source digit, add one when the coordinate is marked, then multiply by the
query's scale. -/
def scaledDigit (p : Parameters) (position source : ℕ) : ℕ :=
  p.scale * (source % p.sourceBase + if position = p.mark then 1 else 0)

private def readDigits (p : Parameters) (s : Work) : Work :=
  {s with sourceDigit := scaledDigit p s.remaining s.source, columnDigit := s.column%p.columnBase}

private theorem read_block {w : ℕ} (p : Parameters) (h : Fits p w) (s : Work)
    (hr : 0 < s.remaining) (hrw : s.remaining < 2^w) (hs : s.source < 2^w) (hc : s.column < 2^w) :
    Block w p 6 0 s 6 (readDigits p s) := by
  let u := {s with sourceDigit := s.source%p.sourceBase}
  let v := {u with columnDigit := s.column%p.columnBase}
  have h₀ : wordStep w p 0 s = some (1, registers w p s) := by
    change some (if word w s.remaining = word w 0 then _ else _, _) = _
    simp [word_eq hrw (Nat.two_pow_pos _), hr.ne']
  have h₁ : wordStep w p 1 s = some (2, registers w p u) := by
    change some (2, Function.update (registers w p s) 11 (BinaryOp.mod.eval (word w s.source) (word w p.sourceBase))) = _
    rw [eval_mod hs h.source_lt]; writeReg
  have h₂ : wordStep w p 2 u = some (3, registers w p v) := by
    change some (3, Function.update (registers w p u) 12 (BinaryOp.mod.eval (word w s.column) (word w p.columnBase))) = _
    rw [eval_mod hc h.column_lt]; writeReg
  have h₃ : wordStep w p 3 v = some (if s.remaining = p.mark then 4 else 5, registers w p v) := by
    change some (if word w s.remaining = word w p.mark then _ else _, _) = _
    simp [word_eq hrw h.mark_lt]
  let marked := {v with sourceDigit := v.sourceDigit + (if s.remaining = p.mark then 1 else 0)}
  have hm : Block w p 2 3 v 5 marked := by
    by_cases he : s.remaining = p.mark
    · rw [ite_eq_left he] at h₃
      have h₄ : wordStep w p 4 v = some (5, registers w p marked) := by
        change some (5, Function.update (registers w p v) 11 (BinaryOp.add.eval (word w v.sourceDigit) (word w 1))) = _
        rw [eval_add]
        simp only [marked, ite_eq_left he]; writeReg
      exact ⟨2, le_rfl, .cons h₃ (.one h₄)⟩
    · rw [ite_eq_right he] at h₃
      have hh : marked = v := by simp [marked, he]
      rw [hh]
      exact ⟨1, by decide, Runs.one h₃⟩
  have h₅ : wordStep w p 5 marked = some (6, registers w p (readDigits p s)) := by
    change some (6, Function.update (registers w p marked) 11 (BinaryOp.mul.eval (word w p.scale) (word w marked.sourceDigit))) = _
    rw [eval_mul]; writeReg
  have hpre : Block w p 3 0 s 3 v := ⟨3, le_rfl, .cons h₀ (.cons h₁ (.one h₂))⟩
  exact chain (chain hpre hm) ⟨1, le_rfl, .one h₅⟩


private def compareDigits (s : Work) : Work :=
  {s with
    divides := s.divides && decide (s.sourceDigit ≤ s.columnDigit)
    same := s.same && decide (s.sourceDigit = s.columnDigit)}

private theorem compare_block {w : ℕ} (p : Parameters) (s : Work)
    (ha : s.sourceDigit < 2^w) (hb : s.columnDigit < 2^w) :
    Block w p 4 6 s 10 (compareDigits s) := by
  let u := {s with divides := s.divides && decide (s.sourceDigit ≤ s.columnDigit)}
  have h₆ : wordStep w p 6 s = some (if s.columnDigit < s.sourceDigit then 7 else 8, registers w p s) := by
    change some (if word w s.columnDigit < word w s.sourceDigit then _ else _, _) = _
    simp [word_lt hb ha]
  have hdiv : Block w p 2 6 s 8 u := by
    by_cases he : s.columnDigit < s.sourceDigit
    · rw [ite_eq_left he] at h₆
      have h₇ : wordStep w p 7 s = some (8, registers w p u) := by
        change some (8, Function.update (registers w p s) 9 (word w 0)) = _
        simp only [u, Nat.not_le_of_gt he, decide_false, Bool.and_false]
        writeReg
      exact ⟨2, le_rfl, .cons h₆ (.one h₇)⟩
    · rw [ite_eq_right he] at h₆
      have hu : u = s := by simp [u, Nat.le_of_not_gt he]
      rw [hu]
      exact ⟨1, by decide, .one h₆⟩
  have h₈ : wordStep w p 8 u = some (if s.sourceDigit = s.columnDigit then 10 else 9, registers w p u) := by
    change some (if word w s.sourceDigit = word w s.columnDigit then _ else _, _) = _
    simp [word_eq ha hb]
  have heq : Block w p 2 8 u 10 (compareDigits s) := by
    by_cases he : s.sourceDigit = s.columnDigit
    · rw [ite_eq_left he] at h₈
      have hh : compareDigits s = u := by simp [compareDigits, u, he]
      rw [hh]
      exact ⟨1, by decide, .one h₈⟩
    · rw [ite_eq_right he] at h₈
      have h₉ : wordStep w p 9 u = some (10, registers w p (compareDigits s)) := by
        change some (10, Function.update (registers w p u) 10 (word w 0)) = _
        simp only [compareDigits, he, decide_false, Bool.and_false]
        writeReg
      exact ⟨2, le_rfl, .cons h₈ (.one h₉)⟩
  exact chain hdiv heq

private def saveDigit (p : Parameters) (s : Work) : Work :=
  {s with residual := if s.remaining = p.request then s.columnDigit-s.sourceDigit else s.residual}

private theorem save_block {w : ℕ} (p : Parameters) (fit : Fits p w) (s : Work)
    (hr : s.remaining < 2^w) (ha : s.sourceDigit < 2^w) (hb : s.columnDigit < 2^w) :
    Block w p 3 10 s 14 (saveDigit p s) := by
  have h₁₀ : wordStep w p 10 s = some (if s.remaining = p.request then 11 else 14, registers w p s) := by
    change some (if word w s.remaining = word w p.request then _ else _, _) = _
    simp [word_eq hr fit.request_lt]
  by_cases he : s.remaining = p.request
  · rw [ite_eq_left he] at h₁₀
    have h₁₁ : wordStep w p 11 s = some (if s.columnDigit < s.sourceDigit then 12 else 13, registers w p s) := by
      change some (if word w s.columnDigit < word w s.sourceDigit then _ else _, _) = _
      simp [word_lt hb ha]
    by_cases hlt : s.columnDigit < s.sourceDigit
    · rw [ite_eq_left hlt] at h₁₁
      have h₁₂ : wordStep w p 12 s = some (14, registers w p (saveDigit p s)) := by
        change some (14, Function.update (registers w p s) 8 (word w 0)) = _
        simp only [saveDigit, ite_eq_left he, Nat.sub_eq_zero_of_le hlt.le]
        writeReg
      exact ⟨3, le_rfl, .cons h₁₀ (.cons h₁₁ (.one h₁₂))⟩
    · rw [ite_eq_right hlt] at h₁₁
      have h₁₃ : wordStep w p 13 s = some (14, registers w p (saveDigit p s)) := by
        change some (14, Function.update (registers w p s) 8 (BinaryOp.sub.eval (word w s.columnDigit)
          (word w s.sourceDigit))) = _
        rw [eval_sub hb ha (Nat.le_of_not_gt hlt)]
        simp only [saveDigit, ite_eq_left he]
        writeReg
      exact ⟨3, le_rfl, .cons h₁₀ (.cons h₁₁ (.one h₁₃))⟩
  · rw [ite_eq_right he] at h₁₀
    have hh : saveDigit p s = s := by simp [saveDigit, he]
    rw [hh]
    exact ⟨1, by decide, .one h₁₀⟩

private def advance (p : Parameters) (s : Work) : Work :=
  {s with
    remaining := s.remaining-1, source := s.source/p.sourceBase, column := s.column/p.columnBase}

private theorem advance_block {w : ℕ} (p : Parameters) (fit : Fits p w) (s : Work) {n : ℕ}
    (hr : s.remaining = n+1) (hrw : s.remaining < 2^w) (hs : s.source < 2^w) (hc : s.column < 2^w) :
    Trace w p 3 14 s 0 (advance p s) := by
  let u := {s with source := s.source/p.sourceBase}
  let v := {u with column := s.column/p.columnBase}
  have h₁₄ : wordStep w p 14 s = some (15, registers w p u) := by
    change some (15, Function.update (registers w p s) 6 (BinaryOp.div.eval (word w s.source) (word w p.sourceBase))) = _
    rw [eval_div hs fit.source_lt]; writeReg
  have h₁₅ : wordStep w p 15 u = some (16, registers w p v) := by
    change some (16, Function.update (registers w p u) 7 (BinaryOp.div.eval (word w s.column) (word w p.columnBase))) = _
    rw [eval_div hc fit.column_lt]; writeReg
  have h₁₆ : wordStep w p 16 v = some (0, registers w p (advance p s)) := by
    change some (0, Function.update (registers w p v) 5 (BinaryOp.sub.eval (word w s.remaining) (word w 1))) = _
    rw [hr, eval_sub_one (hr ▸ hrw) fit.one_lt]
    simp only [advance, hr, Nat.add_one_sub_one]
    writeReg
  exact .cons h₁₄ (.cons h₁₅ (.one h₁₆))

private def round (p : Parameters) (s : Work) : Work :=
  advance p (saveDigit p (compareDigits (readDigits p s)))

private theorem round_run {w : ℕ} (p : Parameters) (fit : Fits p w) (s : Work) {n : ℕ}
    (hr : s.remaining = n+1) (hrw : s.remaining < 2^w) (hs : s.source < 2^w) (hc : s.column < 2^w) :
    Block w p 16 0 s 0 (round p s) := by
  let u := readDigits p s
  let v := compareDigits u
  let z := saveDigit p v
  have hpre := read_block p fit s (by omega) hrw hs hc
  have hmod := Nat.mod_lt s.source fit.source_pos
  have ha : u.sourceDigit < 2^w := by
    apply lt_of_le_of_lt _ fit.product_lt
    apply Nat.mul_le_mul_left
    split <;> omega
  have hb : u.columnDigit < 2^w := (Nat.mod_lt _ fit.column_pos).trans fit.column_lt
  have hcmp := compare_block p u ha hb
  have hsave := save_block p fit v hrw ha hb
  have hnext := advance_block p fit z hr hrw hs hc
  exact chain (chain (chain hpre hcmp) hsave) ⟨3, le_rfl, hnext⟩

private def model (p : Parameters) : ℕ → Work → Work
  | 0, s => s
  | r+1, s => model p r (round p s)

private theorem model_run {w : ℕ} (p : Parameters) (fit : Fits p w) (s : Work) {r : ℕ}
    (hr : s.remaining = r) (hrw : s.remaining < 2^w) (hs : s.source < 2^w) (hc : s.column < 2^w) :
    Block w p (16*r+1) 0 s 17 (model p r s) := by
  induction r generalizing s with
  | zero =>
    refine ⟨1, by simp, .one ?_⟩
    change some (if word w s.remaining = word w 0 then _ else _, _) = _
    simp [hr, model]
  | succ r ih =>
    have hrr : (round p s).remaining = r := by change s.remaining-1 = r; omega
    have ht := ih (round p s) hrr (by omega) ((Nat.div_le_self ..).trans_lt hs) ((Nat.div_le_self ..).trans_lt hc)
    have hbody := round_run p fit s hr hrw hs hc
    rw [model]
    convert chain hbody ht using 1; omega


private def sourceAt (p : Parameters) (r a i : ℕ) :=
  scaledDigit p (r-i) (a / p.sourceBase^i)

private def columnAt (p : Parameters) (b i : ℕ) :=
  b / p.columnBase^i % p.columnBase

private theorem source_succ (p : Parameters) (r a i : ℕ) :
    sourceAt p (r+1) a (i+1) = sourceAt p r (a/p.sourceBase) i := by
  simp [sourceAt, pow_succ', Nat.div_div_eq_div_mul]

private theorem column_succ (p : Parameters) (b i : ℕ) :
    columnAt p b (i+1) = columnAt p (b/p.columnBase) i := by
  simp [columnAt, pow_succ', Nat.div_div_eq_div_mul]

private theorem forall_succ (P : ℕ → Prop) (n : ℕ) :
    (∀ i < n+1, P i) ↔ P 0 ∧ ∀ i < n, P (i+1) := by
  constructor
  · intro h; exact ⟨h 0 (by omega), fun i hi => h (i+1) (by omega)⟩
  · rintro ⟨hz, hs⟩ (_ | i) hi
    · exact hz
    · exact hs i (by omega)

private structure Answer (p : Parameters) (r : ℕ) (s out : Work) : Prop where
  divides : out.divides = true ↔ s.divides = true ∧ ∀ i < r, sourceAt p r s.source i ≤ columnAt p s.column i
  same : out.same = true ↔ s.same = true ∧ ∀ i < r, sourceAt p r s.source i = columnAt p s.column i
  read : ∀ i < r, p.request = r-i → out.residual = columnAt p s.column i - sourceAt p r s.source i
  keep : p.request = 0 ∨ r < p.request → out.residual = s.residual

private theorem model_answer (p : Parameters) (s : Work) {r : ℕ} (hr : s.remaining = r) :
    Answer p r s (model p r s) := by
  induction r generalizing s with
  | zero => exact ⟨by simp [model], by simp [model], by simp, fun _ => rfl⟩
  | succ r ih =>
    let z := round p s
    have hz : z.remaining = r := by change s.remaining-1 = r; omega
    have ans := ih z hz
    have hs (i) : sourceAt p r z.source i = sourceAt p (r+1) s.source (i+1) := (source_succ ..).symm
    have hc (i) : columnAt p z.column i = columnAt p s.column (i+1) := (column_succ ..).symm
    have hread : z.residual = if r+1 = p.request then
        columnAt p s.column 0 - sourceAt p (r+1) s.source 0 else s.residual := by
      simp [z, round, advance, saveDigit, compareDigits, readDigits, hr, sourceAt, columnAt]
    rw [model]
    constructor
    · rw [ans.divides, forall_succ]
      simp only [hs, hc]
      change ((s.divides && decide (scaledDigit p s.remaining s.source ≤ s.column % p.columnBase)) = true ∧ _) ↔ _
      simp [hr, sourceAt, columnAt, and_assoc]
    · rw [ans.same, forall_succ]
      simp only [hs, hc]
      change ((s.same && decide (scaledDigit p s.remaining s.source = s.column % p.columnBase)) = true ∧ _) ↔ _
      simp [hr, sourceAt, columnAt, and_assoc]
    · rintro (_ | i) hi hreq
      · have he : p.request = r+1 := by simpa using hreq
        rw [ans.keep (Or.inr (by omega)), hread, ite_eq_left he.symm]
      · rw [← hs, ← hc]
        exact ans.read i (by omega) (by omega)
    · intro hreq
      have hne : r+1 ≠ p.request := by omega
      rw [ans.keep (by omega), hread, ite_eq_right hne]

/-- The scalar row test, including the returned exponent at one arbitrary
label, runs on a fixed binary stack machine. -/
theorem run_digits {w t : ℕ} (p : Parameters) (fit : Fits p w) (source column : ℕ)
    (ht : t < 2^w) (ha : source < 2^w) (hb : column < 2^w) :
    let input : Work := ⟨t,source,column,0,true,true,0,0⟩
    ∃ ticks ≤ (16*t+1)*(RAMTape.ISA.prepareBound w 0+3), ∃ out,
      UniversalCountStack.SpaceRun (code table) (w+(RAMTape.ISA.prepareBound w 0+3)) ticks
        (RAMTape.ISA.entry table 0) (bank Fin.elim0 0 (registers w p input))
        (RAMTape.ISA.entry table 17) (bank Fin.elim0 0 (registers w p out)) ∧
      (out.divides = true ↔ ∀ i < t, scaledDigit p (t-i) (source/p.sourceBase^i) ≤ column/p.columnBase^i%p.columnBase) ∧
      (out.same = true ↔ ∀ i < t, scaledDigit p (t-i) (source/p.sourceBase^i) = column/p.columnBase^i%p.columnBase) ∧
      ∀ i < t, p.request = t-i → out.residual =
        column/p.columnBase^i%p.columnBase - scaledDigit p (t-i) (source/p.sourceBase^i) := by
  intro input
  obtain ⟨n,hn,hr⟩ := model_run p fit input rfl ht ha hb
  obtain ⟨ticks,hticks,hphys⟩ := run hr
  have ans := model_answer p input rfl
  exact ⟨ticks,hticks.trans (Nat.mul_le_mul_right _ hn), _, hphys,
    by simpa [input, sourceAt, columnAt] using ans.divides,
    by simpa [input, sourceAt, columnAt] using ans.same, ans.read⟩

end RadicalCertificate.MonomialIndex.ExponentISA

end VPVNP
end Computability
end OAI
