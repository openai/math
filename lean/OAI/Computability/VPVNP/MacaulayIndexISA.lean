import OAI.Computability.VPVNP.RegisterTable
import OAI.Computability.VPVNP.GradedMonomialIndex

/-!
# Fixed register program for a dense monomial ordinal

The program enumerates raw graded radix keys in increasing order. At a key it
divides the exponent block by its radix exactly once per label and tests the
digit sum against the outer degree. A selected ordinal returns the raw key.
With the requested ordinal equal to the upper scan limit it returns the count
instead. The instruction table and number of registers are independent of the
degree bound and the number of variables.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.ISA

open BurstRAM BurstRAM.PrivateRAM RAMTape.RegisterTable

/-- The read-only registers, followed by cursor, count, remaining digits,
residual value, digit sum, scratch, one and zero. -/
def table : Template 15 13 0 where
  literalWidth := 1
  entry := 0
  code pc := match pc.val with
    | 0 => .jumpEq 5 3 14 1
    | 1 => .binary .mod 8 5 2 2
    | 2 => .copy 7 1 3
    | 3 => .constant 9 0 4
    | 4 => .jumpEq 7 12 9 5
    | 5 => .binary .mod 10 8 0 6
    | 6 => .binary .add 9 9 10 7
    | 7 => .binary .div 8 8 0 8
    | 8 => .binary .sub 7 7 11 4
    | 9 => .binary .div 10 5 2 10
    | 10 => .jumpEq 9 10 11 13
    | 11 => .jumpEq 6 4 14 12
    | 12 => .binary .add 6 6 11 13
    | 13 => .binary .add 5 5 11 0
    | _ => .accept

/-- The lower and upper radix blocks fit in one register each. -/
structure Parameters where
  /-- Radix for the digits encoding individual variable exponents. -/
  base : ℕ
  /-- Number of variables and hence the number of digits inspected in each candidate key. -/
  arity : ℕ
  /-- Size of the low radix block. Division by this value recovers the total-degree tag. -/
  box : ℕ
  /-- Exclusive upper bound on the raw keys visited by the monomial scan. -/
  limit : ℕ
  /-- Zero-based rank of the valid monomial to return. Using the scan limit as the requested
  rank makes the program count all valid keys. -/
  ordinal : ℕ

/-- Mutable register values of the scan through graded monomial keys. -/
structure Work where
  /-- Raw key currently under consideration, or the exclusive endpoint after exhausting the
  scan. -/
  cursor : ℕ := 0
  /-- Number of valid keys strictly below the cursor. -/
  count : ℕ := 0
  /-- Number of variable digits still to examine for the current candidate. -/
  remaining : ℕ := 0
  /-- Unprocessed suffix of the candidate's low radix block, divided by the radix after each
  digit. -/
  value : ℕ := 0
  /-- Sum of the variable exponent digits examined for the current candidate. -/
  total : ℕ := 0
  /-- Temporary register for an extracted digit or the total-degree tag used in the final
  comparison. -/
  scratch : ℕ := 0

/-- Encode a natural number as a register word modulo two to the power w. -/
def word (w a : ℕ) : Word w := Fin.ofNat _ a

/-- Lay out the five scan parameters, six work values, one and zero in the thirteen hardware
registers. -/
def registers (w : ℕ) (p : Parameters) (s : Work) (j : Fin 13) : Word w :=
  word w <| match j.val with
  | 0 => p.base
  | 1 => p.arity
  | 2 => p.box
  | 3 => p.limit
  | 4 => p.ordinal
  | 5 => s.cursor
  | 6 => s.count
  | 7 => s.remaining
  | 8 => s.value
  | 9 => s.total
  | 10 => s.scratch
  | 11 => 1
  | _ => 0

theorem word_eq {w a b : ℕ} (ha : a < 2^w) (hb : b < 2^w) :
    word w a = word w b ↔ a = b := by simp [word, Fin.ext_iff, Nat.mod_eq_of_lt, ha, hb]

theorem eval_add (w a b : ℕ) :
    BinaryOp.add.eval (word w a) (word w b) = word w (a+b) := by
  apply Fin.ext
  simp only [BinaryOp.eval, word, Fin.val_add, Fin.val_ofNat]
  exact (Nat.add_mod ..).symm

theorem eval_mod {w a b : ℕ} (ha : a < 2^w) (hb : b < 2^w) :
    BinaryOp.mod.eval (word w a) (word w b) = word w (a%b) := by
  simp [BinaryOp.eval, word, Nat.mod_eq_of_lt, ha, hb]

theorem eval_div {w a b : ℕ} (ha : a < 2^w) (hb : b < 2^w) :
    BinaryOp.div.eval (word w a) (word w b) = word w (a/b) := by
  simp [BinaryOp.eval, word, Nat.mod_eq_of_lt, ha, hb]

theorem eval_sub_one {w a : ℕ} (ha : a+1 < 2^w) (hw : 1 < 2^w) :
    BinaryOp.sub.eval (word w (a+1)) (word w 1) = word w a := by
  apply Fin.ext
  simp only [BinaryOp.eval, word, Fin.val_sub, Fin.val_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hw]
  have h : 2^w - 1 + (a+1) = a + 2^w := by omega
  simp [h]

/-- Execution of the graded-key scanner for exactly n instructions between the two indicated
control locations and register configurations. -/
abbrev Trace (w : ℕ) (p : Parameters) (n : ℕ) (pc : Fin 15) (s : Work) (pc' : Fin 15) (s' : Work) :=
  Runs table (Fin.elim0 : Fin 0 → Word w) 0 n pc (registers w p s) pc' (registers w p s')

private theorem write_eq {w : ℕ} (p : Parameters) (s s' : Work) (i : Fin 13) (v : Word w)
    (hi : registers w p s' i = v)
    (hrest : ∀ j ≠ i, registers w p s j = registers w p s' j) :
    Function.update (registers w p s) i v = registers w p s' := by
  funext j
  by_cases h : j = i
  · subst j; simp [hi]
  · simp [Function.update_of_ne h, hrest j h]

private abbrev wordStep (w : ℕ) (p : Parameters) (pc : Fin 15) (s : Work) :=
  step (table.code pc) Fin.elim0 (0 : Word w) (registers w p s)

private theorem digit_round {w : ℕ} (p : Parameters) (s : Work) {r : ℕ}
    (hr : s.remaining = r+1) (hrem : r+1 < 2^w) (hbase : p.base < 2^w)
    (hv : s.value < 2^w) (hw : 1 < 2^w) :
    Trace w p 5 4 s 4 {s with
      remaining := r, value := s.value/p.base
      total := s.total + s.value%p.base, scratch := s.value%p.base} := by
  let s₁ := {s with scratch := s.value % p.base}
  let s₂ := {s₁ with total := s.total + s.value % p.base}
  let s₃ := {s₂ with value := s.value / p.base}
  let s₄ := {s₃ with remaining := r}
  have h₀ : wordStep w p 4 s = some (5, registers w p s) := by
    change some (if word w s.remaining = word w 0 then _ else _, _) = _
    simp [hr, word_eq hrem (Nat.two_pow_pos _)]
  have h₁ : wordStep w p 5 s = some (6, registers w p s₁) := by
    change some (6, Function.update (registers w p s) 10 (BinaryOp.mod.eval (word w s.value) (word w p.base))) = _
    rw [eval_mod hv hbase]
    apply congrArg (fun R => some ((6 : Fin 15), R))
    apply write_eq
    · rfl
    · intro j hj; fin_cases j <;> first | rfl | exact (hj rfl).elim
  have h₂ : wordStep w p 6 s₁ = some (7, registers w p s₂) := by
    change some (7, Function.update (registers w p s₁) 9 (BinaryOp.add.eval (word w s.total) (word w (s.value%p.base)))) = _
    rw [eval_add]
    apply congrArg (fun R => some ((7 : Fin 15), R))
    apply write_eq
    · rfl
    · intro j hj; fin_cases j <;> first | rfl | exact (hj rfl).elim
  have h₃ : wordStep w p 7 s₂ = some (8, registers w p s₃) := by
    change some (8, Function.update (registers w p s₂) 8 (BinaryOp.div.eval (word w s.value) (word w p.base))) = _
    rw [eval_div hv hbase]
    apply congrArg (fun R => some ((8 : Fin 15), R))
    apply write_eq
    · rfl
    · intro j hj; fin_cases j <;> first | rfl | exact (hj rfl).elim
  have h₄ : wordStep w p 8 s₃ = some (4, registers w p s₄) := by
    change some (4, Function.update (registers w p s₃) 7 (BinaryOp.sub.eval (word w s.remaining) (word w 1))) = _
    rw [hr, eval_sub_one hrem hw]
    apply congrArg (fun R => some ((4 : Fin 15), R))
    apply write_eq
    · rfl
    · intro j hj; fin_cases j <;> first | rfl | exact (hj rfl).elim
  exact .cons h₀ (.cons h₁ (.cons h₂ (.cons h₃ (.one h₄))))

/-- Sum the indicated number of least significant base digits, counting leading zeros if
necessary. -/
def digitSum (base : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, v => v%base + digitSum base n (v/base)

private theorem digitSum_eq (base n v : ℕ) :
    digitSum base n v = ∑ i : Fin n, v / base^i.val % base := by
  induction n generalizing v with
  | zero => simp [digitSum]
  | succ n ih =>
    simp [digitSum, ih, Fin.sum_univ_succ, pow_succ', Nat.div_div_eq_div_mul]

private theorem admissible_eq_digitSum (t D : ℕ) (c : Fin (rawSize t D)) :
    admissible c = decide (digitSum (D+1) t (c.val % (D+1)^t) = c.val / (D+1)^t) := by
  change decide ((∑ i : Fin t, c.val % (D+1)^t / (D+1)^i.rev.val % (D+1)) = _) = _
  rw [digitSum_eq, ← Fin.revPerm.sum_comp]
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  rfl
  simp


/-- Width conditions for the scalar scans and the digit-sum comparison. -/
structure Fits (p : Parameters) (w : ℕ) : Prop where
  one_lt : 1 < 2^w
  base_pos : 0 < p.base
  base_lt : p.base < 2^w
  arity_lt : p.arity < 2^w
  box_lt : p.box < 2^w
  limit_lt : p.limit < 2^w
  ordinal_lt : p.ordinal < 2^w
  sum_lt : p.arity * (p.base-1) < 2^w

private theorem digitSum_le (b n v : ℕ) (hb : 0 < b) : digitSum b n v ≤ n*(b-1) := by
  induction n generalizing v with
  | zero => simp [digitSum]
  | succ n ih =>
    have := ih (v/b)
    have := Nat.mod_lt v hb
    rw [digitSum, Nat.succ_mul]
    omega

private theorem digit_loop {w : ℕ} (p : Parameters) (fit : Fits p w) (s : Work) {r : ℕ}
    (hr : s.remaining = r) (hrem : r < 2^w) (hv : s.value < 2^w) :
    ∃ out, Trace w p (5*r+1) 4 s 9 out ∧ out.cursor = s.cursor ∧ out.count = s.count ∧
      out.total = s.total + digitSum p.base r s.value := by
  induction r generalizing s with
  | zero =>
    refine ⟨s, .one ?_, rfl, rfl, by simp [digitSum]⟩
    change some (if word w s.remaining = word w 0 then _ else _, _) = _
    simp [hr]
  | succ r ih =>
    let next := {s with
      remaining := r, value := s.value/p.base
      total := s.total + s.value%p.base, scratch := s.value%p.base}
    have hround := digit_round p s hr hrem fit.base_lt hv fit.one_lt
    obtain ⟨out, htail, hc, hn, he⟩ := ih next rfl (by omega) ((Nat.div_le_self ..).trans_lt hv)
    refine ⟨out, ?_, hc, hn, ?_⟩
    · convert hround.trans htail using 1; omega
    · simpa [next, digitSum, Nat.add_assoc] using he

local macro "writeReg" : tactic => `(tactic|
  (simp only [Option.some.injEq, Prod.mk.injEq, true_and]
   apply write_eq
   · rfl
   · intro j hj; fin_cases j <;> first | rfl | exact (hj rfl).elim))

private theorem setup {w : ℕ} (p : Parameters) (fit : Fits p w) (s : Work) (hc : s.cursor < p.limit) :
    Trace w p 4 0 s 4 {s with value := s.cursor%p.box, remaining := p.arity, total := 0} := by
  let s₁ := {s with value := s.cursor%p.box}
  let s₂ := {s₁ with remaining := p.arity}
  let s₃ := {s₂ with total := 0}
  have h₀ : wordStep w p 0 s = some (1, registers w p s) := by
    change some (if word w s.cursor = word w p.limit then _ else _, _) = _
    simp [word_eq (hc.trans fit.limit_lt) fit.limit_lt, hc.ne]
  have h₁ : wordStep w p 1 s = some (2, registers w p s₁) := by
    change some (2, Function.update (registers w p s) 8 (BinaryOp.mod.eval (word w s.cursor) (word w p.box))) = _
    rw [eval_mod (hc.trans fit.limit_lt) fit.box_lt]
    writeReg
  have h₂ : wordStep w p 2 s₁ = some (3, registers w p s₂) := by
    change some (3, Function.update (registers w p s₁) 7 (word w p.arity)) = _
    writeReg
  have h₃ : wordStep w p 3 s₂ = some (4, registers w p s₃) := by
    change some (4, Function.update (registers w p s₂) 9 (word w 0)) = _
    writeReg
  exact .cons h₀ (.cons h₁ (.cons h₂ (.one h₃)))

/-- A raw key is accepted precisely when the digit sum of its low block equals the total degree
in its high block. -/
def validKey (p : Parameters) (c : ℕ) : Bool :=
  decide (digitSum p.base p.arity (c%p.box) = c/p.box)

private theorem test_run {w : ℕ} (p : Parameters) (fit : Fits p w) (s : Work) (hc : s.cursor < p.limit) :
    ∃ out, Trace w p (5*p.arity+7) 0 s (if validKey p s.cursor then 11 else 13) out ∧
      out.cursor = s.cursor ∧ out.count = s.count := by
  let initial := {s with value := s.cursor%p.box, remaining := p.arity, total := 0}
  have hbegin := setup p fit s hc
  obtain ⟨mid, hm, hmcur, hmcount, hmsum⟩ := digit_loop p fit initial rfl fit.arity_lt
    ((Nat.mod_le _ _).trans_lt (hc.trans fit.limit_lt))
  change mid.cursor = s.cursor at hmcur
  change mid.total = 0 + digitSum p.base p.arity (s.cursor%p.box) at hmsum
  rw [Nat.zero_add] at hmsum
  let out := {mid with scratch := s.cursor/p.box}
  have h₉ : wordStep w p 9 mid = some (10, registers w p out) := by
    change some (10, Function.update (registers w p mid) 10 (BinaryOp.div.eval (word w mid.cursor) (word w p.box))) = _
    rw [hmcur, eval_div (hc.trans fit.limit_lt) fit.box_lt]
    writeReg
  have h₁₀ : wordStep w p 10 out = some (if validKey p s.cursor then 11 else 13, registers w p out) := by
    change some (if word w mid.total = word w (s.cursor/p.box) then _ else _, _) = _
    simp [hmsum, validKey, word_eq ((digitSum_le p.base p.arity (s.cursor%p.box) fit.base_pos).trans_lt fit.sum_lt)
      ((Nat.div_le_self ..).trans_lt (hc.trans fit.limit_lt))]
  refine ⟨out, ?_, hmcur, hmcount⟩
  have htail : Trace w p 2 9 mid (if validKey p s.cursor then 11 else 13) out := .cons h₉ (.one h₁₀)
  change Trace w p (5*p.arity+1) 4 initial 9 mid at hm
  convert (hbegin.trans hm).trans htail using 1; omega

private theorem bump_cursor (w : ℕ) (p : Parameters) (s : Work) :
    Trace w p 1 13 s 0 {s with cursor := s.cursor+1} := by
  apply Runs.one
  change some (0, Function.update (registers w p s) 5 (BinaryOp.add.eval (word w s.cursor) (word w 1))) = _
  rw [eval_add]; writeReg

private theorem bump_count (w : ℕ) (p : Parameters) (s : Work) :
    Trace w p 1 12 s 13 {s with count := s.count+1} := by
  apply Runs.one
  change some (13, Function.update (registers w p s) 6 (BinaryOp.add.eval (word w s.count) (word w 1))) = _
  rw [eval_add]; writeReg

private theorem check_ordinal {w : ℕ} (p : Parameters) (fit : Fits p w) (s : Work) (hn : s.count < 2^w) :
    Trace w p 1 11 s (if s.count = p.ordinal then 14 else 12) s := by
  apply Runs.one
  change some (if word w s.count = word w p.ordinal then _ else _, _) = _
  simp [word_eq hn fit.ordinal_lt]


/-- The return address is either the end of the range or the valid raw
address whose exclusive prefix count equals the requested ordinal. -/
structure Result (p : Parameters) (out : Work) : Prop where
  cursor_le : out.cursor ≤ p.limit
  count_eq : out.count = countCodes (validKey p) out.cursor
  count_le : out.count ≤ p.ordinal
  stopped : out.cursor = p.limit ∨ validKey p out.cursor = true ∧ out.count = p.ordinal

private theorem scan {w : ℕ} (p : Parameters) (fit : Fits p w) (rem : ℕ) (s : Work)
    (hc : s.cursor + rem = p.limit) (hn : s.count = countCodes (validKey p) s.cursor)
    (hk : s.count ≤ p.ordinal) :
    ∃ steps ≤ rem*(5*p.arity+10)+1, ∃ out, Trace w p steps 0 s 14 out ∧ Result p out := by
  induction rem generalizing s with
  | zero =>
    simp only [Nat.add_zero] at hc
    refine ⟨1, by simp, s, .one ?_, ⟨hc.le, hn, hk, Or.inl hc⟩⟩
    change some (if word w s.cursor = word w p.limit then _ else _, _) = _
    simp [hc]
  | succ rem ih =>
    obtain ⟨mid, htest, hmcur, hmcount⟩ := test_run p fit s (by omega)
    have hstep : countCodes (validKey p) (s.cursor+1) = countCodes (validKey p) s.cursor +
        if validKey p s.cursor then 1 else 0 := by rw [countCodes_eq, countCodes_eq, Nat.count_succ]
    have clock {b : ℕ} (hb : b ≤ rem*(5*p.arity+10)+1) :
        (5*p.arity+10)+b ≤ (rem+1)*(5*p.arity+10)+1 := by rw [Nat.succ_mul rem (5*p.arity+10)]; omega
    by_cases hv : validKey p s.cursor = true
    · simp only [ite_eq_left hv] at htest
      have hcheck := check_ordinal p fit mid (hmcount.trans_le hk |>.trans_lt fit.ordinal_lt)
      by_cases he : mid.count = p.ordinal
      · simp only [ite_eq_left he] at hcheck
        refine ⟨_, ?_, mid, htest.trans hcheck, ⟨by omega, hmcur ▸ hmcount.trans hn, he.le, Or.inr ?_⟩⟩
        · have := clock (Nat.zero_le (rem*(5*p.arity+10)+1))
          omega
        · exact ⟨hmcur ▸ hv, he⟩
      · simp only [ite_eq_right he] at hcheck
        let counted := {mid with count := mid.count+1}
        let next := {counted with cursor := counted.cursor+1}
        have hcnt := bump_count w p mid
        have hcur := bump_cursor w p counted
        have hn' : next.count = countCodes (validKey p) next.cursor := by
          change mid.count + 1 = countCodes _ (mid.cursor+1)
          rw [hmcur, hmcount, hn, hstep, ite_eq_left hv]
        obtain ⟨b,hb,out,ht,hr⟩ := ih next (by change mid.cursor+1+rem = _; omega) hn'
          (by change mid.count+1 ≤ _; omega)
        refine ⟨_, ?_, out, (((htest.trans hcheck).trans hcnt).trans hcur).trans ht, hr⟩
        have := clock hb
        omega
    · simp only [ite_eq_right hv] at htest
      let next := {mid with cursor := mid.cursor+1}
      have hcur := bump_cursor w p mid
      have hn' : next.count = countCodes (validKey p) next.cursor := by
        change mid.count = countCodes _ (mid.cursor+1)
        rw [hmcur, hmcount, hn, hstep, ite_eq_right hv, Nat.add_zero]
      obtain ⟨b,hb,out,ht,hr⟩ := ih next (by change mid.cursor+1+rem = _; omega) hn'
        (hmcount.trans_le hk)
      refine ⟨_, ?_, out, (htest.trans hcur).trans ht, hr⟩
      have := clock hb
      omega

/-- The actual bit-stack control has polynomial height even when the
number of raw addresses scanned is exponential. -/
theorem scan_physical {w : ℕ} (p : Parameters) (fit : Fits p w) :
    ∃ ticks ≤ (p.limit*(5*p.arity+10)+1)*(RAMTape.ISA.prepareBound w 0+3), ∃ out, Result p out ∧
      UniversalCountStack.SpaceRun (RAMTape.RegisterTable.code table) (w+(RAMTape.ISA.prepareBound w 0+3)) ticks
        (RAMTape.ISA.entry table 0) (bank Fin.elim0 0 (registers w p {}))
        (RAMTape.ISA.entry table 14) (bank Fin.elim0 0 (registers w p out)) := by
  obtain ⟨n,hn,out,hr,hout⟩ := scan p fit p.limit {} (Nat.zero_add _) (by simp [countCodes_eq]) (Nat.zero_le _)
  obtain ⟨ticks,ht,hphys⟩ := run hr
  exact ⟨ticks, ht.trans (Nat.mul_le_mul_right _ hn), out, hout, hphys⟩

/-- The concrete register input for a graded key scan. -/
def graded (t D ordinal : ℕ) : Parameters := ⟨D+1, t, (D+1)^t, rawSize t D, ordinal⟩

private theorem graded_test (t D ordinal : ℕ) (c : Fin (rawSize t D)) :
    validKey (graded t D ordinal) c.val = admissible c := (admissible_eq_digitSum t D c).symm

private theorem count_congr {p q : ℕ → Bool} (n : ℕ) (h : ∀ i < n, p i = q i) :
    countCodes p n = countCodes q n := by
  induction n with
  | zero => simp [countCodes_eq]
  | succ n ih =>
    have he := ih (fun i hi => h i (hi.trans (Nat.lt_succ_self _)))
    simp only [countCodes_eq] at he ⊢
    rw [Nat.count_succ, Nat.count_succ, he, h n (Nat.lt_succ_self _)]

private theorem graded_count (t D ordinal : ℕ) {n : ℕ} (hn : n ≤ rawSize t D) :
    countCodes (validKey (graded t D ordinal)) n =
      countCodes (fun c => if h : c < rawSize t D then admissible ⟨c,h⟩ else false) n := by
  apply count_congr
  intro i hi
  have hr := hi.trans_le hn
  simpa only [dite_eq_left hr] using graded_test t D ordinal ⟨i,hr⟩

theorem count_result {t D : ℕ} {out : Work} (h : Result (graded t D (rawSize t D)) out) :
    out.cursor = rawSize t D ∧ out.count = size t D := by
  have he : out.cursor = rawSize t D := by
    rcases h.stopped with he | ⟨_,he⟩
    · exact he
    · have hh := (Nat.count_le (p := fun i => validKey (graded t D (rawSize t D)) i = true) (n := out.cursor))
      rw [← countCodes_eq, ← h.count_eq, he] at hh
      exact h.cursor_le.antisymm hh
  refine ⟨he, ?_⟩
  rw [h.count_eq, he, graded_count _ _ _ le_rfl]
  rfl

theorem ordinal_result {t D : ℕ} {k : Fin (size t D)} {out : Work}
    (h : Result (graded t D k) out) :
    out.cursor = (rawCode (enumeration t D k)).val ∧ out.count = k.val := by
  have hlen : countCodes (validKey (graded t D k)) (rawSize t D) = size t D := by
    rw [graded_count _ _ _ le_rfl]; rfl
  have hlt : out.cursor < rawSize t D := by
    apply lt_of_le_of_ne h.cursor_le
    intro he
    have hn := h.count_eq
    change out.cursor = rawSize t D at he
    rw [he, hlen] at hn
    exact (Nat.not_lt_of_ge (hn.symm.trans_le h.count_le)) k.isLt
  obtain ⟨hv,hk⟩ := h.stopped.resolve_left (Nat.ne_of_lt hlt)
  let m := enumeration t D k
  let c := rawCode m
  have hvalid : validKey (graded t D k) c.val = true := (graded_test t D k c).trans (admissible_rawCode m)
  have hc : countCodes (validKey (graded t D k)) c.val = k.val := by
    rw [graded_count _ _ _ c.isLt.le]
    have he := congrArg Fin.val ((enumeration t D).symm_apply_apply k)
    exact he
  refine ⟨Nat.count_injective (p := fun i => validKey (graded t D k) i = true) hv hvalid ?_, hk⟩
  rw [← countCodes_eq, ← countCodes_eq, ← h.count_eq, hk, hc]
  rfl

end RadicalCertificate.MonomialIndex.ISA

end VPVNP
end Computability
end OAI
