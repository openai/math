import OAI.Computability.VPVNP.SliceArithmeticHornerPrepare
import OAI.Computability.VPVNP.SliceArithmeticRound

/-!
# Uniform bit-stack multiplication in the advised polynomial basis

One finite instruction table reads a stack of Horner digits, runs a complete
coefficient scan for each digit and installs the resulting accumulator. Its
control is independent of the prime, extension degree and register width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.HornerControl

open RAMTape BurstRAM SliceArithmeticStreamRow
open SliceArithmeticRound (packed registers packed_length)

variable {p e w : ℕ} [NeZero p]

private abbrev RowAcc := SliceArithmeticRound.Acc

/-- A digit body stages its input, runs the coefficient scan and restores the accumulator. -/
def digitRoutine : FiniteRoutine Ports :=
  (prepare.followedBy (SliceArithmeticRound.scan Extra.rows)).followedBy restore

/-- Consume one round marker per Horner digit and execute a complete coefficient scan for each
digit. -/
def machine : FiniteRoutine Ports := FiniteRoutine.repeatMarked (.inr (.outer .rounds)) digitRoutine

/-- Cost of the preparation, inner scan and output reversal. -/
def digitCap (e w : ℕ) : ℕ :=
  5 * (e*w + e*w + e) + 13*w + 11 + 200*(w+1)^2 +
    (e*(800*(w+1)^2 + 22*w + 10) + 1) + (2*(e*w) + 1)

private structure Logical (p e : ℕ) where
  vector : Vector p e
  lastDigit : Fin p
  reduction : Fin p
  row : RowAcc p

private def top (v : Vector p e) := (List.ofFn v).getLastD 0

private def rowState (s : Logical p e) : RowAcc p := {s.row with result := top s.vector, output := []}

private def regState (w : ℕ) (s : Logical p e) :=
  registers w s.lastDigit s.reduction (rowState s)

private def resetRow (s : Logical p e) : RowAcc p := {rowState s with previous := 0}

private def items (c b v : Vector p e) :=
  List.ofFn (fun i => SliceArithmeticRound.Item.mk (v i) (c i) (b i))

private def advance (c b : Vector p e) (s : Logical p e) (digit : Fin p) : Logical p e :=
  let red := -top s.vector
  let result := (items c b s.vector).foldl (SliceArithmeticRound.next digit red) (resetRow s)
  ⟨add (companion c s.vector) (scale digit b), digit, red, result⟩

private def frame (w : ℕ) (c b : Vector p e) (digits : List (Fin p)) (s : Logical p e) : Stacks Ports :=
  state (regState w s) (streams (packed w (List.ofFn s.vector)) [] [] []
    (extra (packed w (List.ofFn c)) (packed w (List.ofFn b)) e (packed w digits) digits.length 0))

private theorem digit_runs (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (c b : Vector p e) (s : Logical p e) (digit : Fin p) (xs : List (Fin p)) :
    ∃ t ≤ digitCap e w, digitRoutine.Runs t
      (Function.update (frame w c b (digit :: xs) s) (.inr (.outer .rounds)) (List.replicate xs.length true))
      (frame w c b xs (advance c b s digit)) := by
  let cb := packed w (List.ofFn c)
  let bb := packed w (List.ofFn b)
  let vb := packed w (List.ofFn s.vector)
  let tail := packed w xs
  let r := regState w s
  let caller := extra cb bb e tail xs.length 0
  let base := streams [] [] [] [] caller
  let a := resetRow s
  let red := -top s.vector
  let rows := items c b s.vector
  let nextRow := rows.foldl (SliceArithmeticRound.next digit red) a
  let v' := add (companion c s.vector) (scale digit b)
  let out := packed w (List.ofFn v')
  obtain ⟨k, hk, prep⟩ := prepare_runs hw r digit (top s.vector) (Nat.mod_eq_of_lt (Word.modulus_lt hw))
    (Word.limb_val hw _) cb bb vb tail e xs.length
  have entryEq : Function.update (frame w c b (digit :: xs) s) (.inr (.outer .rounds))
        (List.replicate xs.length true) =
      state r (streams vb [] [] [] (extra cb bb e (wordBits (Word.limb w digit) ++ tail) xs.length 0)) := by
    rw [frame, updateStream]
    congr 1
    funext i
    cases i with
    | outer x => cases x <;> simp [streams, extra, packed, cb, bb, tail]
    | _ => rfl
  have rprep : prepared r digit (top s.vector) = registers w digit red a := by
    funext i
    fin_cases i <;> simp [prepared, r, regState, registers, a, resetRow, rowState, red, Word.limb]
  obtain ⟨m, hm, scanRun⟩ := SliceArithmeticRound.scan_runs hw Extra.rows base digit red rows a
  have hinput : SliceArithmeticRound.streams w Extra.rows base rows a =
      streams vb cb bb [] (extra cb bb e tail xs.length e) := by
    funext i
    cases i with
    | outer x => cases x <;> simp [SliceArithmeticRound.streams, streams, base, caller, extra, rows, items]
    | _ => simp [SliceArithmeticRound.streams, rows, items, List.map_ofFn, Function.comp_def,
        streams, base, vb, cb, bb, a, resetRow, rowState, packed]
  have hout : nextRow.output = (List.ofFn v').reverse := by
    simpa [nextRow, rows, items, red, top, v', a, resetRow, rowState] using
      SliceArithmeticRound.fold_vector_output c b s.vector digit a rfl
  have houtput : SliceArithmeticRound.streams w Extra.rows base [] nextRow =
      streams [] [] [] out.reverse caller := by
    funext i
    cases i with
    | outer x => cases x <;> simp [SliceArithmeticRound.streams, streams, base, caller, extra]
    | out => simp [SliceArithmeticRound.streams, streams, hout, out, base]
    | _ => rfl
  have hrows : rows ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [rows, items] at this
    omega
  have hhead := SliceArithmeticRound.fold_result_of_nonempty digit red rows a hrows
  change nextRow.output.head? = some nextRow.result at hhead
  rw [hout, List.head?_reverse] at hhead
  have htop : top v' = nextRow.result := by rw [top, List.getLastD_eq_getLast?, hhead]; rfl
  have houtReg : regState w (advance c b s digit) = registers w digit red nextRow := by
    change registers w digit red {nextRow with result := top v', output := []} = _
    rw [htop]
    rfl
  change (SliceArithmeticRound.scan Extra.rows).Runs m
    (state (registers w digit red a) (SliceArithmeticRound.streams w Extra.rows base rows a))
    (state (registers w digit red nextRow) (SliceArithmeticRound.streams w Extra.rows base [] nextRow)) at scanRun
  rw [hinput, houtput, ← rprep, ← houtReg] at scanRun
  have restored := restore_runs (registers w digit red nextRow) out caller
  rw [← houtReg] at restored
  have full := (prep.followedBy scanRun).followedBy restored
  rw [entryEq]
  refine ⟨_, ?_, full⟩
  simp only [cb, bb, out, packed_length, List.length_ofFn] at hk ⊢
  simp only [rows, items, List.length_ofFn] at hm
  unfold digitCap
  omega

/-- The register bank at entry holds the prime modulus and zero coefficients. -/
def initialRegisters (p w : ℕ) [NeZero p] : Fin 8 → BurstRAM.Word w :=
  registers w (0 : Fin p) 0 ⟨0, 0, 0, 0, 0, []⟩

/-- A single fixed finite control multiplies arbitrary coefficient vectors
of positive degree. It consumes all digits and stores the quotient-ring
product as low-degree-first, little-endian words in the accumulator port. -/
theorem machine_runs (he : 0 < e) (hw : Word.workingWidth p ≤ w) (c a b : Vector p e) :
    ∃ t ≤ e * (digitCap e w + 1) + 1, ∃ reg : Fin 8 → BurstRAM.Word w,
      machine.Runs t
        (state (initialRegisters p w) (streams (packed w (List.ofFn (zero p e))) [] [] []
          (extra (packed w (List.ofFn c)) (packed w (List.ofFn b)) e (packed w (List.ofFn a).reverse) e 0)))
        (state reg (streams (packed w (List.ofFn (mul c a b))) [] [] []
          (extra (packed w (List.ofFn c)) (packed w (List.ofFn b)) e [] 0 0))) := by
  let initial : Logical p e := ⟨zero p e, 0, 0, ⟨0,0,0,0,0,[]⟩⟩
  let digits := (List.ofFn a).reverse
  obtain ⟨t, ht, hrun⟩ := FiniteRoutine.repeatMarked_runs (.inr (.outer .rounds)) digitRoutine (frame w c b)
    (advance c b) (digitCap e w) (fun _ _ => rfl) (fun digit xs s => digit_runs he hw c b s digit xs)
    digits initial
  have hfold (xs : List (Fin p)) (s : Logical p e) :
      (xs.foldl (advance c b) s).vector =
      xs.foldl (fun v digit => add (companion c v) (scale digit b)) s.vector := by
    induction xs generalizing s with
    | nil => rfl
    | cons x xs ih => exact ih (advance c b s x)
  have hout : (digits.foldl (advance c b) initial).vector = mul c a b := by
    rw [hfold]
    dsimp only [digits]
    rw [List.foldl_reverse]
    rfl
  have hz : top (zero p e) = 0 := by
    cases e with
    | zero => simp [top]
    | succ k => rw [top, List.ofFn_succ']; simp [zero]
  have hr₀ : regState w initial = initialRegisters p w := by
    simp only [regState, initial, rowState, hz]
    rfl
  simp only [frame, hr₀, hout, digits, List.length_reverse, List.length_ofFn] at hrun ht
  exact ⟨t, ht, _, hrun⟩

end SliceArithmetic.HornerControl

end VPVNP
end Computability
end OAI
