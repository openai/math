import OAI.Computability.VPVNP.RankCoordinateDimension
import OAI.Computability.VPVNP.RankQueryStackRegister
import OAI.Computability.VPVNP.RegisterTable

/-! # Register arithmetic for a physical prefix-rank query

The control holds the cursor, one, target ordinal, returned rank and inclusive
prefix length in five binary words. It forms the inclusive length before every
rank call and compares the returned word with the ordinal. Other ports remain
available to the matrix and rank subroutines.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.PrefixWords

open RAMTape UniversalCountStack BurstRAM Dispatch TapeWord

variable {L : Type}

/-- The five prefix-rank registers alongside the scalar reader's auxiliary bank. -/
abbrev Port (L : Type) := ISA.Port 5 0 ⊕ L

/-- Initialize the cursor, constant one, requested ordinal, returned rank, and inclusive prefix
length. -/
def words {w : ℕ} (cursor ordinal rank length : ℕ) : Regs 5 w :=
  ![Fin.ofNat _ cursor, 1, Fin.ofNat _ ordinal, Fin.ofNat _ rank, Fin.ofNat _ length]

/-- Mount the five binary words and the prefix reader's auxiliary state in their disjoint
banks. -/
def bank {w : ℕ} (s : Stacks L) (rs : Regs 5 w) : Stacks (Port L) :=
  Sum.elim (ISA.bank Fin.elim0 0 rs []) s

private def addCursor (dst : Fin 5) : RegCode 5 := .op dst .add 0 1

/-- The prefix-length input is register four, and the rank output is register three.
Only this subcall depends on the matrix representation. -/
def rankTest (rank : FiniteRoutine (Port L)) : FiniteRoutine (Port L) :=
  (((addCursor 4).compile.onPorts Sum.inl).followedBy rank).followedBy
    ((ISA.compareRegs .lt (2 : Fin 5) 3).onPorts (Sum.inl : ISA.Port 5 0 → Port L))

/-- Starting at cursor zero, ask for the rank through the current row and advance until that
rank exceeds the requested zero-based ordinal. The cursor then identifies the corresponding
greedy pivot row. -/
def machine (rank : FiniteRoutine (Port L)) : FiniteRoutine (Port L) :=
  greedyPrefix (.inl (.work 0)) (rankTest rank) ((addCursor 0).compile.onPorts Sum.inl)

/-- Step allowance for one register addition, used both to form the inclusive prefix length and
to advance the cursor. Each use contributes separately to the prefix-scan bound. -/
def arithmeticBound (w : ℕ) := arithmeticClock w

private theorem installed {w : ℕ} (s : Stacks L) (rs : Regs 5 w) :
    installStacks Sum.inl (bank s rs) (ISA.bank Fin.elim0 0 rs []) = bank s rs :=
  installStacks_eq Sum.inl_injective _ _ fun _ ↦ rfl

private theorem outside_le {cap w : ℕ} {s : Stacks L} (hs : ∀ l, (s l).length ≤ cap) (rs : Regs 5 w)
    (l : Port L) (outside : ∀ k, Sum.inl k ≠ l) : ((bank s rs) l).length ≤ cap := by
  cases l with
  | inl i => exact (outside i rfl).elim
  | inr i => exact hs i


private theorem registerBank {w : ℕ} (s : Stacks L) : RegisterBank Sum.inl (bank (w := w) s) 0 := by
  refine ⟨Sum.inl_injective, fun _ _ ↦ rfl, ?_⟩
  intro a b j outside
  cases j with
  | inl i => exact (outside i rfl).elim
  | inr i => rfl

variable [DecidableEq L]

private theorem addCursor_runs {cap w : ℕ} {s : Stacks L} (hs : ∀ l, (s l).length ≤ cap)
    (hc : w+arithmeticBound w ≤ cap) (rs : Regs 5 w) (dst : Fin 5) :
    ∃ t ≤ arithmeticBound w, ((addCursor dst).compile.onPorts Sum.inl).BoundedRun cap t
      (bank s rs) (bank s ((addCursor dst).exec rs)) :=
  registerCall_runs (registerBank s) (addCursor dst) rs cap hc (outside_le hs rs)

private theorem comparison_runs {cap w : ℕ} {s : Stacks L} (hs : ∀ l, (s l).length ≤ cap)
    (hc : w+arithmeticBound w ≤ cap) (rs : Regs 5 w) :
    ((ISA.compareRegs .lt (2 : Fin 5) 3).onPorts Sum.inl).BoundedRun cap (20*w+10) (bank s rs)
      (Function.update (bank s rs) (.inl (.work 0)) [decide (rs 2 < rs 3)]) := by
  have run := ISA.compareRegs_run .lt (2 : Fin 5) 3 Fin.elim0 (0 : Word w) rs []
  have bound : 20*w+10 ≤ arithmeticBound w := by unfold arithmeticBound arithmeticClock; nlinarith [Nat.zero_le (w^2)]
  have small := spaceRun_of_steps (cap := cap) run (fun k ↦
    (Nat.add_le_add (RegisterTable.bank_length_le Fin.elim0 0 rs k) bound).trans hc)
  have large := FiniteRoutine.BoundedRun.onPorts (a := ISA.compareRegs .lt (2 : Fin 5) 3) Sum.inl_injective
    (bank s rs) small (outside_le hs rs)
  rw [installed, ← installStacks_update Sum.inl_injective, installed] at large
  exact large

private theorem addCursor_length {w : ℕ} (j k a b : ℕ) :
    (addCursor 4).exec (words (w := w) j k a b) = words j k a (j+1) := by
  funext i
  fin_cases i <;> simp [addCursor, RegCode.exec, Arith.word, Arith.opcode, PrivateRAM.BinaryOp.eval, words]
  apply Fin.ext
  simp [Fin.val_add, Nat.add_mod]

private theorem addCursor_index {w : ℕ} (j k a b : ℕ) :
    (addCursor 0).exec (words (w := w) j k a b) = words (j+1) k a b := by
  funext i
  fin_cases i <;> simp [addCursor, RegCode.exec, Arith.word, Arith.opcode, PrivateRAM.BinaryOp.eval, words]
  apply Fin.ext
  simp [Fin.val_add, Nat.add_mod]

variable {F : Type*} [Field F] [DecidableEq F] {n m w cap T : ℕ}

/-- Numeric rank of a prefix, with saturation only for out-of-range indices,
which the machine never reaches. -/
def rankAt (A : Matrix (Fin n) (Fin m) F) (j : ℕ) :=
  if h : j ≤ n then rankQuery (prefixRows A j h) else rankQuery A

theorem rankAt_eq (A : Matrix (Fin n) (Fin m) F) {j : ℕ} (hj : j ≤ n) :
    rankAt A j = rankQuery (prefixRows A j hj) := by simp [rankAt, hj]

private theorem rankAt_le (A : Matrix (Fin n) (Fin m) F) (j : ℕ) : rankAt A j ≤ n := by
  unfold rankAt
  split_ifs with hj
  · rw [rankQuery_eq]
    exact (by simpa only [Fintype.card_fin] using (prefixRows A j hj).rank_le_card_height : _ ≤ j).trans hj
  · rw [rankQuery_eq]
    simpa only [Fintype.card_fin] using A.rank_le_card_height

/-- The only remaining call contract is the rank of a supplied prefix. All index
arithmetic and comparisons are physical routines, independent of the matrix shape. -/
theorem machine_runs (A : Matrix (Fin n) (Fin m) F) (k : Fin (rankQuery A)) (s : Stacks L)
    (rank : FiniteRoutine (Port L)) (fits : n < 2^w) (hs : ∀ l, (s l).length ≤ cap)
    (hc : w+arithmeticBound w ≤ cap)
    (call : ∀ j < n, ∃ t ≤ T, rank.BoundedRun cap t
      (bank s (words (w := w) j k.val (rankAt A j) (j+1)))
      (bank s (words (w := w) j k.val (rankAt A (j+1)) (j+1)))) :
    let out := (greedyRowIndex A k).val
    ∃ t ≤ n*((arithmeticBound w+T+(20*w+10))+1+arithmeticBound w), (machine rank).BoundedRun cap t
      (bank s (words (w := w) 0 k.val (rankAt A 0) 0))
      (bank s (words (w := w) out k.val (rankAt A (out+1)) (out+1))) := by
  let input j := bank s (words (w := w) j k.val (rankAt A j) j)
  let checked j := bank s (words (w := w) j k.val (rankAt A (j+1)) (j+1))
  apply greedyPrefix_runs A k _ _ _ input checked (fun _ _ ↦ rfl)
  · intro j hj
    obtain ⟨a, ha, add⟩ := addCursor_runs hs hc (words (w := w) j k.val (rankAt A j) j) 4
    rw [addCursor_length] at add
    obtain ⟨b, hb, result⟩ := call j hj
    have comp := comparison_runs hs hc (words (w := w) j k.val (rankAt A (j+1)) (j+1))
    have fitK : k.val < 2^w := by
      have h := A.rank_le_card_height
      rw [Fintype.card_fin] at h
      exact (k.isLt.trans_le ((rankQuery_eq A).le.trans h)).trans fits
    have fitR := (rankAt_le A (j+1)).trans_lt fits
    rw [rankAt_eq A hj] at fitR
    have cmp : decide ((words (w := w) j k.val (rankAt A (j+1)) (j+1)) 2 <
        (words (w := w) j k.val (rankAt A (j+1)) (j+1)) 3) =
        decide (k.val < rankQuery (prefixRows A (j+1) hj)) := by
      simp [words, Fin.lt_def, Nat.mod_eq_of_lt fitK, Nat.mod_eq_of_lt fitR, rankAt_eq A hj]
    rw [cmp] at comp
    exact ⟨_, by omega, (add.followedBy result).followedBy comp⟩
  · intro j _
    obtain ⟨t, ht, add⟩ := addCursor_runs hs hc (words (w := w) j k.val (rankAt A (j+1)) (j+1)) 0
    rw [addCursor_index] at add
    exact ⟨t, ht, add⟩

end RankQuery.Stack.Coordinate.PrefixWords

end VPVNP
end Computability
end OAI
