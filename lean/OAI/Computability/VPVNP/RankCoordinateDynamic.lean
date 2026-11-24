import OAI.Computability.VPVNP.RankCoordinateOrdinalABI
import OAI.Computability.VPVNP.RankCoordinateColumn

/-! # Preparing the query-dependent Cramer row and target

The rank and length of the equation block are fixed advice. Adding its rank to
the current basis ordinal gives a greedy row query whose returned original
index locates the source basis monomial. Adding the same rank to the next
ordinal gives the row to replace in the square numerator.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.Dynamic

open RAMTape UniversalCountStack Dispatch BurstRAM SliceArithmetic

variable {L : Type}

/-- The eight-register ISA stack bank, including its persistent, scratch and private-log ports,
together with the ordinal selector’s auxiliary ports. -/
abbrev Host (L : Type) := ISA.Port 8 0 ⊕ L

/-- Registers contain current, next, equation rank, equation-row count, the
two combined ordinals, original selected row, and selected monomial ordinal. -/
def regs {w : ℕ} (cur next rank rows offset replace original mono : ℕ) : Regs 8 w :=
  ![Fin.ofNat _ cur, Fin.ofNat _ next, Fin.ofNat _ rank, Fin.ofNat _ rows,
    Fin.ofNat _ offset, Fin.ofNat _ replace, Fin.ofNat _ original, Fin.ofNat _ mono]

/-- Combine the live coordinate registers with the auxiliary stacks of the ordinal selector. -/
def bank {w : ℕ} (aux : Stacks L) (rs : Regs 8 w) : Stacks (Host L) := Sum.elim (ISA.bank Fin.elim0 0 rs []) aux

/-- Wire the selector's input and output to registers four and six while leaving its auxiliary
ports in their own bank. -/
def indexPorts : OrdinalRead.Port L → Host L
  | .input => .inl (.reg 4) | .result => .inl (.reg 6) | .aux k => .inr k

theorem indexPorts_injective : Function.Injective (indexPorts (L := L)) := by
  intro a b he; cases a <;> cases b <;> simp_all [indexPorts]

private def offsets : RegCode 8 := .seq (.op 4 .add 2 0) (.op 5 .add 2 1)
private def removePrefix : RegCode 8 := .op 7 .sub 6 3

/-- The greedy selector reads the current combined ordinal from register four.
The two outputs for the Cramer caller are registers five and seven. -/
def machine (selector : FiniteRoutine (OrdinalRead.Port L)) : FiniteRoutine (Host L) :=
  (((offsets.compile.onPorts Sum.inl).followedBy (CallClear.clear (.inl (.reg 6)))).followedBy
    (selector.onPorts indexPorts)).followedBy (removePrefix.compile.onPorts Sum.inl)

/-- Tick allowance for computing the two rank offsets, clearing the selector’s result register
and subtracting the equation-row count after selection. -/
def overhead (w : ℕ) := registerClock w offsets+(w+1)+registerClock w removePrefix

private theorem framed {w : ℕ} (aux : Stacks L) : RegisterBank Sum.inl (bank (w := w) aux) 0 := by
  refine ⟨Sum.inl_injective, fun _ _ ↦ rfl, ?_⟩
  intro _ _ k outside; cases k with
  | inl i => exact (outside i rfl).elim
  | inr => rfl

private theorem outside_le {w cap : ℕ} (aux : Stacks L) (ha : ∀ k, (aux k).length ≤ cap) (rs : Regs 8 w)
    (j : Host L) (hj : ∀ i, Sum.inl i ≠ j) : (bank aux rs j).length ≤ cap := by
  cases j with
  | inl i => exact (hj i rfl).elim
  | inr k => exact ha k

private theorem bank_cap {w cap : ℕ} {aux : Stacks L} (hw : w ≤ cap) (ha : ∀ k, (aux k).length ≤ cap)
    (rs : Regs 8 w) (j : Host L) : (bank aux rs j).length ≤ cap := by
  cases j with
  | inl i => exact (RegisterTable.bank_length_le Fin.elim0 0 rs i).trans hw
  | inr k => exact ha k

private theorem add_offsets {w : ℕ} (u v rank size : ℕ) :
    offsets.exec (regs (w := w) u v rank size 0 0 0 0) = regs u v rank size (rank+u) (rank+v) 0 0 := by
  funext i
  fin_cases i <;> simp [offsets, RegCode.exec, Arith.word, Arith.opcode, PrivateRAM.BinaryOp.eval, regs]
  all_goals apply Fin.ext; simp [Fin.val_add, Nat.add_mod]

private theorem sub_rows {w : ℕ} (u v rank size off k row : ℕ) (hsize : size < 2^w) (hrow : row < 2^w) :
    removePrefix.exec (regs (w := w) u v rank size off k row 0) = regs u v rank size off k row (row-size) := by
  funext i
  fin_cases i <;> simp [removePrefix, RegCode.exec, regs]
  apply Fin.ext
  have hfit : Arith.sub.eval (Fin.ofNat (2^w) row).val (Fin.ofNat (2^w) size).val < 2^w := by
    simp only [Arith.eval, Fin.val_ofNat, Nat.mod_eq_of_lt hrow, Nat.mod_eq_of_lt hsize]
    exact (Nat.sub_le ..).trans_lt hrow
  change (Arith.sub.word (Fin.ofNat (2^w) row) (Fin.ofNat (2^w) size)).val = (Fin.ofNat (2^w) (row-size)).val
  rw [Arith.word_val _ _ _ hfit]
  simp [Arith.eval, Nat.mod_eq_of_lt hrow, Nat.mod_eq_of_lt hsize,
    Nat.mod_eq_of_lt ((Nat.sub_le row size).trans_lt hrow)]

private theorem frame_outside [DecidableEq L] {w : ℕ} (u v rank size off k row : ℕ) (s out : Stacks L)
    (j : Host L) (outside : ∀ z, indexPorts z ≠ j) :
    bank out (regs (w := w) u v rank size off k row 0) j =
      Function.update (bank s (regs (w := w) u v rank size off k 0 0)) (.inl (.reg 6)) [] j := by
  have no : j ≠ .inl (.reg 6) := Ne.symm (outside .result)
  rw [Function.update_of_ne no]
  cases j with
  | inr j => exact (outside (.aux j) rfl).elim
  | inl j => cases j with
    | reg z =>
      have hne : z ≠ 6 := fun eq ↦ by subst z; exact outside .result rfl
      fin_cases z <;> simp_all [bank, ISA.bank, regs]
    | pub i => exact Fin.elim0 i
    | persistent => change wordBits (0 : Word w) = _; rfl
    | work i => change ([] : List Bool) = _; rfl
    | logPort i => change ISA.logStacks ([] : PrivateRAM.WriteLog w) i = _; rfl

variable [DecidableEq L] {F : Type*} [Field F] [DecidableEq F] {e n m w B S : ℕ}

/-- Actual register and greedy-index execution. The result includes all offsets,
the requested basis monomial, and the selector's reusable workspace. -/
theorem machine_bounded (W : Matrix (Fin e) (Fin m) F) (M : Matrix (Fin n) (Fin m) F)
    (cur next : Fin (suffixDimension W M)) (selector : FiniteRoutine (OrdinalRead.Port L))
    {ready : Stacks L → Prop} (hc : OrdinalRead.CorrectSpace selector (greedyRowIndex (appendRows W M)) w B S ready)
    (hw : w ≤ S) (fits : e+n < 2^w) (haux : ∀ s, ready s → ∀ k, (s k).length ≤ S)
    (aux : Stacks L) (hr : ready aux) :
    let rank := rankQuery W
    let i := combinedOrdinal W M cur
    let j := combinedOrdinal W M next
    let row := greedyRowIndex (appendRows W M) i
    ∃ t ≤ B+overhead w, ∃ out, ready out ∧ (machine selector).BoundedRun (S+overhead w) t
      (bank aux (regs (w := w) cur next rank e 0 0 0 0))
      (bank out (regs (w := w) cur next rank e i j row (suffixBasisIndex W M cur))) := by
  let rank := rankQuery W
  let i := combinedOrdinal W M cur
  let j := combinedOrdinal W M next
  let row := greedyRowIndex (appendRows W M) i
  let rs := regs (w := w) cur next rank e i j 0 0
  let rs' := regs (w := w) cur next rank e i j row 0
  let cap := S+overhead w
  have room : w+registerClock w offsets ≤ cap := Nat.add_le_add hw (by dsimp [cap,overhead]; omega)
  have auxFit := haux aux hr
  obtain ⟨a, ha, added⟩ := registerCall_runs (framed aux) offsets (regs (w := w) cur next rank e 0 0 0 0)
    cap room (outside_le _ (fun k ↦ (auxFit k).trans (Nat.le_add_right ..)) _)
  rw [add_offsets] at added
  change (offsets.compile.onPorts Sum.inl).BoundedRun cap a _ (bank aux rs) at added
  let slot : Host L := .inl (.reg 6)
  let pre := Function.update (bank aux rs) slot []
  have cleared := CallClear.clear_runs slot (bank aux rs)
  rw [show ((bank aux rs) slot).length = w from length_wordBits _] at cleared
  have clear : (CallClear.clear slot).BoundedRun cap (w+1) (bank aux rs) pre :=
    spaceRun_of_steps cleared fun k ↦ Nat.add_le_add (bank_cap hw auxFit _ k) (by dsimp [overhead]; omega)
  obtain ⟨b, hb, out, ho, find⟩ := hc i aux hr
  have big : (selector.onPorts indexPorts).BoundedRun cap b pre (bank out rs') := by
    refine FiniteRoutine.BoundedRun.framed (r := selector) indexPorts_injective
      (find.mono_cap (show S ≤ cap from Nat.le_add_right ..)) clear.final_cap ?_ ?_ ?_
    · intro k; cases k <;> rfl
    · intro k; cases k <;> rfl
    · exact frame_outside cur next rank e i j row aux out
  obtain ⟨c, hs, subtracted⟩ := registerCall_runs (framed out) removePrefix rs' cap
    (Nat.add_le_add hw (by dsimp [overhead]; omega)) (fun k _ ↦ big.final_cap k)
  have hrow : row.val < 2^w := row.isLt.trans fits
  have he : e < 2^w := (Nat.le_add_right ..).trans_lt fits
  rw [show removePrefix.exec rs' = regs (w := w) cur next rank e i j row (row.val-e) from sub_rows cur next rank e i j row he hrow] at subtracted
  have done := ((added.followedBy clear).followedBy big).followedBy subtracted
  refine ⟨((a+(w+1))+b)+c, ?_, out, ho, ?_⟩
  · dsimp [overhead]; omega
  · exact done

end RankQuery.Stack.Coordinate.Dynamic

end VPVNP
end Computability
end OAI
