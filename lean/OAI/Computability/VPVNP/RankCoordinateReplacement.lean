import OAI.Computability.VPVNP.RankCoordinateMinor
import OAI.Computability.VPVNP.RankCoordinateSubmatrix

/-!
# The numerator reader for a Cramer minor

The comparison aliases the caller's dense row address and reads the
replacement ordinal from a separate register. The selected scalar reader
therefore receives the usual two addresses. Its result is the target scalar
precisely on the replaced row. The ordinal and comparison workspace are
ready again at every return.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.Replacement

open RAMTape BurstRAM UniversalCountStack Dispatch

/-- Two comparison registers and the scalar-reader workspace used to recognize the replaced
row. -/
abbrev Work (K : Type) := ISA.Port 2 0 ⊕ K
/-- The public matrix-entry reader ports together with the row-replacement workspace. -/
abbrev Port (K : Type) := MacaulayRead.Port (Work K)

variable {K : Type}

/-- At entry, the row supplied by the caller is register zero. The second
comparison register holds the ordinal computed by the enclosing query. -/
def workBank (w : ℕ) (replacement : List Bool) (s : Stacks K) : Stacks (Work K) :=
  Sum.elim (fun a => match a with
    | .reg j => if j = 1 then replacement else []
    | z => ISA.bank Fin.elim0 (0 : Word w) (fun _ => 0) [] z) s

/-- Installing a new ordinal into its designated stack preserves all other
workspace and advice. -/
theorem set_replacement [DecidableEq K] (w : ℕ) (old new : List Bool) (s : Stacks K) :
    Function.update (workBank w old s) (.inl (.reg 1)) new = workBank w new s := by
  funext k
  rcases k with k | k
  · cases k with
    | reg i => fin_cases i <;> rfl
    | _ => rfl
  · rfl

/-- The scalar reader’s auxiliary bank is ready, register one holds the width-w replacement-row
ordinal, and the local register-zero stack is empty because comparison reads the caller’s
row port. -/
def Ready (w k : ℕ) (ready : Stacks K → Prop) (a : Stacks (Work K)) : Prop :=
  ∃ s, ready s ∧ a = workBank w (digits w k) s

private def comparePorts : ISA.Port 2 0 → Port K
  | .reg i => if i = 0 then .row else .aux (.inl (.reg i))
  | z => .aux (.inl z)

private def entryPorts : MacaulayRead.Port K → Port K
  | .row => .row | .col => .col | .result => .result | .aux k => .aux (.inr k)

private theorem entryInj : Function.Injective (entryPorts (K := K)) := by
  intro a b h; cases a <;> cases b <;> simp_all [entryPorts]

/-- The replacement ordinal is a runtime input to this fixed routine. -/
def numerator (ordinary target : FiniteRoutine (MacaulayRead.Port K)) : FiniteRoutine (Port K) :=
  Minor.equalBranch comparePorts 0 1 (ordinary.onPorts entryPorts) (target.onPorts entryPorts)

private def regBank {w : ℕ} (col result : List Bool) (s : Stacks K) (rs : Regs 2 w) : Stacks (Port K)
  | .row => wordBits (rs 0)
  | .col => col
  | .result => result
  | .aux p => workBank w (wordBits (rs 1)) s p

private theorem comparisonBank {w : ℕ} (col result : List Bool) (s : Stacks K) :
    RegisterBank comparePorts (regBank (w := w) col result s) 0 := by
  constructor
  · intro a b h
    cases a <;> cases b <;> simp only [comparePorts] at h ⊢ <;> (try split_ifs at h) <;> simp_all
  · intro rs a
    cases a with
    | reg i => fin_cases i <;> rfl
    | _ => rfl
  · intro a b p hp
    cases p with
    | row => exact (hp (.reg 0) rfl).elim
    | col | result => rfl
    | aux p =>
      rcases p with p | p
      · cases p with
        | reg i => fin_cases i <;> first | rfl | exact (hp (.reg 1) rfl).elim
        | _ => rfl
      · rfl

variable [DecidableEq K] {p e r s w v Bo Bt S : ℕ} {c : SliceArithmetic.Vector p e}
    {ready : Stacks K → Prop} {ordinary target : FiniteRoutine (MacaulayRead.Port K)}
    {D : Matrix (Fin r) (Fin s) (Scalar c)} {T : Fin s → Scalar c}

private theorem liftEntry {i : Fin r} {j : Fin s} {k : Fin r} {run : FiniteRoutine (MacaulayRead.Port K)}
    {z : List Bool} {a b : Stacks K} {t : ℕ}
    (h : run.BoundedRun S t (MacaulayRead.bank w i j [] a) (MacaulayRead.bank w i j z b)) :
    (run.onPorts entryPorts).BoundedRun (max S (w+(20*w+10))) t
      (MacaulayRead.bank w i j [] (workBank w (digits w k) a))
      (MacaulayRead.bank w i j z (workBank w (digits w k) b)) := by
  refine FiniteRoutine.BoundedRun.framed entryInj (h.enlarge (le_max_left ..)) ?_
    (fun x => by cases x <;> rfl) (fun x => by cases x <;> rfl) ?_
  · intro x
    cases x with
    | row => exact (h.initial_cap .row).trans (le_max_left ..)
    | col => exact (h.initial_cap .col).trans (le_max_left ..)
    | result => exact Nat.zero_le _
    | aux x =>
      rcases x with x | x
      · have hle : w ≤ max S (w+(20*w+10)) := (Nat.le_add_right ..).trans (le_max_right ..)
        cases x with
        | reg i => fin_cases i <;> simp [MacaulayRead.bank, workBank, hle]
        | pub i => exact i.elim0
        | persistent => simp [MacaulayRead.bank, workBank, ISA.bank]
        | work _ => exact Nat.zero_le _
        | logPort a => cases a <;> exact Nat.zero_le _
      · exact (h.initial_cap (.aux x)).trans (le_max_left ..)
  · intro x hx
    cases x with
    | row | col => rfl
    | result => exact (hx .result rfl).elim
    | aux x =>
      rcases x with x | x
      · rfl
      · exact (hx (.aux x) rfl).elim

/-- Supply the target row as a scalar reader of the constant-row matrix.
Both arms may update the auxiliary state on return. Every address comparison
and each selected arm respect the stated cap, independent of their running time. -/
theorem correctSpace (ho : MacaulayRead.CorrectSpace ordinary D w v Bo S ready)
    (ht : MacaulayRead.CorrectSpace target (fun _ j => T j : Matrix (Fin r) (Fin s) _) w v Bt S ready)
    (k : Fin r) (hfit : r ≤ 2^w) :
    MacaulayRead.CorrectSpace (numerator ordinary target) (D.updateRow k T) w v
      (20*w+10+(max Bo Bt+1)) (max S (w+(20*w+10))) (Ready w k ready) := by
  rintro i j _ ⟨a, ha, rfl⟩
  let rs : Regs 2 w := ![Fin.ofNat _ i.val, Fin.ofNat _ k.val]
  have heq : rs 0 = rs 1 ↔ i = k := by
    simp only [rs, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.ext_iff, Fin.val_ofNat,
      Nat.mod_eq_of_lt (i.isLt.trans_le hfit), Nat.mod_eq_of_lt (k.isLt.trans_le hfit)]
  let hb := comparisonBank (w := w) (digits w j) [] a
  have aligned : regBank (digits w j) [] a rs = MacaulayRead.bank w i j [] (workBank w (digits w k) a) := by
    funext p; cases p <;> rfl
  by_cases hi : i = k
  · obtain ⟨d, hd, b, hready, run⟩ := ht i j a ha
    have branch := liftEntry (k := k) run
    have test := Minor.equalBranch_runs hb rs 0 1 (ordinary.onPorts entryPorts) (target.onPorts entryPorts)
      (t := d) (out := MacaulayRead.bank w i j (Engine.scalar v (T j)) (workBank w (digits w k) b))
      (le_max_right S _) (by rw [ite_eq_left (heq.mpr hi), aligned]; exact branch)
    rw [aligned] at test
    refine ⟨20*w+10+(d+1), by have := le_max_right Bo Bt; omega, workBank w (digits w k) b, ⟨b, hready, rfl⟩, ?_⟩
    simpa only [numerator, hi, Matrix.updateRow_self] using test
  · obtain ⟨d, hd, b, hready, run⟩ := ho i j a ha
    have branch := liftEntry (k := k) run
    have test := Minor.equalBranch_runs hb rs 0 1 (ordinary.onPorts entryPorts) (target.onPorts entryPorts)
      (t := d) (out := MacaulayRead.bank w i j (Engine.scalar v (D i j)) (workBank w (digits w k) b))
      (le_max_right S _) (by rw [ite_eq_right (heq.not.mpr hi), aligned]; exact branch)
    rw [aligned] at test
    refine ⟨20*w+10+(d+1), by have := le_max_left Bo Bt; omega, workBank w (digits w k) b, ⟨b, hready, rfl⟩, ?_⟩
    simpa only [numerator, Matrix.updateRow_ne hi] using test

/-- Assemble the Cramer numerator from the ordinal selectors and two raw
scalar reads. The target reader receives the selected original column on its
column port. Its row input is immaterial for the constant-row target matrix. -/
theorem submatrix_correctSpace {n m Br Bc : ℕ} {A : Matrix (Fin n) (Fin m) (Scalar c)}
    {f : Fin r → Fin n} {g : Fin s → Fin m} {rawTarget : Fin m → Scalar c}
    {rows cols : FiniteRoutine (OrdinalRead.Port K)}
    (row : OrdinalRead.CorrectSpace rows f w Br S ready)
    (col : OrdinalRead.CorrectSpace cols g w Bc S ready)
    (entry : MacaulayRead.CorrectSpace ordinary A w v Bo S ready)
    (targetEntry : MacaulayRead.CorrectSpace target (fun _ j => rawTarget j : Matrix (Fin n) (Fin m) _)
      w v Bt S ready)
    (k : Fin r) (hfit : r ≤ 2^w) :
    MacaulayRead.CorrectSpace (numerator (Submatrix.minorRead rows cols ordinary)
      (Submatrix.minorRead rows cols target)) ((A.submatrix f g).updateRow k (rawTarget ∘ g)) w v
      (20*w+10+(max (Br+Bc+Bo+2*(w+1)) (Br+Bc+Bt+2*(w+1))+1)) (max S (w+(20*w+10)))
      (Ready w k (Submatrix.Ready ready)) :=
  correctSpace (D := A.submatrix f g) (T := rawTarget ∘ g)
    (ordinary := Submatrix.minorRead rows cols ordinary) (target := Submatrix.minorRead rows cols target)
    (Submatrix.correctSpace (M := A) (f := f) (g := g) row col entry)
    (Submatrix.correctSpace (M := fun _ j => rawTarget j) (f := f) (g := g) row col targetEntry) k hfit

end RankQuery.Stack.Coordinate.Replacement

end VPVNP
end Computability
end OAI
