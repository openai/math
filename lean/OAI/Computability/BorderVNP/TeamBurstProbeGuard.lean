import OAI.Computability.VPVNP.RAMTapeSuccessorRecord
import OAI.Computability.VPVNP.RAMTapeWord
import OAI.Computability.VPVNP.StructuredStackTotal

/-! # Checking a burst probe against its cap and address space

The controller preserves all three RAM operands. It consumes their temporary copies in
little-endian order, subtracting the requested length from the cap and adding it to
the starting address. A carry out of the address sum is legal precisely when every
lower sum bit was zero, so a half-open interval may end at the address-space boundary.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamBurstGuard

open VPVNP RAMTape BurstRAM TapeWord

/-- Original operands, their disposable copies, the common copy scratch, and the verdict stack. -/
inductive Port
  | address | length | cap | addressCopy | lengthCopy | capCopy | temp | flag
  deriving DecidableEq

instance : Fintype Port := derive_fintype% Port

/-- Three one-bit registers carried from a less significant column to the next. -/
private structure Flags where
  carry : Bool
  nonzero : Bool
  borrow : Bool
  deriving DecidableEq, Fintype

private def initial : Flags := ⟨false, false, false⟩

private def next (f : Flags) (a q c : Bool) : Flags :=
  let digit := addBit f.carry a q
  ⟨digit.2, f.nonzero || digit.1, (subBit f.borrow c q).2⟩

private def ok (f : Flags) : Bool := !f.borrow && !(f.carry && f.nonzero)

private def test (f : Flags) (as qs cs : List Bool) : Prop :=
  value qs + f.borrow.toNat ≤ value cs ∧
    value as + value qs + f.carry.toNat + f.nonzero.toNat ≤ 2^as.length

private instance (f : Flags) (as qs cs : List Bool) : Decidable (test f as qs cs) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem subtract_column (b q c : Bool) (x y : ℕ) :
    q.toNat + 2*x + b.toNat ≤ c.toNat + 2*y ↔ x + (subBit b c q).2.toNat ≤ y := by
  cases b <;> cases q <;> cases c <;> simp [subBit] <;> omega

private theorem add_column (k z a q : Bool) (x y limit : ℕ) :
    a.toNat + 2*x + (q.toNat + 2*y) + k.toNat + z.toNat ≤ limit*2 ↔
      x + y + (addBit k a q).2.toNat + (z || (addBit k a q).1).toNat ≤ limit := by
  cases k <;> cases z <;> cases a <;> cases q <;> simp [addBit] <;> omega

private theorem test_cons (f : Flags) (a q c : Bool) (as qs cs : List Bool) :
    test f (a :: as) (q :: qs) (c :: cs) ↔ test (next f a q c) as qs cs := by
  simp only [test, next, value, List.length_cons, pow_succ, subtract_column, add_column]

private theorem ok_nil (f : Flags) : ok f = decide (test f [] [] []) := by
  obtain ⟨a,b,c⟩ := f
  cases a <;> cases b <;> cases c <;> decide

private inductive Phase
  | address (f : Flags)
  | length (f : Flags) (a : Bool)
  | cap (f : Flags) (a q : Bool)
  | finish (b : Bool)
  deriving Fintype

private def readCopies : Routine Port Phase where
  entry := .address initial
  code
    | .address f => .pop .addressCopy fun v => some (v.elim (.finish (ok f)) (.length f))
    | .length f a => .pop .lengthCopy fun v => some (v.elim (.finish false) (.cap f a))
    | .cap f a q => .pop .capCopy fun v => some (v.elim (.finish false) (fun c => .address (next f a q c)))
    | .finish b => .push .flag b none

private def frame (s : Stacks Port) (as qs cs flags : List Bool) : Stacks Port
  | .addressCopy => as | .lengthCopy => qs | .capCopy => cs | .flag => flags
  | k => s k

private theorem write_address (s : Stacks Port) (as qs cs fs bits : List Bool) :
    Function.update (frame s as qs cs fs) .addressCopy bits = frame s bits qs cs fs := by
  funext i; cases i <;> rfl

private theorem write_length (s : Stacks Port) (as qs cs fs bits : List Bool) :
    Function.update (frame s as qs cs fs) .lengthCopy bits = frame s as bits cs fs := by
  funext i; cases i <;> rfl

private theorem write_cap (s : Stacks Port) (as qs cs fs bits : List Bool) :
    Function.update (frame s as qs cs fs) .capCopy bits = frame s as qs bits fs := by
  funext i; cases i <;> rfl

private theorem write_flag (s : Stacks Port) (as qs cs fs bits : List Bool) :
    Function.update (frame s as qs cs fs) .flag bits = frame s as qs cs bits := by
  funext i; cases i <;> rfl

private theorem read_runs (s : Stacks Port) (flags : List Bool) (f : Flags) (as qs cs : List Bool)
    (hq : as.length = qs.length) (hc : as.length = cs.length) :
    StackRuns readCopies.standalone (3*as.length+2) (some (.address f)) (frame s as qs cs flags)
      none (frame s [] [] [] (decide (test f as qs cs) :: flags)) := by
  induction as generalizing f qs cs with
  | nil =>
    cases qs <;> cases cs <;> simp_all only [List.length_cons, List.length_nil, Nat.zero_ne_add_one]
    refine .cons (.pop rfl) (.cons (.push rfl) ?_)
    simp only [frame, write_address, write_flag, List.tail_nil, ok_nil]
    exact .nil ..
  | cons a as ih =>
    cases qs with
    | nil => simp at hq
    | cons q qs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        rw [List.length_cons, show 3*(as.length+1)+2 = ((3*as.length+2)+1)+1+1 by omega]
        refine .cons (.pop rfl) (.cons (.pop rfl) (.cons (.pop rfl) ?_))
        simp only [frame, write_address, write_length, write_cap, List.head?_cons, List.tail_cons, Option.elim_some]
        simpa only [test_cons] using ih (next f a q c) qs cs (Nat.succ.inj hq) (Nat.succ.inj hc)

/-- Fixed finite routine for validating one burst. It pushes one decision bit. -/
def program : FiniteRoutine Port :=
  (((SuccessorFields.prependCopy .address .addressCopy .temp).followedBy
     (SuccessorFields.prependCopy .length .lengthCopy .temp)).followedBy
     (SuccessorFields.prependCopy .cap .capCopy .temp)).followedBy (.ofRoutine readCopies)

/-- Input representation for the guard, including all four initially empty work stacks. -/
structure Ready {w : ℕ} (a q c : Word w) (s : Stacks Port) : Prop where
  /-- Little-endian address. -/
  address : s .address = wordBits a
  /-- Little-endian requested length. -/
  length : s .length = wordBits q
  /-- Little-endian public cap. -/
  cap : s .cap = wordBits c
  /-- No pending address-copy bits. -/
  addressCopy : s .addressCopy = []
  /-- No pending length-copy bits. -/
  lengthCopy : s .lengthCopy = []
  /-- No pending cap-copy bits. -/
  capCopy : s .capCopy = []
  /-- The shared copy scratch is clean. -/
  temp : s .temp = []

/-- The complete physical guard costs exactly eighteen instructions per bit and eight
instructions for empty scans and the verdict. The sole change to the bank is the new flag. -/
theorem runs {w : ℕ} (a q c : Word w) (s : Stacks Port) (h : Ready a q c s) :
    program.Runs (18*w+8) s
      (Function.update s .flag (decide (q.val ≤ c.val ∧ a.val+q.val ≤ 2^w) :: s .flag)) := by
  let as := wordBits a
  let qs := wordBits q
  let cs := wordBits c
  let fs := s .flag
  have clean : frame s [] [] [] fs = s := by
    funext i; cases i <;> first | rfl | exact h.addressCopy.symm | exact h.lengthCopy.symm | exact h.capCopy.symm
  have h1 := SuccessorFields.prependCopy_runs Port.address .addressCopy .temp (by decide) (by decide)
    (by decide) (frame s [] [] [] fs) h.temp
  have h2 := SuccessorFields.prependCopy_runs Port.length .lengthCopy .temp (by decide) (by decide)
    (by decide) (frame s as [] [] fs) h.temp
  have h3 := SuccessorFields.prependCopy_runs Port.cap .capCopy .temp (by decide) (by decide)
    (by decide) (frame s as qs [] fs) h.temp
  simp only [frame, write_address, h.address, length_wordBits, List.append_nil] at h1
  simp only [frame, write_length, h.length, length_wordBits, List.append_nil] at h2
  simp only [frame, write_cap, h.cap, length_wordBits, List.append_nil] at h3
  have h4 := read_runs s fs initial as qs cs (by simp [as, qs]) (by simp [as, cs])
  have he : test initial as qs cs ↔ q.val ≤ c.val ∧ a.val+q.val ≤ 2^w := by
    simp [test, initial, as, qs, cs, value_wordBits]
  have h4' : (FiniteRoutine.ofRoutine readCopies).Runs (3*w+2) (frame s as qs cs fs)
      (frame s [] [] [] (decide (q.val ≤ c.val ∧ a.val+q.val ≤ 2^w) :: fs)) := by
    change StackRuns readCopies.standalone (3*w+2) (some (.address initial)) _ none _
    simpa only [as, length_wordBits, he] using h4
  have all := ((h1.followedBy h2).followedBy h3).followedBy h4'
  rw [← write_flag s [] [] [] fs (decide (q.val ≤ c.val ∧ a.val+q.val ≤ 2^w) :: fs), clean] at all
  simpa only [program, show 5*w+2+(5*w+2)+(5*w+2)+(3*w+2) = 18*w+8 by omega] using all

/-- Every continuation receives the decision and the exact remaining fuel. -/
theorem allStops {w : ℕ} (a q c : Word w) (s : Stacks Port) (h : Ready a q c s)
    (cont : ℕ → Stacks Port → Prop) (fuel : ℕ) :
    program.body.AllStops cont (fuel+(18*w+8)) s ↔
      cont fuel (Function.update s .flag (decide (q.val ≤ c.val ∧ a.val+q.val ≤ 2^w) :: s .flag)) :=
  (runs a q c s h).allStops_iff cont fuel

end TeamBurstGuard

end BorderVNP
end Computability
end OAI
