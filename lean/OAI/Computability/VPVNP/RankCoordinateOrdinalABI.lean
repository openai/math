import OAI.Computability.VPVNP.RankCoordinateOrdinal
import OAI.Computability.VPVNP.RankCoordinateRegisters
import OAI.Computability.VPVNP.SliceArithmeticCallClear
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-! # Returning an original greedy index as a binary word

The caller supplies the dense ordinal on a dedicated port. The fixed adapter
stages it in the five-register prefix scanner, copies out the successful cursor,
and restores the zero-word templates in its scratch registers before returning.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.OrdinalABI

open RAMTape UniversalCountStack BurstRAM Dispatch SliceArithmetic

variable {K : Type} [DecidableEq K]

/-- The prefix-rank registers and underlying scan workspace mounted inside the ordinal reader. -/
abbrev Aux (K : Type) := PrefixWords.Port K
/-- The ordinal reader's public input and output together with its private prefix-scan bank. -/
abbrev Host (K : Type) := OrdinalRead.Port (Aux K)

private def reg (i : Fin 5) : Host K := .aux (.inl (.reg i))
private def tmp : Host K := .aux (.inl (.work 15))

private def reset : RegCode 5 := .seq (.lit 0 0) (.seq (.lit 2 0) (.seq (.lit 3 0) (.lit 4 0)))

private def prepare : FiniteRoutine (Host K) :=
  (CallClear.clear (reg 2)).followedBy (SuccessorFields.prependCopy .input (reg 2) tmp)

/-- Copy the requested ordinal into register two, run the supplied prefix scanner, copy its
selected index from register zero to the result, and reset the four mutable prefix
registers. -/
def machine (scan : FiniteRoutine (Aux K)) : FiniteRoutine (Host K) :=
  ((prepare.followedBy (scan.onPorts OrdinalRead.Port.aux)).followedBy
    (SuccessorFields.prependCopy (reg 0) .result tmp)).followedBy
    (reset.compile.onPorts (OrdinalRead.Port.aux ∘ Sum.inl))

variable {w : ℕ}

/-- Initial prefix-register values for an idle ordinal reader, retaining its underlying
auxiliary stacks. -/
def idle (side : Stacks K) := PrefixWords.bank side (PrefixWords.words (w := w) 0 0 0 0)

private def framed (k : ℕ) (res : List Bool) (side : Stacks K) (rs : Regs 5 w) :=
  OrdinalRead.bank w k res (PrefixWords.bank side rs)

private theorem reg_eq (k : ℕ) (res : List Bool) (side : Stacks K) (rs : Regs 5 w) (i : Fin 5)
    (a : Word w) : Function.update (framed k res side rs) (reg i) (wordBits a) =
      framed k res side (Function.update rs i a) := by
  funext z
  cases z with
  | input | result => rfl
  | aux z =>
    rcases z with z | z
    · cases z with
      | reg j => by_cases eq : j=i <;> simp [framed, reg, OrdinalRead.bank, PrefixWords.bank, ISA.bank, eq]
      | _ => rfl
    · rfl

private theorem result_eq (k : ℕ) (old new : List Bool) (side : Stacks K) (rs : Regs 5 w) :
    Function.update (framed k old side rs) .result new = framed k new side rs := by
  funext z; cases z <;> rfl

private theorem prepare_runs (k : ℕ) (side : Stacks K) : prepare.Runs ((w+1)+(5*w+2))
    (OrdinalRead.bank w k [] (idle (w := w) side)) (framed k [] side (PrefixWords.words (w := w) 0 k 0 0)) := by
  let s := framed k [] side (PrefixWords.words (w := w) 0 0 0 0)
  let mid := Function.update s (reg 2) []
  have clear := CallClear.clear_runs (reg 2) s
  have hlen : (s (reg 2)).length = w := length_wordBits _
  rw [hlen] at clear
  have copy := SuccessorFields.prependCopy_runs (K := Host K) .input (reg 2) tmp
    (by simp [reg]) (by simp [tmp]) (by simp [reg,tmp]) mid (by rfl)
  have hi : mid .input = digits w k := rfl
  have hd : mid (reg 2) = [] := Function.update_self ..
  rw [hi, hd, List.append_nil, length_digits] at copy
  have write : Function.update mid (reg 2) (digits w k) = framed k [] side (PrefixWords.words (w := w) 0 k 0 0) := by
    dsimp only [mid]
    rw [Function.update_idem]
    change Function.update s (reg 2) (wordBits (Fin.ofNat (2^w) k)) = _
    rw [show s = framed k [] side (PrefixWords.words (w := w) 0 0 0 0) from rfl, reg_eq]
    congr 1
    funext i; fin_cases i <;> rfl
  rw [write] at copy
  exact clear.followedBy copy

omit [DecidableEq K] in
private theorem framed_len {A : ℕ} (hw : w ≤ A) (k : ℕ) (result : List Bool) (hres : result.length ≤ A)
    (side : Stacks K) (hside : ∀ j, (side j).length ≤ A) (rs : Regs 5 w) (z : Host K) :
    ((framed k result side rs) z).length ≤ A := by
  cases z with
  | input => exact (length_digits ..).le.trans hw
  | result => exact hres
  | aux z => rcases z with z | z
             · exact (RegisterTable.bank_length_le Fin.elim0 0 rs z).trans hw
             · exact hside z

private theorem reset_exec (cursor ordinal rank len : ℕ) :
    reset.exec (PrefixWords.words (w := w) cursor ordinal rank len) = PrefixWords.words 0 0 0 0 := by
  funext i; fin_cases i <;> rfl

private theorem reset_runs {A : ℕ} (hw : w ≤ A) (k : ℕ) (side : Stacks K) (hs : ∀ j, (side j).length ≤ A)
    (cursor rank len : ℕ) : ∃ t ≤ registerClock w reset,
      (reset.compile.onPorts (OrdinalRead.Port.aux ∘ Sum.inl)).BoundedRun (A+registerClock w reset) t
        (framed k (digits w cursor) side (PrefixWords.words (w := w) cursor k rank len))
        (OrdinalRead.bank w k (digits w cursor) (idle (w := w) side)) := by
  let f : ISA.Port 5 0 → Host K := OrdinalRead.Port.aux ∘ Sum.inl
  let bank' := framed (w := w) k (digits w cursor) side
  have regs : RegisterBank f bank' 0 := by
    refine ⟨fun i j eq ↦ Sum.inl.inj (OrdinalRead.Port.aux.inj eq), fun _ _ ↦ rfl, ?_⟩
    intro a b z out
    cases z with
    | input | result => rfl
    | aux z => rcases z with z | z
               · exact (out z rfl).elim
               · rfl
  let before := PrefixWords.words (w := w) cursor k rank len
  obtain ⟨t, ht, run⟩ := registerCall_runs regs reset before (A+registerClock w reset) (Nat.add_le_add_right hw _)
    (fun z _ ↦ (framed_len hw k _ ((length_digits ..).le.trans hw) side hs before z).trans (Nat.le_add_right ..))
  change (reset.compile.onPorts f).BoundedRun _ _ _ (bank' (reset.exec before)) at run
  rw [show reset.exec before = PrefixWords.words (w := w) 0 0 0 0 from reset_exec ..] at run
  exact ⟨t, ht, run⟩

/-- Time outside the prefix scanner, including all initialization and reclamation. -/
def overhead (w : ℕ) := ((w+1)+(5*w+2))+(5*w+2)+registerClock w reset

/-- The fixed five-register scanner supplies a true scalar-index callback,
including its unchanged input and a reusable ready workspace. -/
theorem correctSpace {r n w T S : ℕ} (g : Fin r → Fin n) (scan : FiniteRoutine (Aux K))
    (side : Stacks K) (hside : ∀ j, (side j).length ≤ S) (hw : w ≤ S)
    (scans : ∀ i : Fin r, ∃ t ≤ T, ∃ rank len : ℕ, scan.BoundedRun S t
      (PrefixWords.bank side (PrefixWords.words (w := w) 0 i.val 0 0))
      (PrefixWords.bank side (PrefixWords.words (w := w) (g i).val i.val rank len))) :
    OrdinalRead.CorrectSpace (machine scan) g w (T+overhead w) (S+overhead w) (· = idle (w := w) side) := by
  intro i s ready
  subst s
  let gval := (g i).val
  obtain ⟨t, ht, rank, len, scanning⟩ := scans i
  let pre := (w+1)+(5*w+2)
  let copying := 5*w+2
  let cap := S+overhead w
  have setup := prepare_runs (w := w) i.val side
  have smallPre : prepare.BoundedRun cap pre (OrdinalRead.bank w i.val [] (idle (w := w) side))
      (framed i.val [] side (PrefixWords.words (w := w) 0 i.val 0 0)) := by
    apply spaceRun_of_steps setup
    intro z
    have hz := framed_len hw i.val [] (Nat.zero_le _) side hside (PrefixWords.words (w := w) 0 0 0 0) z
    exact Nat.add_le_add hz (by dsimp [pre,overhead]; omega)
  let rs := PrefixWords.words (w := w) gval i.val rank len
  have largeScan : (scan.onPorts OrdinalRead.Port.aux).BoundedRun cap t
      (framed i.val [] side (PrefixWords.words (w := w) 0 i.val 0 0)) (framed i.val [] side rs) := by
    refine FiniteRoutine.BoundedRun.framed (r := scan) (fun _ _ h ↦ OrdinalRead.Port.aux.inj h)
      (scanning.mono_cap (show S ≤ cap from Nat.le_add_right ..))
      smallPre.final_cap (fun _ ↦ rfl) (fun _ ↦ rfl) ?_
    intro z outside
    cases z <;> first | rfl | exact (outside _ rfl).elim
  let mid := framed i.val [] side rs
  have move := SuccessorFields.prependCopy_runs (K := Host K) (reg 0) .result tmp (by simp [reg]) (by simp [reg,tmp])
    (by simp [tmp]) mid (by rfl)
  have hsrc : mid (reg 0) = digits w gval := rfl
  have hd : mid .result = [] := rfl
  rw [hsrc, hd, List.append_nil, length_digits, result_eq] at move
  have moved := spaceRun_of_steps (cap := cap) move fun z ↦
    Nat.add_le_add (framed_len hw i.val [] (Nat.zero_le _) side hside rs z) (by dsimp [overhead]; omega)
  obtain ⟨u, hu, clean⟩ := reset_runs hw i.val side hside gval rank len
  have bigClean := clean.mono_cap (show S+registerClock w reset ≤ cap by dsimp [cap, overhead]; omega)
  refine ⟨((pre+t)+copying)+u, ?_, idle (w := w) side, rfl,
    ((smallPre.followedBy largeScan).followedBy moved).followedBy bigClean⟩
  dsimp only [pre, copying, overhead]
  omega

end RankQuery.Stack.Coordinate.OrdinalABI

end VPVNP
end Computability
end OAI
