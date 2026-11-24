import OAI.Computability.VPVNP.SliceArithmeticAdd
import OAI.Computability.VPVNP.SliceArithmeticCallPorts
import OAI.Computability.VPVNP.SliceArithmeticCallCopies

/-!
# Vector addition with a clean calling convention

The two operand streams belong to the caller. A copy of the degree markers
controls the scan, and copies of the modulus and zero word initialize its
registers. The scan consumes the query and writes its result directly onto
the accumulator. The registers are reclaimed before the call returns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.AddCall

open RAMTape BurstRAM
open SliceArithmeticStreamRow (state StreamPort)
open SliceArithmeticRound (packed)
open MultiplyCall (External external)

/-- Ports for a reusable scalar addition call, pairing its coefficient-scan workspace with the
caller's field and operand stacks. -/
abbrev Port := SliceArithmeticStreamRow.Port Unit ⊕ External

/-- The caller's external stacks, with every private port empty. -/
def clean (io : Stacks External) : Stacks Port := Sum.elim (fun _ => []) io

private def reg (i : Fin 8) : Port := .inl (.inl (.reg i))
private def persistent : Port := .inl (.inl .persistent)
private def marker : Port := .inl (.inr (.outer ()))
private def scratch : Port := .inl (.inr .scratch)

private def regSource (i : Fin 8) : External := if i = 0 then .prime else .zeroWord

private def copies : List (Port × Port) :=
  (.inr .degree, marker) :: (.inr .zeroWord, persistent) ::
    List.ofFn (fun i : Fin 8 => (Sum.inr (regSource i), reg i))

private def occupied : List Port := persistent :: List.ofFn reg

private def scanPort : SliceArithmeticStreamRow.Port Unit → Port
  | .inr .coeff => .inr .acc
  | .inr .factor => .inr .query
  | i => .inl i

private theorem scanPort_injective : Function.Injective scanPort := by
  rintro (i | i) (j | j)
  · exact fun h => Sum.inl.inj h
  · cases j <;> simp [scanPort]
  · cases i <;> simp [scanPort]
  · cases i <;> cases j <;> simp [scanPort]

/-- The coefficient scan has one fixed table for each prime-field operation. -/
def operation (op : Word.Op) : FiniteRoutine Port :=
  ((CallCopies.copyPlan scratch copies).followedBy
    ((SliceArithmeticAdd.vectorOp op ()).onPorts scanPort)).followedBy (CallClear.cleanup occupied)

/-- Initialization, the vector scan, and register cleanup, in bit-stack steps. -/
def callCap (e w : ℕ) : ℕ :=
  (10 * (5 * (e + w) + 2) + 1) +
    (e * (200 * (w + 1) ^ 2 + 17 * w + 8) + 2 * (e * w) + 2) + (9 * (w + 1) + 1)

private def privateStreams (rows : ℕ) : Stacks (StreamPort Unit)
  | .outer () => List.replicate rows true
  | _ => []

private def frame {w : ℕ} (r : Fin 8 → BurstRAM.Word w) (rows : ℕ) (io : Stacks External) :
    Stacks Port := Sum.elim (state r (privateStreams rows)) io

private def registers (p w : ℕ) (i : Fin 8) : BurstRAM.Word w :=
  if i = 0 then Fin.ofNat _ p else 0

private theorem valid : CallCopies.Valid scratch copies := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro k hk
    simp only [copies, List.map_cons, List.map_ofFn, List.mem_cons, List.mem_ofFn,
      Function.comp_apply] at hk ⊢
    rcases hk with rfl | rfl | ⟨i, rfl⟩ <;> simp [reg, persistent, marker]
  · simp [copies, scratch]
  · simp [copies, scratch, marker, persistent, reg]

private theorem prepare_runs {p e w : ℕ} (c b a : List Bool) :
    ∃ t ≤ 10 * (5 * (e + w) + 2) + 1, (CallCopies.copyPlan scratch copies).Runs t
      (clean (external p e w c b a)) (frame (registers p w) e (external p e w c b a)) := by
  let s := clean (external p e w c b a)
  obtain ⟨t, ht, run⟩ := CallCopies.copyPlan_runs scratch copies s (e+w) valid rfl (by
    intro pair h
    simp only [copies, List.mem_cons, List.mem_ofFn] at h
    rcases h with rfl | rfl | ⟨i, rfl⟩ <;> rfl) (by
    intro pair h
    simp only [copies, List.mem_cons, List.mem_ofFn] at h
    rcases h with rfl | rfl | ⟨i, rfl⟩
    · simp [s, clean, external]
    · simp [s, clean, external]
    · by_cases hi : i = 0 <;> simp [s, clean, regSource, external, hi])
  have hreg (i : Fin 8) : CallCopies.copied copies s (reg i) = s (.inr (regSource i)) :=
    CallCopies.copied_at copies s valid.1 (p := (.inr (regSource i), reg i))
      (by simp only [copies, List.mem_cons, List.mem_ofFn]; exact Or.inr (Or.inr ⟨i, rfl⟩))
  have hm : CallCopies.copied copies s marker = s (.inr .degree) :=
    CallCopies.copied_at copies s valid.1 (List.mem_cons_self ..)
  have hper : CallCopies.copied copies s persistent = s (.inr .zeroWord) :=
    CallCopies.copied_at copies s valid.1 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have he : CallCopies.copied copies s = frame (registers p w) e (external p e w c b a) := by
    funext j
    rcases j with (k | k) | k
    · cases k with
      | reg i => by_cases hi : i = 0 <;> simpa [s, clean, frame, state, reg, registers, ISA.bank, regSource, hi,
          external] using hreg i
      | pub i => exact i.elim0
      | persistent => exact hper
      | work i => rw [CallCopies.copied_outside] <;> simp [s, clean, frame, state, ISA.bank, copies, reg,
          marker, persistent]
      | logPort i => rw [CallCopies.copied_outside] <;> cases i <;> simp [s, clean, frame, state, ISA.bank,
          ISA.logStacks, AddressLog.keys, AddressLog.values, copies, reg, marker, persistent]
    · cases k with
      | outer x => cases x; exact hm
      | _ => rw [CallCopies.copied_outside] <;> simp [s, clean, frame, state, privateStreams, copies,
          reg, marker, persistent]
    · rw [CallCopies.copied_outside] <;> simp [s, clean, frame, copies, reg, marker, persistent]
  rw [he] at run
  exact ⟨t, by simpa [copies] using ht, run⟩

private theorem reclaim {w : ℕ} (r : Fin 8 → BurstRAM.Word w) (io : Stacks External) :
    ∃ t ≤ 9 * (w + 1) + 1, (CallClear.cleanup occupied).Runs t (frame r 0 io) (clean io) := by
  obtain ⟨t, ht, run⟩ := CallClear.cleanup_runs occupied (frame r 0 io) w (by
    intro i hi
    simp only [occupied, List.mem_cons, List.mem_ofFn] at hi
    rcases hi with rfl | ⟨j, rfl⟩ <;> simp [frame, state, reg, persistent, ISA.bank])
  have he : CallClear.erased occupied (frame r 0 io) = clean io := by
    funext j
    rcases j with (k | k) | k
    · cases k with
      | reg i =>
        have hi : reg i ∈ occupied := List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
        exact ite_eq_left hi
      | pub i => exact i.elim0
      | persistent => exact ite_eq_left (List.mem_cons_self ..)
      | work i => simp [CallClear.erased, occupied, reg, persistent, frame, clean, state, ISA.bank]
      | logPort i => cases i <;> simp [CallClear.erased, occupied, reg, persistent, frame, clean, state,
          ISA.bank, ISA.logStacks, AddressLog.keys, AddressLog.values]
    · cases k <;> simp [CallClear.erased, occupied, reg, persistent, frame, clean, state, privateStreams]
    · simp [CallClear.erased, occupied, reg, persistent, frame, clean]
  rw [he] at run
  exact ⟨t, by simpa [occupied] using ht, run⟩

/-- Consume the query and replace the accumulator by the coefficientwise result. -/
theorem operation_runs (op : Word.Op) {p e w : ℕ} [NeZero p] (hw : Word.workingWidth p ≤ w) (a b : Vector p e)
    (coeff : List Bool) :
    ∃ t ≤ callCap e w, (operation op).Runs t
      (clean (external p e w coeff (packed w (List.ofFn b)) (packed w (List.ofFn a))))
      (clean (external p e w coeff [] (packed w (List.ofFn (fun i => op.eval (a i) (b i)))))) := by
  let input := external p e w coeff (packed w (List.ofFn b)) (packed w (List.ofFn a))
  let output := external p e w coeff [] (packed w (List.ofFn (fun i => op.eval (a i) (b i))))
  obtain ⟨t, ht, init⟩ := prepare_runs (p := p) (e := e) (w := w) coeff (packed w (List.ofFn b))
    (packed w (List.ofFn a))
  obtain ⟨n, next, hn, _, scan⟩ := SliceArithmeticAdd.vectorOp_runs op hw () (fun _ => []) (registers p w)
    (by simpa [registers] using Nat.mod_eq_of_lt (Word.modulus_lt hw)) a b
  have run : ((SliceArithmeticAdd.vectorOp op ()).onPorts scanPort).Runs n
      (frame (registers p w) e input) (frame next 0 output) := by
    apply FiniteRoutine.runs_onPorts_framed _ scanPort_injective scan
    · rintro (i | i)
      · rfl
      · cases i <;> simp [scanPort, frame, state, SliceArithmeticAdd.streams, privateStreams, input, external]
    · rintro (i | i)
      · rfl
      · cases i <;> simp [scanPort, frame, state, SliceArithmeticAdd.streams, privateStreams, output, external]
    · rintro ((i | i) | i) h
      · exact (h (.inl i) rfl).elim
      · cases i with
        | old | coeff | factor | out | scratch => rfl
        | outer x => exact (h (.inr (.outer x)) rfl).elim
      · cases i with
        | query => exact (h (.inr .factor) rfl).elim
        | acc => exact (h (.inr .coeff) rfl).elim
        | _ => rfl
  obtain ⟨k, hk, done⟩ := reclaim next output
  exact ⟨_, Nat.add_le_add (Nat.add_le_add ht hn) hk, (init.followedBy run).followedBy done⟩

/-- Add two packed coefficient vectors with the shared field-arithmetic port convention. -/
def machine : FiniteRoutine Port := operation .add

/-- Add the query to the accumulator, consuming the query and reclaiming every
private stack. The modulus, zero word, degree markers and coefficient advice
are available to subsequent calls. -/
theorem machine_runs {p e w : ℕ} [NeZero p] (hw : Word.workingWidth p ≤ w) (a b : Vector p e)
    (coeff : List Bool) :
    ∃ t ≤ callCap e w, machine.Runs t
      (clean (external p e w coeff (packed w (List.ofFn b)) (packed w (List.ofFn a))))
      (clean (external p e w coeff [] (packed w (List.ofFn (add a b))))) :=
  operation_runs .add hw a b coeff

end SliceArithmetic.AddCall

end VPVNP
end Computability
end OAI
