import OAI.Computability.VPVNP.RankQueryStackEngineSpec
import OAI.Computability.VPVNP.SliceArithmeticConstant
import OAI.Computability.VPVNP.SliceArithmeticCallClear
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-! # Terminal and arity arms of the physical Schur dispatch -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Describe

open Engine RAMTape
open TapeWord (ScanPort)
open SliceArithmeticRound (packed)

/-- Auxiliary stacks used by the description arms, comprising six descriptor words, the
extension modulus coefficients, and two scratch stacks for writing field literals. -/
inductive Wire where
  | desc (i : Fin 6) | coeff | scratch | extra
  deriving DecidableEq, Fintype

variable {K : Type} {p e n U Z w v : ℕ} {c : SliceArithmetic.Vector p e}

/-- Embed one of the ten live Schur frame slots into the stack ports of the interpreter. -/
def livePort (i : Fin 10) : Engine.Port K := .frame (.inl i)

/-- Push the descriptor branch bit onto the engine's condition stack. A true bit signals a
returned scalar and a false bit starts a child scan. -/
def signal (b : Bool) : FiniteRoutine (Engine.Port K) := .ofRoutine (Routine.push .condition b)

/-- Connect the constant writer's input and work stacks to the coefficient, extra and scratch
wires, and send its packed scalar to `out`. -/
def literalPorts (bank : Wire ↪ K) (out : Engine.Port K) : ScanPort → Engine.Port K
  | .left => .aux (bank .coeff)
  | .right => .aux (bank .extra)
  | .tmp => .aux (bank .scratch)
  | .out => out

/-- Write the packed scalar one for `true` or zero for `false` to the selected engine port,
using the field advice on the coefficient wire. -/
def literal (bank : Wire ↪ K) (out : Engine.Port K) (b : Bool) : FiniteRoutine (Engine.Port K) :=
  (SliceArithmeticConstant.machine b).onPorts (literalPorts bank out)

/-- The ten stacks holding the current Schur frame, in field order, which the terminal arm
clears on return. -/
def livePorts : List (Engine.Port K) := (List.finRange 10).map livePort

/-- Clear the ten live frame fields and push the true return signal once the scalar result is
in place. -/
def finish : FiniteRoutine (Engine.Port K) :=
  (SliceArithmetic.CallClear.cleanup livePorts).followedBy (signal true)

/-- Return the constant selected by `b` from a Schur leaf by writing its packed scalar,
clearing the live frame and signaling completion. -/
def terminal (bank : Wire ↪ K) (b : Bool) : FiniteRoutine (Engine.Port K) :=
  (literal bank .result b).followedBy finish

/-- Start a child scan by copying descriptor word one into the remaining-child count, setting
the scalar accumulator to zero and pushing the false signal. -/
def arity (bank : Wire ↪ K) : FiniteRoutine (Engine.Port K) :=
  ((SuccessorFields.prependCopy (.aux (bank (.desc 1))) (livePort 7) (.aux (bank .scratch))).followedBy
    (literal bank (livePort 8) false)).followedBy (signal false)

/-- The coefficient wire holds the packed vector `c` at limb width `v`, and the scratch and
extra wires are empty for a constant write. -/
def Clean (bank : Wire ↪ K) (v : ℕ) (c : SliceArithmetic.Vector p e) (aux : Stacks K) : Prop :=
  aux (bank .coeff) = packed v (List.ofFn c) ∧ aux (bank .scratch) = [] ∧ aux (bank .extra) = []

variable [DecidableEq K] [Fact p.Prime] [NeZero e]

omit [DecidableEq K] in
private theorem literal_injective (bank : Wire ↪ K) (out : Engine.Port K) (ho : ∀ i, .aux (bank i) ≠ out) :
    Function.Injective (literalPorts bank out) := by
  intro x y h
  cases x <;> cases y <;> simp_all [literalPorts]

/-- The scalar selected by a constant descriptor in `Scalar c`, equal to one for `true` and
zero for `false`. -/
def constant (c : SliceArithmetic.Vector p e) (b : Bool) : Scalar c := if b then 1 else 0

omit [NeZero e] in
private theorem scalar_constant (b : Bool) : scalar v (constant c b) =
    packed v (List.ofFn (SliceArithmeticConstant.literal b p e)) := by
  cases b with
  | false => change packed v (List.ofFn (Scalar.pack c (SliceArithmetic.zero p e)).digits) = _
             rw [Scalar.digits_pack]; rfl
  | true => change packed v (List.ofFn (Scalar.pack c (SliceArithmetic.one p e)).digits) = _
            rw [Scalar.digits_pack]; rfl

theorem literal_runs (hw : SliceArithmetic.Word.workingWidth p ≤ v) (bank : Wire ↪ K)
    (out : Engine.Port K) (ho : ∀ i, .aux (bank i) ≠ out) (b : Bool) (s : Stacks (Engine.Port K))
    (hcoeff : s (.aux (bank .coeff)) = packed v (List.ofFn c))
    (hscratch : s (.aux (bank .scratch)) = []) (hextra : s (.aux (bank .extra)) = []) (hout : s out = []) :
    (literal bank out b).Runs (7*(e*v)+3) s (Function.update s out (scalar v (constant c b))) := by
  have h := SliceArithmeticConstant.machine_runs (NeZero.pos e) hw b c []
  apply (SliceArithmeticConstant.machine b).runs_onPorts_framed (literal_injective bank out ho) (by simpa using h)
  · intro z; cases z <;> assumption
  · intro z; cases z <;> simp [literalPorts, ho, hcoeff, hscratch, hextra, scalar_constant, TapeWord.scanStacks]
  · intro z hz; exact Function.update_of_ne (Ne.symm (hz .out)) ..

private theorem enter_width (q : SchurKey n U Z) (j : Fin 10) :
    ((fields w [] q [] [] []) j).length ≤ w := by
  refine Fin.cases (Nat.zero_le _) (fun j => ?_) j
  refine Fin.addCases (motive := fun i => (Fin.append (fun x : Fin 6 => UniversalCountStack.digits w (q.words x))
    ![[],[],[]] i).length ≤ w) (fun x : Fin 6 => ?_) (fun x : Fin 3 => ?_) j
  · rw [Fin.append_left,UniversalCountStack.length_digits]
  · rw [Fin.append_right]; fin_cases x <;> exact Nat.zero_le _

private theorem clear_eq (data saved : Data) (res : List Bool) (aux : Stacks K) :
    SliceArithmetic.CallClear.erased livePorts (store data saved [] res aux) =
    store (fun _ => []) saved [] res aux := by
  funext k
  cases k with
  | frame k =>
    cases k with
    | inl j => simp [SliceArithmetic.CallClear.erased,livePorts,livePort,store]
    | inr j => simp [SliceArithmetic.CallClear.erased,livePorts,livePort,store]
  | _ => simp [SliceArithmetic.CallClear.erased,livePorts,livePort,store]

omit [Fact p.Prime] [NeZero e] in
theorem finish_runs (q : SchurKey n U Z) (fs : List (F n U Z c)) (r : Scalar c) (aux : Stacks K) :
    ∃ t ≤ 10*(w+1)+2, finish.Runs t
      (store (fields w [] q [] [] []) (history w v fs) [] (scalar v r) aux)
      (atControl w v (.returned r) fs aux [true]) := by
  let init := store (fields w [] q [] [] []) (history w v fs) [] (scalar v r) aux
  obtain ⟨t,ht,hclear⟩ := SliceArithmetic.CallClear.cleanup_runs livePorts init w (by
    intro i hi
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
    exact enter_width ..)
  rw [show init = _ from rfl, clear_eq] at hclear
  let mid := store (fun _ => []) (history w v fs) [] (scalar v r) aux
  have hpush := Routine.runs_push (Engine.Port.condition (K := K)) true mid
  have finalEq : Function.update mid .condition (true :: mid .condition) =
      atControl w v (.returned r) fs aux [true] := by funext k; cases k with | frame z => cases z <;> rfl | _ => rfl
  rw [finalEq] at hpush
  exact ⟨_, by simpa [livePorts] using Nat.add_le_add_right ht 1, hclear.followedBy hpush⟩

theorem terminal_runs (hw : SliceArithmetic.Word.workingWidth p ≤ v) (bank : Wire ↪ K)
    (q : SchurKey n U Z) (fs : List (F n U Z c)) (aux : Stacks K) (hc : Clean bank v c aux) (b : Bool) :
    ∃ t ≤ 7*(e*v)+3 + (10*(w+1)+2), (terminal bank b).Runs t
      (atControl w v (.enter q) fs aux) (atControl w v (.returned (constant c b)) fs aux [true]) := by
  let init := atControl w v (.enter q) fs aux
  have hl := literal_runs hw bank .result (fun i h => by contradiction) b init hc.1 hc.2.1 hc.2.2 rfl
  have he : Function.update init .result (scalar v (constant c b)) =
      store (fields w [] q [] [] []) (history w v fs) [] (scalar v (constant c b)) aux := by
    funext k; cases k with | frame z => cases z <;> rfl | _ => rfl
  rw [he] at hl
  obtain ⟨t,ht,hf⟩ := finish_runs q fs (constant c b) aux
  exact ⟨_, Nat.add_le_add_left ht _, hl.followedBy hf⟩

theorem arity_runs (hw : SliceArithmetic.Word.workingWidth p ≤ v) (bank : Wire ↪ K)
    (q : SchurKey n U Z) (fs : List (F n U Z c)) (aux : Stacks K) (hc : Clean bank v c aux)
    (k : ℕ) (hk : aux (bank (.desc 1)) = UniversalCountStack.digits w k) :
    (arity bank).Runs ((5*w+2)+(7*(e*v)+3)+1)
      (atControl w v (.enter q) fs aux) (atControl w v (.scan q k 0) fs aux [false]) := by
  let init := atControl w v (.enter q) fs aux
  let mid := store (fields w [] q (UniversalCountStack.digits w k) [] []) (history w v fs) [] [] aux
  let loaded := atControl w v (.scan q k 0) fs aux
  have hcopy := SuccessorFields.prependCopy_runs (.aux (bank (.desc 1)) : Engine.Port K)
    (livePort 7) (.aux (bank .scratch)) (by intro h; contradiction)
    (fun h => by have := bank.injective (Engine.Port.aux.inj h); contradiction)
    (by intro h; contradiction) init hc.2.1
  have hlen : (init (.aux (bank (.desc 1)))).length = w := by change (aux _).length = _; simp [hk]
  have midEq : Function.update init (livePort 7) (init (.aux (bank (.desc 1))) ++ init (livePort 7)) = mid := by
    funext z; cases z with
    | frame z => rcases z with z | z
                 · fin_cases z <;> first | rfl | (change aux (bank (.desc 1)) ++ [] = UniversalCountStack.digits w k; simp [hk])
                 · rfl
    | _ => rfl
  rw [midEq,hlen] at hcopy
  have hlit := literal_runs hw bank (livePort 8) (fun i h => by contradiction) false mid hc.1 hc.2.1 hc.2.2 rfl
  have loadEq : Function.update mid (livePort 8) (scalar v (constant c false)) = loaded := by
    funext z; cases z with
    | frame z => rcases z with z | z
                 · fin_cases z <;> rfl
                 · rfl
    | _ => rfl
  rw [loadEq] at hlit
  have hpush := Routine.runs_push (Engine.Port.condition (K := K)) false loaded
  have finalEq : Function.update loaded .condition (false :: loaded .condition) =
      atControl w v (.scan q k 0) fs aux [false] := by funext z; cases z with | frame j => cases j <;> rfl | _ => rfl
  rw [finalEq] at hpush
  exact (hcopy.followedBy hlit).followedBy hpush

end RankQuery.Stack.Describe

end VPVNP
end Computability
end OAI
