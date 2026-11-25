import OAI.Computability.BorderVNP.TeamSignedStack
import OAI.Computability.VPVNP.RAMTapeNamed

/-! # A total signed validator with a unary stack clock

A timeout rejects canonically before the next instruction. One stack holds one bit per
remaining instruction. All other stacks and all genuine nondeterministic choices agree with
the original machine. The stopping bound applies on arbitrary stack contents and controls.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamGuard

open VPVNP.RAMTape TeamStack VPVNP.UniversalMachine StackCompiler

variable {K L Q R : Type*} [DecidableEq K] [DecidableEq L]

/-- Signed counts are preserved by relabeling the registers and finite control. -/
theorem paths_lift {src : StackCode K Q} {target : StackCode L R} {neg : Q → Bool} {neg' : R → Bool}
    (ports : K → L) (hp : Function.Injective ports) (labels : Q → R) (base : Stacks L)
    (hc : ∀ q, target (labels q) = (src q).rename ports labels) (hs : ∀ q, neg' (labels q) = neg q)
    (t : ℕ) (q : Q) (s : Stacks K) :
    TeamStack.paths target neg' t (labels q) (installStacks ports base s) = TeamStack.paths src neg t q s := by
  induction t generalizing q s with
  | zero => rfl
  | succ t ih =>
    rw [TeamStack.paths, hc, TeamStack.paths]
    cases src q <;> simp only [StackOp.rename, Function.comp_apply, installStacks_at hp,
      installStacks_update hp, ih, hs]

/-- Deterministic preparatory steps preserve the entire signed count at the remaining clock. -/
theorem runs_paths {src : StackCode K Q} {t q s q' s'} (run : StackRuns src t q s q' s')
    (neg : Q → Bool) (fuel : ℕ) :
    TeamStack.paths src neg (fuel+t) q s = TeamStack.paths src neg fuel q' s' := by
  induction run with
  | nil => rfl
  | cons hs _ ih => cases hs <;> simp_all [TeamStack.paths]

/-- Signed version of the named-port compiler, with the program's literal prefix on input. -/
theorem prefix_named [Fintype K] [Fintype Q] (input : K) (code : StackCode K Q)
    (neg : Q → Bool) (start : Q) (payload : Word) (T : ℕ) :
    let P := machine (labeledCode input code) neg start
    let raw := programPrefix P ++ payload
    StopsWithin code T start (labeledInput input raw) →
    T * (6 * (raw.length + (Fintype.card K+1) + T) + 4) ≤ raw.length^100 →
    signedCount raw.get = TeamStack.paths code neg T start (labeledInput input raw) := by
  intro P raw stops clock
  have h := (stopsWithin_lift (target := labeledCode input code) (labeledPort input)
    (labeledPort_injective input) id (inputStacks raw) (fun _ => rfl) T start _).2 stops
  have hp := paths_lift (target := labeledCode input code) (neg := neg) (neg' := neg) (labeledPort input)
    (labeledPort_injective input) id (inputStacks raw) (fun _ => rfl) (fun _ => rfl) T start (labeledInput input raw)
  rw [installedInput] at h hp
  exact (prefix_value (labeledCode input code) neg start payload T h clock).trans hp

/-- Before each instruction, a fresh state pops a single tick from the budget. -/
inductive Phase (Q : Type*) where
  | check (q : Q)
  | execute (q : Q)
  | timeout
  deriving Fintype

/-- The validator can only access its own ports, independently of the dedicated fuel stack. -/
def code (src : StackCode K Q) : StackCode (K ⊕ Unit) (Phase Q)
  | .check q => .pop (.inr ()) fun b => if b.isSome then .execute q else .timeout
  | .execute q => (src q).rename Sum.inl Phase.check
  | .timeout => .halt false

/-- Timeouts and clock checks have zero sign bit. -/
def negative (neg : Q → Bool) : Phase Q → Bool
  | .execute q => neg q
  | _ => false

/-- The clock stack is disjoint from the original data, including the input. -/
def bank (s : Stacks K) (fuel : ℕ) : Stacks (K ⊕ Unit) :=
  Sum.elim s fun _ => List.replicate fuel true

private theorem consume (s : Stacks K) (t : ℕ) :
    Function.update (bank s (t+1)) (.inr ()) ((bank s (t+1) (.inr ())).tail) = bank s t := by
  funext i
  cases i with
  | inl => simp [bank]
  | inr u => cases u; simp [bank, List.replicate_succ]

omit [DecidableEq K] in
@[simp] private theorem bank_inl (s : Stacks K) (t : ℕ) (k : K) : bank s t (.inl k) = s k := rfl

private theorem modify (s : Stacks K) (t : ℕ) (k : K) (v : List Bool) :
    Function.update (bank s t) (.inl k) v = bank (Function.update s k v) t := by
  funext i
  cases i with
  | inl j => by_cases h : j = k <;> simp [bank, h]
  | inr u => simp [bank]

/-- On every initial bank, malformed or otherwise, the guarded validator stops and returns
precisely the signed path sum of its source at the fuel limit. -/
theorem executes (src : StackCode K Q) (neg : Q → Bool) (q : Q) (s : Stacks K) (fuel : ℕ) :
    StopsWithin (code src) (2*fuel+2) (.check q) (bank s fuel) ∧
    TeamStack.paths (code src) (negative neg) (2*fuel+2) (.check q) (bank s fuel) =
      TeamStack.paths src neg fuel q s := by
  induction fuel generalizing q s with
  | zero => simp [StopsWithin, TeamStack.paths, code, bank, TeamTape.haltWeight]
  | succ t ih =>
    rw [show 2*(t+1)+2 = ((2*t+2)+1)+1 by omega]
    generalize he : 2*t+2 = left at ih ⊢
    have hp : (bank s (t+1) (.inr ())).head?.isSome = true := by simp [bank, List.replicate_succ]
    simp only [StopsWithin, code, hp, ↓reduceIte, consume, TeamStack.paths]
    cases h : src q with
    | push k b r => simpa only [StackOp.rename, bank_inl, modify] using ih r (Function.update s k (b :: s k))
    | pop k f => simpa only [StackOp.rename, Function.comp_apply, bank_inl, modify] using ih (f (s k).head?) (Function.update s k (s k).tail)
    | goto r => exact ih r s
    | choose l r => exact ⟨⟨(ih l s).1, (ih r s).1⟩, congrArg₂ (· + ·) (ih l s).2 (ih r s).2⟩
    | halt b => simp [negative]

end TeamGuard

end BorderVNP
end Computability
end OAI
