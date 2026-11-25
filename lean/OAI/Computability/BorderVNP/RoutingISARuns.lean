import OAI.Computability.BorderVNP.RoutingISA

/-!
# Execution of structured team assembly

The trace retains every fetched old word, binary branch choice, private macro
choice, and signed contribution. A conditional or loop test takes one ordinary
tick. A straight-line operation uses the same action and word semantics as
the physical instruction dispatcher.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Contents of all 64 word registers. -/
abbrev Bank (w : ℕ) := Reg → Word w

/-- Ordinary no-probe instruction event. -/
def tick (w : ℕ) : TeamRAM.Event w := ⟨.ordinary none, [], [], .plus⟩

/-- One binary guess, retaining its identity in the trace. -/
def choiceTick (w : ℕ) (b : Bool) : TeamRAM.Event w := ⟨.ordinary none, [], [b], .plus⟩

/-- Single instruction with a fall-through destination. -/
def Code.isAtom : Code → Bool
  | .nop | .constant .. | .publicWord .. | .copy .. | .binary .. | .load .. | .store .. |
    .sign .. | .call .. => true
  | _ => false

/-- Data and signed contribution of one primitive statement, ignoring just its
fixed successor PC. Division and remainder reject on a zero divisor. -/
def Code.atom {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (s : Bank w) :
    Code → TeamRAM.Instr w (Bank w)
  | .nop => .localStep s .plus
  | .constant d v => .localStep (Function.update s d (Fin.ofNat _ v.val)) .plus
  | .publicWord d i => .localStep (Function.update s d (pub i)) .plus
  | .copy d x => .localStep (Function.update s d (s x)) .plus
  | .binary op d x y =>
    if (op = .div ∨ op = .mod) ∧ s y = 0 then .reject
    else .localStep (Function.update s d (op.eval (s x) (s y))) .plus
  | .load d a => .load (s a) (Function.update s d)
  | .store a v => .store (s a) (s v) s
  | .sign b => .localStep s (if b then .minus else .plus)
  | .call j a l => .call (s a) (s l).val (macros j) s
  | .accept => .accept
  | _ => .reject

/-- Normal return of one fixed assembly fragment. Early rejection or acceptance
does not return to the fragment's continuation. -/
inductive Runs {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) :
    Code → Bank w → Memory w → List (TeamRAM.Event w) → Bank w → Memory w → Prop where
  | atom {c s m a s' sign bits} (hc : c.isAtom = true)
      (ha : (c.atom pub macros s).action = some a)
      (hs : (c.atom pub macros s).advance bits (TeamRAM.previous m a) = some (s', sign)) :
      Runs pub macros c s m [⟨a, TeamRAM.previous m a, bits, sign⟩] s' (TeamRAM.afterAction m a)
  | seq {a b s m es s' m' fs s'' m''} (first : Runs pub macros a s m es s' m')
      (second : Runs pub macros b s' m' fs s'' m'') :
      Runs pub macros (.seq a b) s m (es ++ fs) s'' m''
  | ifEq {x y a b s m es s' m'} (h : Runs pub macros (if s x = s y then a else b) s m es s' m') :
      Runs pub macros (.ifEq x y a b) s m (tick w :: es) s' m'
  | ifLt {x y a b s m es s' m'} (h : Runs pub macros (if s x < s y then a else b) s m es s' m') :
      Runs pub macros (.ifLt x y a b) s m (tick w :: es) s' m'
  | choose {a b s m es s' m'} (bit : Bool)
      (h : Runs pub macros (if bit then a else b) s m es s' m') :
      Runs pub macros (.choose a b) s m (choiceTick w bit :: es) s' m'
  | whileDone {x y body s m} (h : ¬ s x < s y) :
      Runs pub macros (.whileLt x y body) s m [tick w] s m
  | whileStep {x y body s m es s' m' fs s'' m''} (guard : s x < s y)
      (step : Runs pub macros body s m es s' m')
      (loop : Runs pub macros (.whileLt x y body) s' m' fs s'' m'') :
      Runs pub macros (.whileLt x y body) s m (tick w :: (es ++ fs)) s'' m''

/-- Native execution up to a control-flow join, retaining the final registers
and actual memory. -/
inductive NativePrefix {w : ℕ} {S : Type*} (P : S → TeamRAM.Instr w S) :
    S → Memory w → List (TeamRAM.Event w) → S → Memory w → Prop where
  | nil (s m) : NativePrefix P s m [] s m
  | cons {s m a bits next sign rest z mz}
      (ha : (P s).action = some a)
      (hs : (P s).advance bits (TeamRAM.previous m a) = some (next, sign))
      (tail : NativePrefix P next (TeamRAM.afterAction m a) rest z mz) :
      NativePrefix P s m (⟨a, TeamRAM.previous m a, bits, sign⟩ :: rest) z mz

/-- Sequencing two fetched native paths preserves all the events and states. -/
theorem NativePrefix.append {w : ℕ} {S : Type*} {P : S → TeamRAM.Instr w S} {s m es t mt fs z mz}
    (first : NativePrefix P s m es t mt) (second : NativePrefix P t mt fs z mz) :
    NativePrefix P s m (es ++ fs) z mz := by
  induction first with
  | nil => exact second
  | cons ha hs _ ih => exact .cons ha hs (ih second)

/-- Closing a native prefix at an actual accepting halt gives the exact
shared-memory execute result on the recorded binary choices. -/
theorem NativePrefix.execute {w : ℕ} {S : Type*} {P : S → TeamRAM.Instr w S} {s m es t mt}
    (h : NativePrefix P s m es t mt) (halt : P t = .accept) :
    TeamRAM.execute P s m (es.map TeamRAM.Event.choices) = some es := by
  induction h with
  | nil => simp [TeamRAM.execute, halt]
  | cons ha hs _ ih => simp [TeamRAM.execute, ha, hs, ih halt]

/-- Execute a fixed single instruction which takes an ordinary local tick. -/
theorem Runs.localStep {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s s' : Bank w} (m : Memory w) (hc : c.isAtom = true)
    (h : c.atom pub macros s = .localStep s' .plus) :
    Runs pub macros c s m [tick w] s' m :=
  .atom hc (by rw [h]; rfl) (by rw [h]; rfl)

/-- Load from the actual word address and record its previous contents. -/
theorem Runs.load {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (d a : Reg) (s : Bank w) (m : Memory w) :
    Runs pub macros (.load d a) s m [⟨.ordinary (some ((s a).val, none)), [m (s a).val], [], .plus⟩]
      (Function.update s d (m (s a).val)) m :=
  .atom rfl rfl rfl

/-- Store a shared word, preserving its true prior value in the chronological record. -/
theorem Runs.store {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (a v : Reg) (s : Bank w) (m : Memory w) :
    Runs pub macros (.store a v) s m
      [⟨.ordinary (some ((s a).val, some (s v))), [m (s a).val], [], .plus⟩]
      s (Function.update m (s a).val (s v)) :=
  .atom rfl rfl rfl

end RoutingISA

end BorderVNP
end Computability
end OAI
