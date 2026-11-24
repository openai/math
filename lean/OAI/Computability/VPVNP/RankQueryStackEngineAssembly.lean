import OAI.Computability.VPVNP.RankQueryStackScanSetup
import OAI.Computability.VPVNP.RankQueryStackStages
import OAI.Computability.VPVNP.RankQueryStackMultiplyAdd

/-!
# Linking the Schur determinant callbacks

A single shared binary register bank computes child queries. Its output words
are copied into the emptied live registers only after the parent's frame has
been saved. The accumulator callback uses the native extension-field arithmetic.
The remaining installation point reads and interprets the matrix descriptor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Engine.Assembly

open RAMTape UniversalCountStack Dispatch

variable {K : Type} [DecidableEq K]

/-- Auxiliary stack holding one pending child-query word in the dispatcher's output register
bank. -/
def source (bank : EngineAlias.Small ↪ K) (i : Fin 6) := bank (.reg (Code.outReg capacity i))

/-- Link the descriptor, child dispatcher, activation and field multiply-add routines into the
evaluator's actions. -/
def actions (bank : EngineAlias.Small ↪ K) (tmp : K) (mac : MultiplyAdd.Aux → K)
    (descriptor : FiniteRoutine (Engine.Port K)) : Actions K where
  describe := descriptor
  scan := ScanCall.scan tmp (EngineAlias.stageChild bank false)
  activate := Activate.machine (source bank) tmp
  right := ScanCall.right tmp (EngineAlias.stageChild bank true)
  multiplyAdd := MultiplyAdd.machine mac

variable {n U Z p e w v : ℕ} {c : SliceArithmetic.Vector p e}

/-- The descriptor's additional state occupies ports outside the shared
Schur register bank. The field-arithmetic advice and scratch also persist. -/
def Ready (bank : EngineAlias.Small ↪ K) (tmp : K) (mac : MultiplyAdd.Aux → K)
    (extra : Stacks K → Prop) (n w v : ℕ) (c : SliceArithmetic.Vector p e) (s : Stacks K) : Prop :=
  EngineAlias.Ready bank w n s ∧ s tmp = [] ∧ MultiplyAdd.Ready mac v c s ∧ extra s

/-- The auxiliary bank is ready and its six pending output registers encode the specified Schur
key. -/
def Pending (bank : EngineAlias.Small ↪ K) (tmp : K) (mac : MultiplyAdd.Aux → K)
    (extra : Stacks K → Prop) (w v : ℕ) (c : SliceArithmetic.Vector p e)
    (q : Key n U Z) (s : Stacks K) : Prop :=
  Ready bank tmp mac extra n w v c s ∧ ∀ i, s (source bank i) = digits w (q.words i)

/-- Step allowance for local child dispatch, scalar multiply-add and movement of the encoded
words. -/
def localBudget (w e v : ℕ) : ℕ :=
  (Operation.left.clock w + Operation.right.clock w) + MultiplyAdd.callCap e v +
    100*(w+e*v+1)

variable [Fact p.Prime] [NeZero e]

/-- Every call except the descriptor is instantiated here with an executable
finite bit-stack routine. The descriptor may have a separate, larger clock. -/
theorem contracts {s Bd : ℕ} (bank : EngineAlias.Small ↪ K) (tmp : K) (mac : MultiplyAdd.Aux → K)
    (hm : Function.Injective mac) (htmp : ∀ i, bank i ≠ tmp) (hmac : ∀ i j, bank i ≠ mac j)
    (extra : Stacks K → Prop) (hex : ∀ a b, extra a → (∀ j, (∀ i, bank i ≠ j) → b j = a j) → extra b)
    (desc : FiniteRoutine (Engine.Port K)) (entry : Entry n (Scalar c))
    (hn : n ≤ 2^s) (hu : U ≤ 2^s) (hz : Z ≤ 2^s) (hp : 2*s+6 ≤ w)
    (hw : (2*s+6+1)*widthFactor ≤ w) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (hd : ∀ (q : Key n U Z) (fs : List (F n U Z c)) aux,
      Ready bank tmp mac extra n w v c aux → ∃ t ≤ Bd, ∃ out, Ready bank tmp mac extra n w v c out ∧
        desc.Runs t (atControl w v (.enter q) fs aux)
          (match (SchurKey.program entry).describe q with
           | .inl r => atControl w v (.returned r) fs out [true]
           | .inr k => atControl w v (.scan q k 0) fs out [false])) :
    Contracts (actions bank tmp mac desc) (SchurKey.program (U := U) (Z := Z) entry) w v (localBudget w e v)
      (SchurKey.arityBound n U Z) (Ready bank tmp mac extra n w v c) (Pending bank tmp mac extra w v c) Bd := by
  have preserve (q : Key n U Z) (aux out : Stacks K) (ha : Ready bank tmp mac extra n w v c aux)
      (pending : EngineAlias.Pending bank w q out)
      (outside : ∀ j, (∀ i, bank i ≠ j) → out j = aux j) : Pending bank tmp mac extra w v c q out :=
    ⟨⟨pending.1, (outside _ htmp).trans ha.2.1,
      fun i => (outside _ (fun j => hmac j i)).trans (ha.2.2.1 i), hex aux out ha.2.2.2 outside⟩,
      pending.2⟩
  constructor
  · exact hd
  · intro q acc fs aux ready
    obtain ⟨t, ht, run⟩ := ScanCall.zero_runs (w := w) (v := v) tmp (EngineAlias.stageChild bank false) q acc fs aux ready.2.1
    exact ⟨t, by dsimp [localBudget]; omega, aux, ready, run⟩
  · intro q k acc fs aux hk valid ready
    have hb := EngineAlias.inputs_bounded s hn hu hz q (k+1) hk
    have h6 : k+1 < 2^(2*s+6) := hb 6
    have hkfit := h6.trans_le (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hp)
    obtain ⟨tc, ht, out, pend, child, outside⟩ := EngineAlias.stageChild_runs bank false entry q k valid
      [] (scalar v acc) [] (history w v fs) [] [] aux ready.1
      (EngineAlias.inputs_bounded s hn hu hz q k (by omega)) hp hw
    have ho := preserve ((SchurKey.program entry).left q k) aux out ready pend outside
    obtain ⟨t, ht', run⟩ := ScanCall.succ_runs tmp _ q k acc fs aux out ready.2.1 hkfit child
    change tc ≤ Operation.left.clock w at ht
    exact ⟨t, by dsimp [localBudget]; omega, out, ho, run⟩
  · intro q fs aux pend
    have run := Activate.machine_runs (source bank) tmp (fun i => htmp _) w v q fs aux pend.1.2.1 pend.2
    exact ⟨_, by dsimp [localBudget]; omega, aux, pend.1, run⟩
  · intro q k acc l fs aux hk valid ready
    obtain ⟨tc, ht, out, pend, child, outside⟩ := EngineAlias.stageChild_runs bank true entry q k valid
      [] (scalar v acc) [] (history w v fs) [] (scalar v l) aux ready.1
      (EngineAlias.inputs_bounded s hn hu hz q k hk.le) hp hw
    have ho := preserve ((SchurKey.program entry).right q k) aux out ready pend outside
    have run := ScanCall.right_runs tmp _ q k acc l fs aux out ho.1.2.1 child
    change tc ≤ Operation.right.clock w at ht
    exact ⟨_, by dsimp [localBudget]; omega, out, ho, run⟩
  · intro q k acc l r fs aux _ ready
    obtain ⟨t,ht,run⟩ := MultiplyAdd.machine_runs mac hm hv w q k acc l r fs aux ready.2.2.1
    exact ⟨t, by dsimp [localBudget]; omega, aux, ready, run⟩

end RankQuery.Stack.Engine.Assembly

end VPVNP
end Computability
end OAI
