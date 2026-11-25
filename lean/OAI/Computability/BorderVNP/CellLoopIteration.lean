import OAI.Computability.BorderVNP.CellLoopBound
import OAI.Computability.BorderVNP.CellLoopCounter
import OAI.Computability.BorderVNP.CellRecordScan

/-! # Executing one repetition of a sparse private command block

The body stays in one persistent private stack. The current binary index is prepended to
a working copy of the enclosing environment, and the child sees only the copied body,
its extended environment, and the shared reverse-output stack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator.Loop

open VPVNP.RAMTape RationalHitting.StackLanguage

/-- Private registers of one active loop, independent of its trip count. -/
inductive Aux where
  | limit | remaining | index | callRow | callEnv | temp
  deriving DecidableEq

instance : Fintype Aux := derive_fintype% _

/-- Local and enclosing ports used by a loop dispatch. -/
abbrev Ports := IO ⊕ Aux

/-- Stack contents at boundaries inside a repeated invocation. -/
structure Frame where
  /-- Compact repeated command body. -/
  row : List Bool
  /-- Encoded enclosing counter list. -/
  env : List Bool
  /-- Emitted instructions in reverse bit order. -/
  out : List Bool
  /-- Expression staging register. -/
  limit : List Bool := []
  /-- Number of outstanding copies, in unary. -/
  remaining : List Bool := []
  /-- Binary ordinal of the current copy. -/
  index : List Bool := []
  /-- Body copy passed to the child. -/
  callRow : List Bool := []
  /-- Lexical environment passed to the child. -/
  callEnv : List Bool := []
  /-- Temporary copy of the index to frame. -/
  temp : List Bool := []

/-- Port interpretation at an actual loop boundary. -/
def Frame.store (f : Frame) : Stacks Ports
  | .inl .row => f.row
  | .inl .env => f.env
  | .inl .out => f.out
  | .inr .limit => f.limit
  | .inr .remaining => f.remaining
  | .inr .index => f.index
  | .inr .callRow => f.callRow
  | .inr .callEnv => f.callEnv
  | .inr .temp => f.temp

/-- Change one named stack, with the remaining contents kept verbatim. -/
def Frame.set (f : Frame) (k : Ports) (w : List Bool) : Frame :=
  match k with
  | .inl .row => {f with row := w}
  | .inl .env => {f with env := w}
  | .inl .out => {f with out := w}
  | .inr .limit => {f with limit := w}
  | .inr .remaining => {f with remaining := w}
  | .inr .index => {f with index := w}
  | .inr .callRow => {f with callRow := w}
  | .inr .callEnv => {f with callEnv := w}
  | .inr .temp => {f with temp := w}

theorem Frame.update_store (f : Frame) (k : Ports) (w : List Bool) :
    Function.update f.store k w = (f.set k w).store := by
  funext i
  rcases k with k | k <;> rcases i with i | i <;> cases k <;> cases i <;> simp [store,set]

/-- Child port routing at a loop iteration. -/
def childPorts : IO → Ports
  | .row => .inr .callRow
  | .env => .inr .callEnv
  | .out => .inl .out

private theorem childPorts_inj : Function.Injective childPorts := by
  intro i j h; cases i <;> cases j <;> simp_all [childPorts]

/-- A complete repeat body, down to deterministic stack instructions. -/
def iteration (child : Fragment IO) : Fragment Ports :=
  (Fragment.copyWord (.inl .row) (.inr .callRow)).seq <|
  (Fragment.copyWord (.inl .env) (.inr .callEnv)).seq <|
  (Fragment.copyWord (.inr .index) (.inr .temp)).seq <|
  (Fragment.prepend (.inr .temp) (.inr .callEnv)).seq <|
  (child.mount childPorts).seq <|
  (Fragment.erase (.inr .callEnv)).seq (Fragment.advance (.inr .index))

/-- The repeat body adds a linear allowance in the copied fields and binary index. -/
def overhead (body env : List Bool) (i : ℕ) : ℕ := 120*(body.length+env.length+i.bits.length+1)+120

/-- One iteration runs its child on the current index and leaves the next canonical index,
including at a binary carry. The saved body and all remaining iteration markers survive. -/
theorem iteration_run (child : Fragment IO) (body env out newOut remain : List Bool)
    (i : ℕ) {t : ℕ} (hchild : child.Runs t (io body (codeWord i.bits ++ env) out)
      (io [] (codeWord i.bits ++ env) newOut)) :
    let f : Frame := {row := body,env := env,out := out,remaining := remain,index := i.bits}
    ∃ d ≤ overhead body env i + t,
      (iteration child).Runs d f.store ({f with out := newOut, index := (i+1).bits}).store := by
  intro f
  let f₁ : Frame := {f with callRow := body}
  let f₂ : Frame := {f₁ with callEnv := env}
  let f₃ : Frame := {f₂ with temp := i.bits}
  let f₄ : Frame := {f₃ with temp := [], callEnv := codeWord i.bits ++ env}
  let f₅ : Frame := {f₄ with callRow := [], out := newOut}
  let f₆ : Frame := {f₅ with callEnv := []}
  obtain ⟨a,ha,ra⟩ := Fragment.copyWord_run (src := (Sum.inl IO.row : Ports)) (dst := .inr .callRow) (by simp) f.store
  rw [Frame.update_store] at ra
  obtain ⟨b,hb,rb⟩ := Fragment.copyWord_run (src := (Sum.inl IO.env : Ports)) (dst := .inr .callEnv) (by simp) f₁.store
  rw [Frame.update_store] at rb
  obtain ⟨c,hc,rc⟩ := Fragment.copyWord_run (src := (Sum.inr Aux.index : Ports)) (dst := .inr .temp) (by simp) f₂.store
  rw [Frame.update_store] at rc
  obtain ⟨d,hd,rd⟩ := Fragment.prepend_run (src := (Sum.inr Aux.temp : Ports)) (dst := .inr .callEnv) (by simp) f₃.store
  rw [Frame.update_store,Frame.update_store] at rd
  have re : (child.mount childPorts).Runs t f₄.store f₅.store := by
    apply child.runs_mount childPorts_inj hchild
    · intro k; cases k <;> rfl
    · intro k; cases k <;> rfl
    · intro k hk
      rcases k with k|k <;> cases k <;> first | rfl | exact (hk .out rfl).elim | exact (hk .row rfl).elim
  obtain ⟨g,hg,rg⟩ := Fragment.erase_run (.inr .callEnv) f₅.store
  rw [Frame.update_store] at rg
  obtain ⟨j,hj,rj⟩ := Fragment.advance_run (.inr .index) f₆.store i rfl
  rw [Frame.update_store] at rj
  refine ⟨a+(b+(c+(d+(t+(g+j))))), ?_, ?_⟩
  · simp only [Frame.store, f, f₁, f₂, f₃, f₄, f₅, List.length_nil, mul_zero, add_zero,
      List.length_append, codeWord_length] at ha hb hc hd hg
    unfold overhead
    omega
  · exact Fragment.runs_seq _ _ ra (Fragment.runs_seq _ _ rb (Fragment.runs_seq _ _ rc
      (Fragment.runs_seq _ _ rd (Fragment.runs_seq _ _ re (Fragment.runs_seq _ _ rg rj)))))

end CellMacro.Generator.Loop

end BorderVNP
end Computability
end OAI
