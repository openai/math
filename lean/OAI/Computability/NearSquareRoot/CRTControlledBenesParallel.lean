import OAI.Computability.NearSquareRoot.CRTControlledBenesRun
import OAI.Computability.NearSquareRoot.CRTControlledDispatch

/-! # Simultaneous execution of the compiled switches

Each full address retains an external control field. Its value selects a separate
table in each block. A physical stage permutes the packed records by sending each
record to the address obtained by applying the active local switch in every block.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes

open IntegerMultiplication IntegerMultiplication.Code

abbrev PackedAddress (E : Type*) {B : Type*} (width : B → ℕ) :=
  E × ((b : B) → Word (width b))

def controlledPerm {E B : Type*} {width : B → ℕ}
    (p : E → (b : B) → Equiv.Perm (Word (width b))) : Equiv.Perm (PackedAddress E width) where
  toFun x := (x.1, fun b => p x.1 b (x.2 b))
  invFun x := (x.1, fun b => (p x.1 b).symm (x.2 b))
  left_inv x := by simp
  right_inv x := by simp

/-- The element initially at `x` is written to `e x`. -/
def scatter {D V : Type*} (e : Equiv.Perm D) : Equiv.Perm (D → V) :=
  e.arrowCongr (Equiv.refl _)

private theorem scatter_fold {D V A : Type*} (step : A → Equiv.Perm D)
    (s : List A) (v : D → V) (x : D) :
    (s.foldl (fun v a => scatter (step a) v) v)
      (s.foldl (fun x a => step a x) x) = v x := by
  induction s generalizing v x with
  | nil => rfl
  | cons a s ih =>
    simpa [scatter] using ih (scatter (step a) v) (step a x)

private theorem controlled_fold {E B A : Type*} {w : B → ℕ}
    (p : A → E → (b : B) → Equiv.Perm (Word (w b))) (s : List A)
    (x : PackedAddress E w) :
    s.foldl (fun x a => controlledPerm (p a) x) x =
      (x.1, fun b => s.foldl (fun y a => p a x.1 b y) (x.2 b)) := by
  induction s generalizing x with
  | nil => rfl
  | cons a s ih => exact ih (controlledPerm (p a) x)

/-- One common half-stage of all compiled block tables. -/
def packedStage {E B : Type*} (width : B → ℕ) (t : E → B → RawTable) (a : Bool × ℕ) :
    Equiv.Perm (PackedAddress E width) :=
  controlledPerm fun e b => stagePerm (d := width b) (t e b) a.1 a.2

theorem packedStages_run {E B : Type*} (w : B → ℕ) (t : E → B → RawTable)
    (p : E → (b : B) → Equiv.Perm (Word (w b))) (ht : ∀ e b, RawRepresents (p e b) (t e b))
    (D : ℕ) (hw : ∀ b, w b ≤ D) (x : PackedAddress E w) :
    (executionOrder D).foldl (fun y a => packedStage w t a y) x = controlledPerm p x := by
  unfold packedStage
  rw [controlled_fold]
  exact congrArg (Prod.mk x.1) (funext fun b =>
    stagesPerm_padded_run (p x.1 b) (t x.1 b) (ht x.1 b) (x.2 b) D (hw b))

theorem packedData_run {E B V : Type*} (w : B → ℕ) (t : E → B → RawTable)
    (p : E → (b : B) → Equiv.Perm (Word (w b))) (ht : ∀ e b, RawRepresents (p e b) (t e b))
    (D : ℕ) (hw : ∀ b, w b ≤ D) (v : PackedAddress E w → V) :
    (executionOrder D).foldl (fun v a => scatter (packedStage w t a) v) v =
      scatter (controlledPerm p) v := by
  funext y
  let x := (controlledPerm p).symm y
  have hs := scatter_fold (packedStage w t) (executionOrder D) v x
  rw [packedStages_run w t p ht D hw, (controlledPerm p).apply_symm_apply y] at hs
  exact hs

/-- A single P192 program consumes the emitted stages, transports each descriptor and
executes the packed physical switches. All blocks and external control values share the
same stage command. -/
theorem chargedPackedStages {X : Type*} {E B V : X → Type*}
    (w : (x : X) → B x → ℕ) (t : (x : X) → E x → B x → RawTable)
    (p : (x : X) → E x → (b : B x) → Equiv.Perm (Word (w x b)))
    (ht : ∀ x e b, RawRepresents (p x e b) (t x e b))
    (D : X → ℕ) (hw : ∀ x b, w x b ≤ D x)
    (key : X → Bool × ℕ → Tree) (box : (x : X) → (PackedAddress (E x) (w x) → V x) → Tree)
    (charge : X → Bool × ℕ → ℕ) (allowance : X → ℕ)
    (step : Task (fun i : (x : X) × {a // a ∈ executionOrder (D x)} ×
        (PackedAddress (E x) (w x) → V x) => charge i.1 i.2.1)
      (fun i => .fork (key i.1 i.2.1) (box i.1 i.2.2))
      (fun i => box i.1 (scatter (packedStage (w i.1) (t i.1) i.2.1) i.2.2)))
    (bound : ∀ x, ∀ a ∈ executionOrder (D x), charge x a + (key x a).count + 1 ≤ allowance x) :
    Task (fun i : (x : X) × (PackedAddress (E x) (w x) → V x) => 2 * D i.1 * allowance i.1 + 1)
      (fun i => .fork (Task.forest (key i.1) (executionOrder (D i.1))) (box i.1 i.2))
      (fun i => box i.1 (scatter (controlledPerm (p i.1)) i.2)) := by
  have run := Controlled.physicalSchedule (fun x => executionOrder (D x)) key box
    (fun x a => scatter (packedStage (w x) (t x) a)) charge allowance step bound
  exact run.conform (fun _ => by rw [executionOrder_length]) (fun _ => rfl)
    (fun i => by rw [packedData_run (w i.1) (t i.1) (p i.1) (ht i.1) (D i.1) (hw i.1)])

end Benes

end NearSquareRoot
end Computability
end OAI
