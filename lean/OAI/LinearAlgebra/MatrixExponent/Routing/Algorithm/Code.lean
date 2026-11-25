import OAI.LinearAlgebra.MatrixExponent.Coloring.Vector
import OAI.LinearAlgebra.MatrixExponent.Transport.System

section
/-!
# Deterministic straight-line word programs

A program contains its literal bits and words. A gate stores four bits.
The children of a tabulation are a finite array of programs, fixed before
evaluation. The evaluator materializes each result array once. The word
accounting uses pointers to immutable pairs and arrays.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
open Coloring

inductive Code (w : ℕ) : Type → Type → Type 1
  | id {A} : Code w A A
  | fst {A D} : Code w (A × D) A
  | snd {A D} : Code w (A × D) D
  | comp {A D E} : Code w A D → Code w D E → Code w A E
  | pair {A D E} : Code w A D → Code w A E → Code w A (D × E)
  | select {A} : Code w (Bool × A × A) A
  | tab {A D} {h} : h ≤ w → (B h → Code w A D) → Code w A (B h → D)
  | «at» {A} {h} : h ≤ w → B h → Code w (B h → A) A
  | read {A} {h} : h ≤ w → Code w ((B h → A) × B h) A
  | bit {A} : Bool → Code w A Bool
  | lit {A} {h} : h ≤ w → B h → Code w A (B h)
  | gate : Bool → Bool → Bool → Bool → Code w (Bool × Bool) Bool
  | lt {h} : h ≤ w → Code w (B h × B h) Bool
  | eq {h} : h ≤ w → Code w (B h × B h) Bool
  | add {h} : h ≤ w → Code w (B h × B h) (B h)
  | resize {h k} : h ≤ w → k ≤ w → Code w (B h) (B k)
  | odd {h} : h ≤ w → Code w (B h) Bool
  | halve {h} : h ≤ w → Code w (B h) (B h)

namespace Code
variable {w h : ℕ} {A D : Type}

/-- Materialize the child array, whose entries can then be read by index. -/
def tabulate (hh : h ≤ w) (f : B h → Code w A D) : Code w A (B h → D) :=
  let a := Vector.ofFn f
  tab hh (fun i => a[i.val])

def eval : {A D : Type} → Code w A D → A → D
  | _, _, .id, x => x
  | _, _, .fst, x => x.1
  | _, _, .snd, x => x.2
  | _, _, .comp f g, x => g.eval (f.eval x)
  | _, _, .pair f g, x => (f.eval x, g.eval x)
  | _, _, .select, x => if x.1 then x.2.1 else x.2.2
  | _, _, .tab _ f, x =>
    let a := Vector.ofFn (fun i => (f i).eval x)
    fun i => a[i.val]
  | _, _, .at _ i, x => x i
  | _, _, .read _, x => x.1 x.2
  | _, _, .bit b, _ => b
  | _, _, .lit _ i, _ => i
  | _, _, .gate a b c d, x => if x.1 then (if x.2 then d else c) else (if x.2 then b else a)
  | _, _, .lt _, x => decide (x.1 < x.2)
  | _, _, .eq _, x => decide (x.1 = x.2)
  | _, _, .add _, x => x.1 + x.2
  | _, _, .resize _ _, x => Fin.ofNat _ x.val
  | _, _, .odd _, x => decide (x.val % 2 = 1)
  | _, _, .halve _, x => ⟨x.val / 2, (Nat.div_le_self ..).trans_lt x.isLt⟩

/-- Charge each instruction once and each table slot once. -/
def charge (header slot : ℕ) : {A D : Type} → Code w A D → ℕ
  | _, _, .comp f g => header + charge header slot f + charge header slot g
  | _, _, .pair f g => header + charge header slot f + charge header slot g
  | _, _, .tab _ f => header + ∑ i, (slot + charge header slot (f i))
  | _, _, _ => header

/-- Reserve an opcode, literal/width fields, and child references in an
eight-word header. Each tabulation has one additional reference per child. -/
def advice (c : Code w A D) := charge 8 1 c

/-- A frame holds operands, result and continuation. Pairs can stay in
the frame. Tabulation allocates one extra result word per slot. -/
def scratch (c : Code w A D) := charge 8 1 c

/-- Word cost with a fixed charge for dispatch, operations and frame
access. A table slot includes reading its child offset and writing its result. -/
def time (c : Code w A D) := charge 16 4 c

end Code
end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
end

/-! # A permutation system with distinct exterior and channel widths -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transport
open Coloring
open scoped Classical
variable {F : Type} {h p w n : ℕ}

/-- The exterior and interior record lengths may be different. -/
structure PaddedSystem (F : Type) (h p w n : ℕ) where
  selector : Format
  config : Format
  dispatch : ((Perm h).pair selector).obj → (Controls h p config).obj
  group : Port h p → ℕ
  kernel : config.obj → (Fin w → Bool) → (Fin w → Bool) → Channels p n → F

abbrev PaddedPins (A : Format) (p w n : ℕ) :=
  A.pins ⊕ Fin w ⊕ Fin w ⊕ (B p × Fin n)

namespace PaddedSystem
variable (S : PaddedSystem F h p w n)

def localWeight (x : PaddedPins S.config p w n → Bool) : F :=
  S.kernel (S.config.code.symm (x ∘ Sum.inl)) (fun i => x (.inr (.inl i)))
    (fun i => x (.inr (.inr (.inl i)))) (fun i => x (.inr (.inr (.inr i))))

variable [Field F]

def value (v : (Controls h p S.config).obj) (x y : Site h → Fin w → Bool)
    (c : Site h → Channels p n) : F :=
  ∏ i, S.kernel (v i).1 (x i) (y i) (c i)

/-- Transmission is counted in bits, including both ends of each link. -/
def Correct (C : ℕ) : Prop :=
  ∀ (σ : Equiv.Perm (B h)) (x y : Site h → Fin w → Bool),
    (∀ t c, let v := S.dispatch (σ, t)
      S.value v x y c ≠ 0 → Valid S.group (commands v) ∧
        (Enabled (commands v)).card * n ≤ C * 2 ^ h * w) ∧
    (if ∀ i, x i = y (Routing.inflate h σ i) then (1 : F) else 0) =
      ∑ t : S.selector.pins → Bool, ∑ c : Site h → Channels p n,
        let v := S.dispatch (σ, S.selector.code.symm t)
        S.value v x y c * (if Joins (commands v) c then 1 else 0)

end PaddedSystem

end OAI.LinearAlgebra.MatrixExponent.Transport
end
