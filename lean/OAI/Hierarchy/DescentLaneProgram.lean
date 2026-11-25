import OAI.Hierarchy.DescentBoundedBitHistory
import OAI.Hierarchy.DescentRotorAlphabet

namespace OAI
namespace Hierarchy.DescentLaneGates
open DescentKernelHistory DescentResetGates
noncomputable section
variable {A : Type} {width : A→ℕ} {Y p : ℕ}

/-- Exactly one physical cable or terminal and two natural numbers describe the complete operand. -/
structure Lane (p : ℕ) (width : A→ℕ) where
  port : A
  start : ℕ
  stride : ℕ
  fits : ∀j : Fin p,start+stride*j.val<width port

def Lane.atBit (l : Lane p width) (d : Fin p) : BitRef width := ⟨l.port,l.start+l.stride*d.val,l.fits d⟩

def Lane.word (l : Lane p width) (x : BitRef width→Bool) : Word p := fun j=>x (l.atBit j)

structure Op (Y p : ℕ) (width : A→ℕ) where
  tag : CanonicalTag Y
  arity : ℕ
  arg : Fin arity→Lane p width

structure Program (Y p : ℕ) (width : A→ℕ) where
  Node : Type
  [finite : Fintype Node]
  op : Node→Op Y p width
attribute [instance] Program.finite

def Program.recipe (q : Program Y p width) : BitRecipe (CanonicalTag Y) A width where
  Hidden := Empty
  hiddenWidth := Empty.elim
  Node := q.Node
  tag i := (q.op i).tag
  arity i := (q.op i).arity
  size _ _ := p
  arg i j d := .inl (((q.op i).arg j).atBit d)

end
end Hierarchy.DescentLaneGates

end OAI
