import OAI.LinearAlgebra.MatrixExponent.Diagram.Permute
import OAI.LinearAlgebra.MatrixExponent.Diagram.Wide

/-!
# Bit networks as finite directed multigraphs

Every argument slot belongs either to a named exterior position or to
one end of an internal edge. The two bijections specify this incidence
without requiring a topological order. In particular, loops are allowed.
-/

namespace OAI.LinearAlgebra.MatrixExponent

structure Diagram (F : Type) (a b : Wire) where
  V : Type
  [fv : Fintype V]
  E : Type
  [fe : Fintype E]
  table : V → Table F
  src : (Σ v, slots (table v).1) ≃ slots a ⊕ E
  dst : (Σ v, slots (table v).2.1) ≃ slots b ⊕ E

attribute [instance] Diagram.fv Diagram.fe

namespace Diagram
variable {F : Type} {a b : Wire} (G : Diagram F a b)

def arity (v : G.V) : ℕ := wd (G.table v).1 + wd (G.table v).2.1
def cost : ℕ := ∑ v, (1 + G.arity v)

def Trivalent : Prop := ∀ v, G.arity v ≤ 3
def Admits (u : ℕ) (L : Set (Table F)) : Prop :=
  ∀ v, G.arity v ≤ u ∧ (G.arity v ≤ 3 ∨ G.table v ∈ L)

def source (e : G.E) : G.V := (G.src.symm (.inr e)).1
def target (e : G.E) : G.V := (G.dst.symm (.inr e)).1

/-- Weight of one station before the internal edge bits are summed. -/
def vertex (x : Val a) (y : Val b) (z : G.E → Bool) (v : G.V) : F :=
  (G.table v).2.2
    ((bits (G.table v).1).symm (fun i => Sum.elim (bits a x) z (G.src ⟨v, i⟩)))
    ((bits (G.table v).2.1).symm (fun i => Sum.elim (bits b y) z (G.dst ⟨v, i⟩)))

noncomputable def eval [Field F] (x : Val a) (y : Val b) : F := by
  classical
  exact ∑ z : G.E → Bool, ∏ v, G.vertex x y z v

end Diagram
end OAI.LinearAlgebra.MatrixExponent
