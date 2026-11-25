import OAI.Computability.BorderVNP.CrossingNetwork
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

namespace OAI
/-! # Parallel equal copies on common physical cables -/

namespace Hierarchy.DescentInitialHost
open Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [CommSemiring F] {D : ℕ} {P : Type*} {bits : P → ℕ}
variable (N : Network D P bits)

def stacked (s : ℕ) : Network D P (fun p => s*bits p) where
  Site := N.Site
  Edge := N.Edge
  finiteSite := N.finiteSite
  finiteEdge := N.finiteEdge
  src := N.src
  dst := N.dst
  width e := s*N.width e
  attach := N.attach
  position := N.position
  in_ball := N.in_ball

def rowAt {s w : ℕ} (a : Fin (s*w) → Bool) (i : Fin s) : Fin w → Bool :=
  fun j => a (finProdFinEquiv (i,j))

def stackRows {s w : ℕ} (a : Fin s → Fin w → Bool) : Fin (s*w) → Bool :=
  fun z => a (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2

@[simp] theorem rowAt_stackRows {s w : ℕ} (a : Fin s → Fin w→Bool) (i : Fin s) :
    rowAt (stackRows a) i=a i := by funext j;simp [rowAt,stackRows]

def stackAssignment (s : ℕ) : (Fin s → N.Assignment) ≃ (stacked N s).Assignment where
  toFun a e := stackRows fun i => a i e
  invFun z i e := rowAt (z e) i
  left_inv a := by funext i e j;simp
  right_inv a := by
    funext e j
    change a e (finProdFinEquiv ((finProdFinEquiv.symm j).1,(finProdFinEquiv.symm j).2)) = a e j
    exact congrArg (a e) (finProdFinEquiv.apply_symm_apply j)

def stackTable {s : ℕ} (T : N.Tables F) : (stacked N s).Tables F :=
  fun v z x => ∏i : Fin s,T v (fun e => rowAt (z e) i) (fun p => rowAt (x p) i)

/-- Local bit order is the physical row then the bit on the old cable.
Summing once over the widened cables gives the full product of copies. -/
theorem stack_value (s : ℕ) (T : N.Tables F) (x : Ports (fun p => s*bits p)) :
    (stacked N s).value (stackTable N T) x=∏ i : Fin s,N.value T (fun p => rowAt (x p) i) := by
  classical
  unfold Network.value
  rw [Fintype.prod_sum]
  rw [←(stackAssignment N s).sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  change (∏ v : N.Site, ∏ i : Fin s, T v
    (fun e => rowAt (stackRows (fun j => a j e.val)) i) (fun p => rowAt (x p.val) i)) =
    ∏ i : Fin s, ∏ v : N.Site, T v (fun e => a i e.val) (fun p => rowAt (x p.val) i)
  simp only [rowAt_stackRows]
  exact Finset.prod_comm (f:=fun v (i : Fin s) => T v (fun e => a i e.val) (fun p => rowAt (x p.val) i))

end
end Hierarchy.DescentInitialHost

end OAI
