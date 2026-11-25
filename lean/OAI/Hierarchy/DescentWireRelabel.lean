import OAI.Computability.BorderVNP.BitVolume
import Mathlib.Tactic

namespace OAI
/-! # Change the bit numbering of each physical wire and exterior pin -/

namespace Hierarchy.DescentWireRelabel
open Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section
variable {D : ℕ} {P : Type*} {bits : P→ℕ} (N : Network D P bits)
variable (wire : ∀e,Equiv.Perm (Fin (N.width e))) (pin : ∀p,Equiv.Perm (Fin (bits p)))

/-- Each permutation sends an old bit index to its newly stored index. -/
def word {n : ℕ} (π : Equiv.Perm (Fin n)) : (Fin n→Bool) ≃ (Fin n→Bool) :=
  Equiv.arrowCongr π.symm (Equiv.refl Bool)

def assignments : N.Assignment ≃ N.Assignment := Equiv.piCongrRight fun e=>word (wire e)
def pins : Ports bits ≃ Ports bits := Equiv.piCongrRight fun p=>word (pin p)

def tables {K : Type*} (T : N.Tables K) : N.Tables K := fun v a x=>
  T v (fun e=>word (wire e.val) (a e)) (fun p=>word (pin p.val) (x p))

theorem read {K : Type*} (T : N.Tables K) (a : N.Assignment) (x : Ports bits) (v : N.Site) :
    N.read (tables N wire pin T) a x v=N.read T (assignments N wire a) (pins pin x) v := rfl

theorem value {K : Type*} [CommSemiring K] (T : N.Tables K) (x : Ports bits) :
    N.value (tables N wire pin T) x=N.value T (pins pin x) := by
  unfold Network.value
  simp only [read]
  exact (assignments N wire).sum_comp (fun a : N.Assignment=>∏v,N.read T a (pins pin x) v)

theorem value_encoded {K : Type*} [CommSemiring K] (T : N.Tables K) (x : Ports bits) :
    N.value (tables N wire pin T) ((pins pin).symm x)=N.value T x := by rw [value,Equiv.apply_symm_apply]

end
end Hierarchy.DescentWireRelabel

end OAI
