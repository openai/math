import OAI.ThreeFlat.BitNetwork
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.EquivFin

namespace OAI
/-! # Removing unaddressed hidden bits

At most three hidden bits per cell occur at an address. Each remaining hidden
bit doubles the number of equal summands in the contraction, a scalar which
one constant cell supplies over every commutative semiring.
-/

noncomputable section
open scoped Classical BigOperators
namespace ThreeFlat.BitNetwork

variable {p : ℕ} {F : Type*} (N : BitNetwork F p)

private def addressed (h : Fin N.internal) : Prop :=
  ∃ a : Fin N.cells × Fin 3, N.source a.1 a.2 = .hidden h

private abbrev Used := {h : Fin N.internal // addressed N h}
private abbrev Unused := {h : Fin N.internal // ¬addressed N h}

private theorem card_used_le : Fintype.card (Used N) ≤ 3*N.cells := by
  let address (h : Used N) := h.property.choose
  have injective : Function.Injective address := by
    intro i j hij
    have hi := i.property.choose_spec
    have hj := j.property.choose_spec
    change N.source (address i).1 (address i).2 = .hidden i.val at hi
    change N.source (address j).1 (address j).2 = .hidden j.val at hj
    rw [hij] at hi
    exact Subtype.ext (BitSource.hidden.inj (hi.symm.trans hj))
  simpa [Fintype.card_prod,Nat.mul_comm] using Fintype.card_le_of_injective address injective

private def renumber : (s : BitSource N.internal p) →
    (∀ a, s = .hidden a → addressed N a) → BitSource (Fintype.card (Used N)) p
  | .hidden a, hs => .hidden (Fintype.equivFin _ (⟨a,hs a rfl⟩ : Used N))
  | .pin a, _ => .pin a
  | .constant b, _ => .constant b

private def compactSource (i : Fin N.cells) (j : Fin 3) : BitSource (Fintype.card (Used N)) p :=
  renumber N (N.source i j) (fun _ h => ⟨(i,j),h⟩)

private def usedNetwork : BitNetwork F p where
  internal := Fintype.card (Used N)
  cells := N.cells
  source := compactSource N
  table := N.table

private def splitAssignments : (Fin N.internal → Bool) ≃
    (Fin (Fintype.card (Used N)) → Bool) × (Unused N → Bool) :=
  (Equiv.piEquivPiSubtypeProd (addressed N) fun _ => Bool).trans
    (Equiv.prodCongr (Equiv.arrowCongr (Fintype.equivFin (Used N)) (Equiv.refl Bool)) (Equiv.refl _))

private theorem read_compact (x : Fin p → Bool) (h : Fin N.internal → Bool)
    (i : Fin N.cells) (j : Fin 3) :
    (compactSource N i j).read ((splitAssignments N h).1) x = (N.source i j).read h x := by
  have general (s : BitSource N.internal p) (hs : ∀ a, s = .hidden a → addressed N a) :
      (renumber N s hs).read ((splitAssignments N h).1) x = s.read h x := by
    cases s <;> simp [renumber,BitSource.read,splitAssignments,Equiv.arrowCongr]
  exact general (N.source i j) (fun _ he => ⟨(i,j),he⟩)

private theorem weight_used [CommSemiring F] (x : Fin p → Bool) (h : Fin N.internal → Bool) :
    (usedNetwork N).weight x (splitAssignments N h).1 = N.weight x h := by
  apply Finset.prod_congr rfl
  intro i _
  change N.table i _ = N.table i _
  apply congrArg (N.table i)
  exact funext (read_compact N x h i)

/-- Remove every unaddressed hidden variable and include its scalar contribution. -/
def compactHidden [CommSemiring F] : BitNetwork F p where
  internal := Fintype.card (Used N)
  cells := N.cells+1
  source := Fin.lastCases (fun _ => .constant false) (compactSource N)
  table := Fin.lastCases (fun _ => (Fintype.card (Unused N → Bool) : F)) N.table

private theorem weight_compactHidden [CommSemiring F] (x : Fin p → Bool)
    (h : Fin (Fintype.card (Used N)) → Bool) :
    N.compactHidden.weight x h = (usedNetwork N).weight x h * Fintype.card (Unused N → Bool) := by
  unfold weight factor compactHidden usedNetwork
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last]

/-- The normalization preserves every external tensor coefficient. -/
theorem compactHidden_eval [CommSemiring F] (x : Fin p → Bool) : N.compactHidden.eval x = N.eval x := by
  let c := usedNetwork N
  let e := splitAssignments N
  symm
  calc
    N.eval x = ∑ h, c.weight x (e h).1 :=
      Finset.sum_congr rfl (fun h _ => (weight_used N x h).symm)
    _ = ∑ q : (Fin (Fintype.card (Used N)) → Bool) × (Unused N → Bool), c.weight x q.1 :=
      e.sum_comp (fun q => c.weight x q.1)
    _ = ∑ h, (c.weight x h * Fintype.card (Unused N → Bool)) := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm]; rfl
    _ = N.compactHidden.eval x :=
      Finset.sum_congr rfl (fun h _ => (weight_compactHidden N x h).symm)

@[simp] theorem compactHidden_cells [CommSemiring F] : N.compactHidden.cells = N.cells+1 := rfl

theorem compactHidden_internal [CommSemiring F] : N.compactHidden.internal ≤ 3*N.cells :=
  card_used_le N

theorem compactHidden_size [CommSemiring F] :
    N.compactHidden.cells + N.compactHidden.internal ≤ 4*N.cells+1 := by
  rw [compactHidden_cells]
  have := compactHidden_internal N
  omega

end ThreeFlat.BitNetwork

end
end OAI
