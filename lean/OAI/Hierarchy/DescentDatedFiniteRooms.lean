import OAI.Hierarchy.DescentDatedAddressRate
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Filter.Finite

namespace OAI
/-! # Combining native address bounds across finitely many original degree values -/
namespace Hierarchy.DescentDatedAddressBook.Bounded
open Filter
variable {ι : ℕ→Type*} {x : ∀h,ι h→ℕ}

theorem restrict (r : Bounded x) (q : ∀h,ι h→Prop) :
    Bounded (fun h (i : {j:ι h //q h j})=>x h i.val) :=by
  obtain ⟨K,paid⟩:=r
  exact ⟨K,paid.mono fun h p i=>p i.val⟩

theorem of_restrict (q : ∀h,ι h→Prop) (eventual : ∀ᶠ h:ℕ in atTop,∀i,q h i)
    (bounded : Bounded (fun h (i:{j:ι h //q h j})=>x h i.val)) : Bounded x :=by
  obtain ⟨C,paid⟩:=bounded
  exact ⟨C,eventual.and paid |>.mono fun h ⟨ok,fits⟩ i=>fits ⟨i,ok i⟩⟩

theorem finite_parts {m : ℕ} (tag : ∀h,ι h→Fin m)
    (each : ∀d:Fin m,Bounded (fun h (i : {j:ι h //tag h j=d})=>x h i.val)) : Bounded x :=by
  classical
  choose cost paid using each
  have all_paid : ∀ᶠ h : ℕ in atTop, ∀ (d : Fin m) (i : {j : ι h // tag h j=d}),
      x h i.val ≤ 2^(cost d*h) := Filter.eventually_all.mpr paid
  refine ⟨Finset.univ.sup cost,?_⟩
  filter_upwards [all_paid] with h ok
  intro i
  have bound := ok (tag h i) ⟨i,rfl⟩
  have degree_le : cost (tag h i) ≤ Finset.univ.sup cost :=
    Finset.le_sup (f:=cost) (Finset.mem_univ (tag h i))
  exact bound.trans (Nat.pow_le_pow_right (by decide : 0<2) (Nat.mul_le_mul_right h degree_le))

end Hierarchy.DescentDatedAddressBook.Bounded

end OAI
