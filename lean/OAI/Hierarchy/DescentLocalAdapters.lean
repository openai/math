import OAI.Hierarchy.DescentLocalTables
import OAI.Computability.BorderVNP.BitVolume
import Mathlib.Data.Fintype.EquivFin

namespace OAI
/-! # Boundary reindexing and row formatting on literal networks -/

namespace Hierarchy.DescentLocalAdapters
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {D : ℕ} {P Q K : Type*} {bits : P→ℕ} (N : Network D P bits)
    (place : Q → P) (newBits : Q→ℕ)

def graph : Network D Q newBits where
  Site := N.Site
  Edge := N.Edge
  finiteSite := N.finiteSite
  finiteEdge := N.finiteEdge
  src := N.src
  dst := N.dst
  width := N.width
  attach := N.attach ∘ place
  position := N.position
  in_ball := N.in_ball

def Local (encode : Ports newBits → Ports bits) := ∀v (x y : Ports newBits),
  (∀q,N.attach (place q)=v → x q=y q) → ∀p,N.attach p=v → encode x p=encode y p

def tables (T : N.Tables K) (encode : Ports newBits → Ports bits) : (graph N place newBits).Tables K :=
  DescentLocalTables.tables _ (fun a pins v=>N.read T a (encode pins) v)

theorem read (T : N.Tables K) (encode : Ports newBits → Ports bits) (loc : Local N place newBits encode)
    (a : N.Assignment) (x : Ports newBits) (v : N.Site) :
    (graph N place newBits).read (tables N place newBits T encode) a x v=N.read T a (encode x) v := by
  refine DescentLocalTables.read (graph N place newBits)
    (fun assignment pins site => N.read T assignment (encode pins) site) ?_ a x v
  intro j a b p q wires pins
  apply congrArg₂ (T j)
  · exact funext (fun e => wires e.val e.property)
  · exact funext (fun t => loc j p q pins t.val t.property)

theorem value [CommSemiring K] (T : N.Tables K) (encode : Ports newBits → Ports bits)
    (loc : Local N place newBits encode) (x : Ports newBits) :
    (graph N place newBits).value (tables N place newBits T encode) x=N.value T (encode x) := by
  unfold Network.value
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro v _
  exact read N place newBits T encode loc a x v

theorem degree [Fintype P] [Fintype Q] (unique : Function.Injective place) (v : N.Site) :
    (graph N place newBits).bitDegree v≤N.bitDegree v := by
  let f : Q ⊕ N.Edge×Bool → P ⊕ N.Edge×Bool := Sum.map place id
  unfold Network.bitDegree
  refine Finset.card_le_card_of_injOn f ?_ (Sum.map_injective.mpr ⟨unique,Function.injective_id⟩).injOn
  intro q keep
  have atSite := (Finset.mem_filter.mp keep).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  rcases q with q | ⟨e,b⟩ <;> exact atSite

end
end Hierarchy.DescentLocalAdapters

end OAI
