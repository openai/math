import OAI.Hierarchy.ProbeArchiveRowBound
import OAI.Hierarchy.ProbeStripOccupancy

namespace OAI
/-! # Per-row archive bounds from the actual native occurrence owners and field numbers -/

namespace Hierarchy.ProtocolRAM.PaidWidths
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Fin.CommRing Classical
noncomputable section
variable {w edges : ℕ}

/-- Original row index of a positively charged occurrence hitting one exact reporter ID. -/
def Slice.Positive (s : Slice) (m : Memory w) (e : Fin edges) :=
  { i : Fin s.count // (s.edge.eval m (i.val:Word w)).val=e.val ∧ 0<(s.amount.eval m (i.val:Word w)).val }

/-- Only positive, genuinely hit occurrences require a live ball owner. This
includes the empty purchased board and all uncommitted padded records. -/
theorem Slice.live_load {Ball X V : Type*} (s : Slice) (m : Memory w) (e : Fin edges)
    (place : Ball×X ↪ V) (source : Fin edges→V) (roles cap : ℕ)
    (owner : s.Positive m e→Ball) (field : s.Positive m e→Fin roles)
    (inside : ∀i,∃ x,place (owner i,x)=source e)
    (distinct : ∀i j,owner i=owner j → field i=field j → i=j)
    (bounded : ∀i : s.Positive m e,(s.amount.eval m (i.val.val:Word w)).val≤cap) : s.load m e≤roles*cap := by
  let hit (i : Fin s.count) := (s.edge.eval m (i.val:Word w)).val=e.val ∧ 0<(s.amount.eval m (i.val:Word w)).val
  let number : s.Positive m e ↪ Fin roles := ⟨field,by
    intro i j eqn
    obtain ⟨x,left⟩ := inside i
    obtain ⟨y,right⟩ := inside j
    exact distinct i j (congrArg Prod.fst (place.injective (left.trans right.symm))) eqn⟩
  let numbered : { i : Fin s.count // hit i } ↪ Fin roles := number
  have size : (Finset.univ.filter hit).card≤roles := by
    simpa only [Fintype.card_subtype,Fintype.card_fin] using Fintype.card_le_of_embedding numbered
  calc
    _ ≤ ∑ i : Fin s.count,if hit i then cap else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases atEdge : (s.edge.eval m (i.val:Word w)).val=e.val
      · by_cases pos : 0<(s.amount.eval m (i.val:Word w)).val
        · have positiveHit : hit i := ⟨atEdge,pos⟩
          simpa only [ite_eq_left atEdge,ite_eq_left positiveHit] using bounded ⟨i,atEdge,pos⟩
        · have empty : (s.amount.eval m (i.val:Word w)).val=0 := by omega
          simp [hit,atEdge,empty]
      · simp [hit,atEdge]
    _ = (Finset.univ.filter hit).card*cap := by rw [←Finset.sum_filter]; simp
    _ ≤ _ := Nat.mul_le_mul_right cap size

/-- A live direct, secondary radius, or tree occurrence has a named source site
inside its own selected strip. On a single physical edge its source ball is
therefore fixed. Different occurrences in that ball use different field numbers.
This bounds the true paid native scatter even when distinct physical edges have
identical global endpoint pairs. -/
theorem Slice.owned_load {Ball X V : Type*} (s : Slice) (m : Memory w) (e : Fin edges)
    (place : Ball×X ↪ V) (source : Fin edges→V) (roles cap : ℕ)
    (row : Fin s.count→Ball) (field : Fin s.count→Fin roles)
    (inside : ∀i,(s.edge.eval m (i.val:Word w)).val=e.val → 0<(s.amount.eval m (i.val:Word w)).val →
      ∃ x,place (row i,x)=source e)
    (distinct : ∀i j,(s.edge.eval m (i.val:Word w)).val=e.val → (s.edge.eval m (j.val:Word w)).val=e.val →
      0<(s.amount.eval m (i.val:Word w)).val → 0<(s.amount.eval m (j.val:Word w)).val →
      row i=row j → field i=field j → i=j)
    (bounded : ∀ i : Fin s.count,(s.amount.eval m (i.val:Word w)).val≤cap) : s.load m e≤roles*cap := by
  apply s.live_load m e place source roles cap (fun i=>row i.val) (fun i=>field i.val)
  · intro i
    exact inside i.val i.property.1 i.property.2
  · intro i j sameRow sameField
    exact Subtype.ext (distinct i.val j.val i.property.1 j.property.1 i.property.2 j.property.2 sameRow sameField)
  · exact fun i=>bounded i.val

end
end Hierarchy.ProtocolRAM.PaidWidths

end OAI
