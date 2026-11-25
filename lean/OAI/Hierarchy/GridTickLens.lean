import OAI.Hierarchy.GridPassageSelection
import OAI.Hierarchy.GridPairAllocation

namespace OAI
/-! # Passing scheduled untouched pairs to the actual external labels -/

namespace Hierarchy.GridTicks
open GridLens
open scoped Classical

variable {k n q : ℕ}

theorem tick_in_cell_iff (x : Cell k (n+1)) (t : Tick k (n+1) q) :
    t ∈ cellTicks x ↔ (index.symm t).1 = x := by
  constructor
  · intro ht
    obtain ⟨s,_,rfl⟩ := Finset.mem_map.mp ht
    change (index.symm (index (x,s))).1 = x
    simp
  · intro h
    apply Finset.mem_map.mpr
    refine ⟨(index.symm t).2, Finset.mem_univ _, ?_⟩
    change index (x,(index.symm t).2) = t
    rw [← h]
    exact index.apply_symm_apply t

theorem rail_through_tick (x : Cell k (n+1)) (j : Fin k) (t : Tick k (n+1) q)
    (ht : t ∈ lineTicks j x) : cellOnRail j (index.symm t).1 (x j) = x := by
  obtain ⟨⟨a,s⟩,_,rfl⟩ := Finset.mem_map.mp ht
  change cellOnRail j (index.symm (index (Function.update x j a,s))).1 (x j) = x
  rw [Equiv.symm_apply_apply]
  funext i
  by_cases h : i = j <;> simp [cellOnRail, h]

/-- Every scheduled pair outside this cell maps injectively to an untouched external rail.
The map may use any external label order, including the fixed order used for catalyst selection. -/
theorem available_rails_of_scheduled {E : Type*} [Fintype E] [LinearOrder E]
    (direction : E → Fin k) (row : E → Cell k (n+1)) (touch : E → Option (Fin (n+1)))
    (x : Cell k (n+1)) (j : Fin k) (count : Tick k (n+1) q → ℕ)
    (label : (Σ t, Fin (count t)) ↪ E) (heading : ∀ a, direction (label a) = j)
    (assigned : ∀ a, row (label a) = (index.symm a.1).1)
    (single : ∀ a, touch (label a) = some ((index.symm a.1).1 j)) :
    ((pairsOn count (lineTicks j x)) \ (pairsOn count (cellTicks x))).card ≤
      (untouchedRails direction row touch x j).card := by
  let available := (pairsOn count (lineTicks j x)) \ (pairsOn count (cellTicks x))
  have maps : available.map label ⊆ untouchedRails direction row touch x j := by
    intro e he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp he
    have onLine := (Finset.mem_sigma.mp (Finset.mem_sdiff.mp ha).1).1
    have line := rail_through_tick x j a.1 onLine
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, heading a, by simpa [assigned] using line, ?_⟩
    rw [single]
    intro eqv
    have h := Option.some.inj eqv
    have eq : (index.symm a.1).1 = x := by
      rw [← h] at line
      simpa using line
    apply (Finset.mem_sdiff.mp ha).2
    exact Finset.mem_sigma.mpr ⟨(tick_in_cell_iff x a.1).mpr eq, Finset.mem_univ _⟩
  simpa [available] using Finset.card_le_card maps

/-- Original external labels in a fixed direction owned by a fixed scheduled tick. -/
def pairFiber {E : Type*} [Fintype E] (direction : E → Fin k) (owner : E → Tick k (n+1) q)
    (j : Fin k) (t : Tick k (n+1) q) : Finset E :=
  Finset.univ.filter (fun e => direction e = j ∧ owner e = t)

section
variable {E : Type*} [Fintype E] [LinearOrder E] (direction : E → Fin k) (owner : E → Tick k (n+1) q)
    (j : Fin k) (count : Tick k (n+1) q → ℕ) (hcount : ∀ t, (pairFiber direction owner j t).card = count t)

/-- Restore an actual external label from its rank within the fiber of its owner. -/
def scheduledLabel (a : Σ t, Fin (count t)) : E :=
  (pairFiber direction owner j a.1).orderEmbOfFin (hcount a.1) a.2

theorem scheduledLabel_spec (a : Σ t, Fin (count t)) :
    direction (scheduledLabel direction owner j count hcount a) = j ∧
      owner (scheduledLabel direction owner j count hcount a) = a.1 :=
  (Finset.mem_filter.mp ((pairFiber direction owner j a.1).orderEmbOfFin_mem (hcount a.1) a.2)).2

def scheduledEmbedding : (Σ t, Fin (count t)) ↪ E where
  toFun := scheduledLabel direction owner j count hcount
  inj' := by
    rintro ⟨t,a⟩ ⟨u,b⟩ h
    have ha := (scheduledLabel_spec direction owner j count hcount ⟨t,a⟩).2
    have hb := (scheduledLabel_spec direction owner j count hcount ⟨u,b⟩).2
    have ht := ha.symm.trans ((congrArg owner h).trans hb)
    change t = u at ht
    subst u
    exact congrArg (Sigma.mk t) (((pairFiber direction owner j t).orderEmbOfFin (hcount t)).injective h)

include hcount in
/-- The per-direction load bound guarantees enough untouched rail labels for this precise owner map. -/
theorem available_rails_of_tick_counts (x : Cell k (n+1)) :
    ((pairsOn count (lineTicks j x)) \ (pairsOn count (cellTicks x))).card ≤
      (untouchedRails direction (fun e => (index.symm (owner e)).1)
        (fun e => some ((index.symm (owner e)).1 (direction e))) x j).card := by
  let lbl := scheduledEmbedding direction owner j count hcount
  have spec (a) : direction (lbl a) = j ∧ owner (lbl a) = a.1 :=
    scheduledLabel_spec direction owner j count hcount a
  exact available_rails_of_scheduled direction _ _ x j count lbl
    (fun a => (spec a).1) (fun a => by rw [(spec a).2])
    (fun a => by rw [(spec a).1, (spec a).2])
end

end Hierarchy.GridTicks

end OAI
