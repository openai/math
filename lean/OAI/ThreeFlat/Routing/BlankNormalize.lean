import OAI.ThreeFlat.Routing.SpillSlots
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Clearing the payloads of inactive spill slots -/

namespace ThreeFlat.Routing.BlankNormalize

open Spill
open scoped BigOperators Classical
noncomputable section

def result {S : Type*} {w : ℕ} (x : SlotBits S w → Bool) (p : SlotBits S w) : Bool :=
  x (p.1, none) && x p

@[simp] theorem result_flag {S : Type*} {w : ℕ} (x : SlotBits S w → Bool) (i : S) :
    result x (i, none) = x (i, none) := by simp [result]

theorem zeroBlanks {S : Type*} {w : ℕ} (x : SlotBits S w → Bool) :
    ZeroBlanks (result x) := by
  intro i hi j
  rw [result_flag] at hi
  simp [result, hi]

@[simp] theorem occupied_result {S : Type*} [Fintype S] {w : ℕ} (x : SlotBits S w → Bool) :
    occupied (result x) = occupied x := by
  simp [occupied]

@[simp] theorem payloads_result {S : Type*} [Fintype S] {w : ℕ} (x : SlotBits S w → Bool) :
    payloads (result x) = payloads x := by
  unfold payloads
  rw [occupied_result]
  apply Multiset.map_congr rfl
  intro i hi
  have active : x (i, none) = true := (Finset.mem_filter.mp hi).2
  funext j
  simp [result, active]

private def network (F S : Type*) [Zero F] [One F] [Fintype S] (w : ℕ) :
    BitNetwork F (Fintype.card (SlotBits S w ⊕ SlotBits S w)) where
  cells := Fintype.card (SlotBits S w)
  internal := 0
  source i :=
    let q := (Fintype.equivFin (SlotBits S w)).symm i
    ![.pin (Fintype.equivFin _ (.inl (q.1, none))), .pin (Fintype.equivFin _ (.inl q)),
      .pin (Fintype.equivFin _ (.inr q))]
  table _ b := if (b 0 && b 1) = b 2 then 1 else 0

/-- One cell per bit tests the proposed output against the activity-gated input. -/
def stage (F S : Type*) [CommSemiring F] [Fintype S] (w : ℕ) :
    Stage F (SlotBits S w) (SlotBits S w) where
  network := network F S w
  run x := some (result x)
  checked x y := by
    let pin := fun j => Sum.elim x y ((Fintype.equivFin _).symm j)
    have cell (h : Fin 0 → Bool) (p : SlotBits S w) :
        (network F S w).factor pin h (Fintype.equivFin _ p) =
          if result x p = y p then 1 else 0 := by
      simp [BitNetwork.factor,network,BitSource.read,pin,result]; split_ifs <;> simp_all
    change (∑ h : Fin 0 → Bool, ∏ t : Fin (Fintype.card (SlotBits S w)), (network F S w).factor pin h t) = _
    let test (i : Fin (Fintype.card (SlotBits S w))) : F :=
      let p := (Fintype.equivFin (SlotBits S w)).symm i
      if result x p = y p then 1 else 0
    have all (h : Fin 0 → Bool) (i : Fin (Fintype.card (SlotBits S w))) :
        (network F S w).factor pin h i = test i := by
      obtain ⟨p,rfl⟩ := (Fintype.equivFin (SlotBits S w)).surjective i
      simpa only [test, Equiv.symm_apply_apply] using cell h p
    simp_rw [all]
    rw [Fintype.sum_unique, ← (Fintype.equivFin (SlotBits S w)).prod_comp test]
    simp [test, Fintype.prod_boole, funext_iff]

@[simp] theorem stage_run (F S : Type*) [CommSemiring F] [Fintype S] (w : ℕ)
    (x : SlotBits S w → Bool) : (stage F S w).run x = some (result x) := rfl

@[simp] theorem stage_cells (F S : Type*) [CommSemiring F] [Fintype S] (w : ℕ) :
    (stage F S w).network.cells = Fintype.card S * (w+1) := by
  change Fintype.card (S × Option (Fin w)) = _
  simp

@[simp] theorem stage_internal (F S : Type*) [CommSemiring F] [Fintype S] (w : ℕ) :
    (stage F S w).network.internal = 0 := rfl

theorem stage_volume (F S : Type*) [CommSemiring F] [Fintype S] (w : ℕ) :
    (stage F S w).network.cells + (stage F S w).network.internal +
        Fintype.card (SlotBits S w ⊕ SlotBits S w) = 3 * (Fintype.card S * (w+1)) := by
  simp only [stage_cells, stage_internal, Nat.add_zero, SlotBits, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
  omega

end
end ThreeFlat.Routing.BlankNormalize

end OAI
