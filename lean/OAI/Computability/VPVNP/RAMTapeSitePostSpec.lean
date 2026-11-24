import OAI.Computability.VPVNP.RAMTapeSitePostBank
import OAI.Computability.VPVNP.RAMValidatorPost

/-!
# Correctness of the physical sort and boundary decisions

For the actual shared sorting fields the checked block determines the
terminal predecessor test. On a passing sorting transcript the physical
last-slot test therefore compares exactly the replayed block with the
edge records. A failed comparator contributes zero regardless of that block.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SitePost

open BurstRAM RAMLayout RAMSort RAMBoundary Boundary

variable {d e w : ℕ}

theorem boundary_decision (hw : 2 ≤ w) {B S : ℕ} (hB : 0 < B)
    (messages : RAMBoundary.Sends S (Word w)) (v : Fin S) (previous sent : RawSlot w)
    (block : Fin B → RawSlot w)
    (hp : (parsedSlot hw previous).record = RAMBoundary.receive messages v)
    (hs : v.val+1 < S → (parsedSlot hw sent).record = RAMBoundary.outgoing messages v)
    (hzero : v.val = 0 → (recordBytes previous).all (!·) = true)
    (hlast : S ≤ v.val+1 → (recordBytes sent).all (!·) = true) :
    decision (decide (0<v.val)) (decide (v.val+1<S)) previous sent (List.ofFn block) = true ↔
      RAMBoundary.checkAt hB messages v (fun i => (parsedSlot hw (block i)).record) := by
  have iff := Boundary.path_count_checkAt_iff hw hB messages v previous sent block hp hs
  dsimp only at iff
  have cnt := Boundary.path_count (decide (0<v.val)) (decide (v.val+1<S)) previous sent (List.ofFn block)
  simp only [List.length_ofFn] at cnt
  rw [cnt, Bool.toNat_eq_one] at iff
  exact ⟨fun h => (iff.mp h).2.1, fun h => iff.mpr ⟨hzero,h,hlast⟩⟩

theorem decision_iff (hw : 2 ≤ w) (hc : 2^d*2^e<2^w) (b : SendArrays d (2^e) w) (v : Word d)
    (x y : SortReplay.State (2+e) w) (prev sent : RawSlot w) :
    let ss := phases ((2+e)+d) ((2+e)+d) le_rfl
    let m := (unpackMessages (parseMessages hw hc b)).memory
    (y.2.all id = true ↔ x.2.all id = true ∧ SortCanonical hw hc b v ∧ RAMSort.checks v ss
      (physicalFieldsEquiv.{0,0} (2+e) d _ m.sortSends) (SortReplay.decoded hw x.1)) →
    (y.2.all id = true → (fun i => (parsedSlot hw (y.1 i)).record) = outputAt m v (SortReplay.decoded hw x.1)) →
    (parsedSlot hw prev).record = RAMBoundary.receive m.lastRecords v →
    (v.val+1 < 2^d → (parsedSlot hw sent).record = RAMBoundary.outgoing m.lastRecords v) →
    (v.val = 0 → (recordBytes prev).all (!·) = true) →
    (2^d ≤ v.val+1 → (recordBytes sent).all (!·) = true) →
    ((decision (decide (0<v.val)) (decide (v.val+1<2^d)) prev sent (List.ofFn y.1) && y.2.all id) = true ↔
      x.2.all id = true ∧ SortCanonical hw hc b v ∧ MemoryAt m v (SortReplay.decoded hw x.1)) := by
  intro ss m flagSort blockSort hp hs hz hl
  have hb := boundary_decision hw (Nat.two_pow_pos (2+e)) m.lastRecords v prev sent y.1 hp hs hz hl
  rw [Bool.and_eq_true, hb, MemoryAt]
  constructor
  · rintro ⟨hb, hf⟩
    obtain ⟨h₁,h₂,h₃⟩ := flagSort.mp hf
    rw [blockSort hf] at hb
    exact ⟨h₁,h₂,h₃,hb⟩
  · rintro ⟨h₁,h₂,h₃,hb⟩
    have hf := flagSort.mpr ⟨h₁,h₂,h₃⟩
    rw [blockSort hf]
    exact ⟨hb,hf⟩

end RAMTape.SitePost

end VPVNP
end Computability
end OAI
