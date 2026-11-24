import OAI.Computability.VPVNP.PrimedStackRAMState

/-!
# Memory updates at the boundaries of the primed parser

Before each site, the parser clears every location mark and installs a
singleton root stack. The histogram survives these operations. After the
last site, the comparison at a dense index reads the count of its unique
production label.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Admin

open BurstRAM PrimedStackRAM
open scoped Fin.CommRing Classical

variable {base R n m H w : ℕ} {mem : Memory w}
variable {x : Fin 2 → Fin R → Fin m → Bool} {st : VisitState n m H}

/-- Typed scratch stores preserve every word in the reserved prefix. -/
theorem store_below (mem : Memory w) (c : Locations R n m H) (v : Word w)
    (hf : base + size R n m (labelCount n m H) ≤ 2 ^ w) {a : ℕ} (ha : a < base) :
    store base mem c v a = mem a := by
  have hne : a ≠ address base c := by
    unfold address
    omega
  simp [store, writeMemory, Nat.mod_eq_of_lt (address_lt hf c), hne]

/-- One clear call erases exactly the selected location from the logical mark set. -/
theorem clear_holds (hr : Holds base x st mem) (j : Fin m)
    (hf : base + size R n m (labelCount n m H) ≤ 2 ^ w) :
    Holds base x {st with marked := st.marked.erase j}
      (store base mem (markCell j : Locations R n m H) 0) := by
  have hview (a : Locations R n m H) (hne : a ≠ markCell j) :
      view base (store base mem (markCell j : Locations R n m H) 0) a = view base mem a := by
    rw [view_store_apply _ _ _ _ _ hf, ite_eq_right (fun h => (hne h).elim)]
  refine ⟨⟨hr.pending.fits, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hview _ (by simp [depthCell, markCell])]
    exact hr.pending.depth
  · intro i
    rw [hview _ (by simp [degCell, markCell])]
    exact hr.pending.degrees i
  · intro i
    rw [hview _ (by simp [stateCell, markCell])]
    exact hr.pending.states i
  · intro g s i
    rw [hview _ (by simp [markCell])]
    exact hr.input g s i
  · intro i
    rw [view_store_apply _ _ _ _ _ hf, hr.marked]
    by_cases hi : i = j <;> simp [markCell, hi]
  · intro a
    rw [hview _ (by simp [countCell, markCell])]
    exact hr.counts a

/-- Install a frame in slot zero and overwrite the old stack depth with one. -/
def rootStore (base R m : ℕ) (mem : Memory w) (d : Fin n) (root : Fin H) : Memory w :=
  let slot : Fin n := ⟨0, (Nat.zero_le d.val).trans_lt d.isLt⟩
  store base (store base (store base mem (degCell slot : Locations R n m H) (d.val : Word w))
    (stateCell slot : Locations R n m H) (root.val : Word w)) (depthCell : Locations R n m H) 1

/-- The three root stores leave every input bit, mark and production count intact. -/
theorem root_data (mem : Memory w) (d : Fin n) (root : Fin H)
    (hf : base + size R n m (labelCount n m H) ≤ 2 ^ w) :
    DataEq base R n m H mem (rootStore base R m mem d root) := by
  intro c hc
  have hne (a : Locations R n m H) (ha : dataCell a = false) : c ≠ a := by
    rintro rfl
    simp [ha] at hc
  simp [rootStore, view_store_apply _ _ _ _ _ hf, hne depthCell rfl,
    hne (degCell _) rfl, hne (stateCell _) rfl]

/-- The root stores install a singleton stack regardless of the old depth or frame words. -/
theorem root_rep (mem : Memory w) (d : Fin n) (root : Fin H)
    (hf : base + size R n m (labelCount n m H) ≤ 2 ^ w) :
    Represents (R := R) (n := n) (m := m) (H := H) base
      (rootStore base R m mem d root) (frames w [(d,root)]) := by
  have hn : 1 ≤ n := (Nat.zero_le d.val).trans_lt d.isLt
  have hw : 1 < 2 ^ w := hn.trans_lt (capacity_fit base hf)
  change Represents (R := R) (n := n) (m := m) (H := H) base
    (rootStore base R m mem d root) [((d.val : Word w), (root.val : Word w))]
  refine ⟨hn, ?_, ?_, ?_⟩
  · simp [rootStore, view_store_apply _ _ _ _ _ hf, Nat.mod_eq_of_lt hw]
  all_goals
    rintro ⟨i, hi⟩
    obtain rfl : i = 0 := by simp at hi; omega
    simp [rootStore, view_store_apply _ _ _ _ _ hf, depthCell, degCell, stateCell, Fin.castLE]

/-- Root initialization installs a singleton pending stack for the new site. -/
theorem root_holds (hr : Holds base x st mem) (d : Fin n) (root : Fin H)
    (hf : base + size R n m (labelCount n m H) ≤ 2 ^ w) :
    Holds base x {st with pending := [(d,root)]} (rootStore base R m mem d root) :=
  hr.withStack _ (root_data mem d root hf) (root_rep mem d root hf)

/-- The final word comparison tests the exact logical production count. -/
theorem compare_iff (hr : Holds base x st mem) (j : Fin (labelCount n m H)) (v : Word w) :
    view base mem (countCell j : Locations R n m H) = v ↔
      st.counts ((labelIndex n m H).symm j) = v.val := by
  have hc := hr.counts ((labelIndex n m H).symm j)
  rw [Equiv.apply_symm_apply] at hc
  rw [Fin.ext_iff, hc]

end PrimedCounter.Admin

end VPVNP
end Computability
end OAI
