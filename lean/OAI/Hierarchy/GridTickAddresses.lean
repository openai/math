import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card

namespace OAI
/-! # The ticks on each rail line and at each of its cells -/

namespace Hierarchy.GridTicks

variable {k g q : ℕ}

abbrev Cell (k g : ℕ) := Fin k → Fin g
abbrev Tick (k g q : ℕ) := Fin (g^k*q)

/-- Index cells in base `g`, with `q` consecutive slots per cell. -/
def index : Cell k g × Fin q ≃ Tick k g q :=
  (Equiv.prodCongr finFunctionFinEquiv (Equiv.refl _)).trans finProdFinEquiv

def cellEntry (z : Cell k g) : Fin q ↪ Tick k g q where
  toFun t := index (z,t)
  inj' _ _ h := congrArg Prod.snd (index.injective h)

def lineEntry (j : Fin k) (z : Cell k g) : Fin g × Fin q ↪ Tick k g q where
  toFun p := index (Function.update z j p.1,p.2)
  inj' := by
    rintro ⟨a,s⟩ ⟨b,t⟩ h
    have h' := index.injective h
    have ab := congrFun (congrArg Prod.fst h') j
    have st := congrArg Prod.snd h'
    exact Prod.ext (by simpa using ab) st

def cellTicks (z : Cell k g) : Finset (Tick k g q) := Finset.univ.map (cellEntry z)

def lineTicks (j : Fin k) (z : Cell k g) : Finset (Tick k g q) := Finset.univ.map (lineEntry j z)

@[simp] theorem card_cellTicks (z : Cell k g) : (cellTicks (q:=q) z).card = q := by
  simp [cellTicks]

@[simp] theorem card_lineTicks (j : Fin k) (z : Cell k g) :
    (lineTicks (q:=q) j z).card = g*q := by
  simp [lineTicks]

theorem cell_subset_line (j : Fin k) (z : Cell k g) :
    cellTicks (q:=q) z ⊆ lineTicks j z := by
  intro t ht
  obtain ⟨s, _, rfl⟩ := Finset.mem_map.mp ht
  apply Finset.mem_map.mpr
  refine ⟨(z j,s),Finset.mem_univ _, ?_⟩
  change index (Function.update z j (z j),s) = index (z,s)
  rw [Function.update_eq_self]

/-- The transverse address of the line containing a tick is read directly from
the cell part of its address. -/
theorem mem_line_iff (j : Fin k) (z : Cell k g) (t : Tick k g q) :
    t ∈ lineTicks j z ↔ ∀ i, i ≠ j → (index.symm t).1 i = z i := by
  constructor
  · rintro ht i hij
    obtain ⟨⟨a,s⟩, _, rfl⟩ := Finset.mem_map.mp ht
    change (index.symm (index (Function.update z j a,s))).1 i = z i
    rw [index.symm_apply_apply]
    exact Function.update_of_ne hij _ _
  · intro h
    let u := index.symm t
    have patch : Function.update z j (u.1 j) = u.1 := by
      funext i
      by_cases hij : i = j
      · simp [hij]
      · exact (Function.update_of_ne hij _ _).trans (h i hij).symm
    apply Finset.mem_map.mpr
    refine ⟨(u.1 j,u.2),Finset.mem_univ _,?_⟩
    change index (Function.update z j (u.1 j),u.2) = t
    rw [patch]
    exact index.apply_symm_apply t

end Hierarchy.GridTicks

end OAI
