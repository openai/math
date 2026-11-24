import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

/-!
# Absolute cursors of the pair counter

The machine makes one call for each cell in each input pass. It then visits
each site in row-major order, clearing its marks, initializing its root and
processing one node per call. The final calls compare all histogram entries.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Cursor

/-- A site occupies one call per clear, one root call, and one call per node. -/
def span (m nodes : ℕ) := m + (1 + nodes)

/-- Start of the histogram comparisons. -/
def compareStart (assembly S m nodes : ℕ) := assembly + S * span m nodes

/-- Total number of calls. -/
def calls (assembly S m nodes T : ℕ) := assembly + (S * span m nodes + T)

/-- The three types of call within one site's parse block, indexed by mark position, root
initialization or node number. -/
abbrev LocalItem (m nodes : ℕ) := Fin m ⊕ (Fin 1 ⊕ Fin nodes)
/-- All calls in the pair schedule, partitioned into input assembly, per-site parser operations
and final label comparisons. -/
abbrev Item (assembly S m nodes T : ℕ) :=
  Fin assembly ⊕ ((Fin S × LocalItem m nodes) ⊕ Fin T)

/-- Number the calls within a site by listing its mark clears first, then its root
initialization and node visits. -/
def localIndex (m nodes : ℕ) : LocalItem m nodes ≃ Fin (span m nodes) :=
  ((Equiv.refl _).sumCongr finSumFinEquiv).trans finSumFinEquiv

/-- All independent slots of the binary branch tape, in chronological order. -/
def index (assembly S m nodes T : ℕ) : Item assembly S m nodes T ≃ Fin (calls assembly S m nodes T) :=
  let rows := ((Equiv.refl _).prodCongr (localIndex m nodes)).trans finProdFinEquiv
  let later := (rows.sumCongr (Equiv.refl _)).trans finSumFinEquiv
  ((Equiv.refl _).sumCongr later).trans finSumFinEquiv

variable {A S m nodes T : ℕ}

theorem index_input (j : Fin A) : (index A S m nodes T (.inl j)).val = j.val := rfl

theorem index_site (u : Fin S) (i : LocalItem m nodes) :
    (index A S m nodes T (.inr (.inl (u,i)))).val = A + (u.val * span m nodes + (localIndex m nodes i).val) := by
  change A + ((localIndex m nodes i).val + span m nodes * u.val) = _
  rw [Nat.mul_comm, Nat.add_comm (localIndex m nodes i).val]

theorem index_compare (j : Fin T) :
    (index A S m nodes T (.inr (.inr j))).val = compareStart A S m nodes + j.val := by
  change A + (S * span m nodes + j.val) = _
  rw [compareStart, Nat.add_assoc]

@[simp] theorem local_clear (j : Fin m) : (localIndex m nodes (.inl j)).val = j.val := rfl
@[simp] theorem local_init (u : Fin 1) : (localIndex m nodes (.inr (.inl u))).val = m := by
  have hu : u.val = 0 := by have := u.isLt; omega
  change m + u.val = m
  omega
@[simp] theorem local_node (j : Fin nodes) : (localIndex m nodes (.inr (.inr j))).val = m+1+j.val := by
  change m + (1+j.val) = _
  omega

/-- Word division and remainder in the site phase recover both the physical
row and its local phase. -/
theorem unpack_site (u : Fin S) (i : LocalItem m nodes) :
    let v := (index A S m nodes T (.inr (.inl (u,i)))).val
    A ≤ v ∧ v < compareStart A S m nodes ∧
      (v-A) / span m nodes = u.val ∧ (v-A) % span m nodes = (localIndex m nodes i).val := by
  rw [index_site]
  dsimp only
  have h := (localIndex m nodes i).isLt
  have hp : 0 < span m nodes := by unfold span; omega
  have hlt : u.val * span m nodes + (localIndex m nodes i).val < S * span m nodes := by
    calc
      _ < u.val * span m nodes + span m nodes := Nat.add_lt_add_left h _
      _ = (u.val+1)*span m nodes := (Nat.succ_mul ..).symm
      _ ≤ _ := Nat.mul_le_mul_right _ u.isLt
  simp [compareStart, hlt, Nat.mod_eq_of_lt h]
  rw [Nat.mul_comm u.val, Nat.mul_add_div hp, Nat.div_eq_of_lt h, Nat.add_zero]

/-- For the paper's `2R` sites, each has exactly `2n−1` nodes. -/
theorem calls_pair (R n T : ℕ) (hn : 0 < n) :
    calls (2*(2*R*n)) (2*R) n (2*n-1) T = 10*R*n+T := by
  have h : span n (2*n-1) = 3*n := by unfold span; omega
  rw [calls, h]
  ring

end PrimedCounter.Cursor

end VPVNP
end Computability
end OAI
