import OAI.Computability.VPVNP.PairTraversalRoleExecution
import OAI.Computability.VPVNP.PairNodeDispatch

/-!
# The native dispatch opcode reads the selected pass's role

The DFS uses a word-valued node address. The table uses the same absolute
address plus a fixed public offset. The full tag-region bound proves there
is no wraparound for any selected node.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRoles

open BurstRAM TraversalRows Compression LocalHistory CompressorRecords
open scoped Fin.CommRing

variable {w : ℕ}

/-- Case labels used in the native router. -/
def Role.dispatch : Role → NodeDispatch.Role
  | .cursor => .leaf
  | .shrink => .shrink
  | .refresh => .refresh

theorem Role.decode (r : Role) (fit : 2 < 2 ^ w) :
    NodeDispatch.role (r.code : Word w) = r.dispatch := by
  have h1 : (1 : Word w) ≠ 0 := by
    intro e
    have h := congrArg Fin.val e
    change 1 % (2 ^ w) = 0 at h
    rw [Nat.mod_eq_of_lt (by omega)] at h
    omega
  have h2 : (2 : Word w) ≠ 0 := by
    intro e
    have h := congrArg Fin.val e
    change 2 % (2 ^ w) = 0 at h
    rw [Nat.mod_eq_of_lt fit] at h
    omega
  have h21 : (2 : Word w) ≠ 1 := by
    intro e
    have h := congrArg Fin.val e
    change 2 % (2 ^ w) = 1 % (2 ^ w) at h
    rw [Nat.mod_eq_of_lt fit, Nat.mod_eq_of_lt (by omega)] at h
    omega
  cases r <;> simp [Role.code, Role.dispatch, NodeDispatch.role, h1, h2, h21]

private theorem layerAddress_lt (cap base : ℕ) (ls : List TaggedLayer) (i : Fin ls.length)
    (j : Fin ls[i].layer.count) : address cap (layerBase cap base ls i.val) j.val <
      base + tagWords cap ls := by
  induction ls generalizing base with
  | nil => exact Fin.elim0 i
  | cons L ls ih =>
    have bound : base + tagWords cap (L :: ls) = endPos cap base L.layer + tagWords cap ls := by
      simp [endPos, address, tagWords, words, Nat.mul_add, Nat.add_assoc]
    rw [bound]
    cases i using Fin.cases with
    | zero =>
      change address cap (layerBase cap base (L :: ls) 0) j.val < _
      rw [layerBase_zero]
      exact (Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left j.isLt (by omega)) _).trans_le
        (Nat.le_add_right _ _)
    | succ i =>
      simpa only [Fin.getElem_fin, Fin.val_succ, List.getElem_cons_succ, layerBase_cons] using
        ih (endPos cap base L.layer) i j

/-- At any selected layer and site, the machine's one external read dispatches
to precisely the handler corresponding to the retained pass origin. -/
theorem Reads.dispatch {m : Memory w} {offset cap base : ℕ} {ls : List TaggedLayer}
    (hr : Reads w m offset cap base ls) (codes : 2 < 2 ^ w)
    (fit : offset + base + tagWords cap ls ≤ 2 ^ w) (i : Fin ls.length)
    (j : Fin ls[i].layer.count) :
    let node := address cap (layerBase cap base ls i.val) j.val
    NodeDispatch.role (m (((offset : Word w) + (node : Word w)).val)) = ls[i].role.dispatch := by
  intro node
  have room : offset + node < 2 ^ w := by
    have h := Nat.add_lt_add_left (layerAddress_lt cap base ls i j) offset
    simpa only [Nat.add_assoc] using h.trans_le (Nat.add_assoc .. ▸ fit)
  rw [probe_word_add offset node m room, hr.at_layer i j]
  exact Role.decode _ codes

end PairSimulation.TraversalRoles

end VPVNP
end Computability
end OAI
