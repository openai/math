import OAI.Computability.VPVNP.PairTraversalControllerInputs

/-!
# Locating the level of a popped traversal node

The DFS node is a row address. The descending scan accepts the first level
whose published start is at most this address. Its stride quotient recovers
the exact site ordinal, even when other levels contain no rows.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexLevelBounds

open BurstRAM BurstRAM.PrivateRAM TraversalRows TraversalRoles TraversalControllerInputs
open scoped Fin.CommRing

/-- The next prefix base is the exclusive end of this layer's rows. -/
theorem layerBase_succ (cap base : ℕ) (tags : List TaggedLayer) (j : Fin tags.length) :
    layerBase cap base tags (j.val + 1) =
      endPos cap (layerBase cap base tags j.val) tags[j].layer := by
  simp only [layerBase, words, List.take_succ_eq_append_getElem j.isLt,
    List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, Nat.add_zero, Nat.mul_add, endPos, address, Nat.add_assoc]
  rfl

theorem layerBase_mono (cap base : ℕ) (tags : List TaggedLayer) :
    Monotone (layerBase cap base tags) := by
  apply monotone_nat_of_le_succ
  intro i
  by_cases hi : i < tags.length
  · rw [layerBase_succ cap base tags ⟨i, hi⟩]
    exact Nat.le_add_right _ _
  · simp [layerBase, List.take_of_length_le (Nat.le_of_not_gt hi),
      List.take_of_length_le (show tags.length ≤ i + 1 by omega)]

/-- The chosen row belongs to its own interval. All earlier exclusive
ends are below or equal to its address and all later starts are strictly above it. -/
theorem node_interval (cap base : ℕ) (tags : List TaggedLayer) (j : Fin tags.length)
    (id : Fin tags[j].layer.count) :
    let start := layerBase cap base tags
    let node := address cap (start j.val) id.val
    start j.val ≤ node ∧ node < start (j.val + 1) ∧
      (∀ i < j.val, start (i + 1) ≤ node) ∧ (∀ i, j.val < i → node < start i) ∧
      (node - start j.val) / (cap + 2) = id.val := by
  intro start node
  have hlo : start j.val ≤ node := Nat.le_add_right _ _
  have hhi : node < start (j.val + 1) := by
    rw [show start (j.val + 1) = _ from layerBase_succ cap base tags j]
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left id.isLt (by omega)) _
  exact ⟨hlo, hhi, fun i hi => (layerBase_mono cap base tags hi).trans hlo,
    fun i hi => hhi.trans_le (layerBase_mono cap base tags hi),
    by simp [node, address, Nat.mul_div_cancel_left _ (by omega : 0 < cap + 2)]⟩

variable {w H first pitch offset cap base : ℕ} {pub : Fin 11 → Word w} {m : Memory w}
variable {old : TaggedLayer} {ls : List (Fiber w)}
variable (d : Resident pub m H first pitch offset cap base old ls)

include d in
/-- The descending scan begins at the actual last level and uses the published header geometry. -/
theorem resident_geometry :
    (terminalField pub m 1).val = ls.length + 1 ∧
    terminalField pub m 15 = ((cap + 2 : ℕ) : Word w) ∧
    terminalField pub m 16 = (first : Word w) ∧ terminalField pub m 17 = (pitch : Word w) := by
  simp only [terminal_read d _ (by decide : 1 < 32), terminal_read d _ (by decide : 15 < 32),
    terminal_read d _ (by decide : 16 < 32), terminal_read d _ (by decide : 17 < 32),
    d.levels, d.rowStride, d.firstHead, d.levelPitch, and_self]

include d in
/-- Every live level has a start cell, including the terminal state. -/
theorem resident_start (i : ℕ) (hi : i ≤ ls.length) :
    levelField pub m i 14 = (layerBase cap base (old :: ls.map Prod.fst) i : Word w) :=
  (level_read d i 14 hi (by decide)).trans (d.currentBase i hi)

include d in
/-- The resident count gives the exclusive end for every level. In particular,
the terminal level needs no successor header. -/
theorem resident_end (j : Fin (old :: ls.map Prod.fst).length) :
    levelField pub m j.val 14 + terminalField pub m 15 * siteCount pub m j.val =
      (layerBase cap base (old :: ls.map Prod.fst) (j.val + 1) : Word w) := by
  let tags := old :: ls.map Prod.fst
  have hj : j.val ≤ ls.length := by simpa using j.isLt
  have hs := ((resident_schedule d).lookup j).1
  have count : siteCount pub m j.val = (tags[j].layer.count : Word w) := by
    rw [← hs]
    exact Fin.ext (Nat.mod_eq_of_lt (siteCount pub m j.val).isLt).symm
  rw [resident_start d _ hj, (resident_geometry d).2.1, count, layerBase_succ]
  simp [endPos, address, tags]

include d in
/-- Actual header reads give the comparisons of the descending scan and the
machine's unsigned subtraction and division give the exact owner identifier. -/
theorem resident_locates (j : Fin (old :: ls.map Prod.fst).length)
    (id : Fin (old :: ls.map Prod.fst)[j].layer.count) (node : Word w)
    (hn : node.val = address cap (layerBase cap base (old :: ls.map Prod.fst) j.val) id.val)
    (fit : layerBase cap base (old :: ls.map Prod.fst) (ls.length + 1) < 2 ^ w) :
    j.val ≤ (terminalField pub m 1).val - 1 ∧ levelField pub m j.val 14 ≤ node ∧
    (∀ i, j.val < i → i ≤ (terminalField pub m 1).val - 1 → node < levelField pub m i 14) ∧
    BinaryOp.div.eval (node - levelField pub m j.val 14) (terminalField pub m 15) =
      (id.val : Word w) := by
  let tags := old :: ls.map Prod.fst
  let start := layerBase cap base tags
  have hj : j.val ≤ ls.length := by simpa using j.isLt
  have last : (terminalField pub m 1).val - 1 = ls.length := by rw [(resident_geometry d).1]; omega
  have starts (i : ℕ) (hi : i ≤ ls.length) : (levelField pub m i 14).val = start i := by
    rw [resident_start d i hi, Fin.val_natCast]
    exact Nat.mod_eq_of_lt ((layerBase_mono cap base tags (Nat.le_succ_of_le hi)).trans_lt fit)
  obtain ⟨hlo, _, _, later, quotient⟩ := node_interval cap base tags j id
  have le : levelField pub m j.val 14 ≤ node := by
    change (levelField pub m j.val 14).val ≤ node.val
    rw [starts _ hj, hn]
    exact hlo
  have strideFit : cap + 2 < 2 ^ w := by
    have positive : 1 ≤ tags[j].layer.count :=
      Nat.succ_le_of_lt ((Nat.zero_le id.val).trans_lt id.isLt)
    have bound := Nat.mul_le_mul_left (cap + 2) positive
    have total := (layerBase_mono cap base tags (Nat.succ_le_succ hj)).trans_lt fit
    rw [layerBase_succ cap base tags j] at total
    simp only [Nat.mul_one] at bound
    unfold endPos address at total
    omega
  refine ⟨last ▸ hj, le, ?_, ?_⟩
  · intro i hi hl
    change node.val < (levelField pub m i 14).val
    rw [starts i (last ▸ hl), hn]
    exact later i hi
  · change Fin.ofNat _ ((node - levelField pub m j.val 14).val / (terminalField pub m 15).val) = _
    rw [Fin.sub_val_of_le le, starts j.val hj, hn, (resident_geometry d).2.1,
      Fin.val_natCast, Nat.mod_eq_of_lt strideFit, quotient]
    rfl

end PairSimulation.VertexLevelBounds

end VPVNP
end Computability
end OAI
