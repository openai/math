import OAI.LinearAlgebra.MatrixExponent.FunctionNetwork

/-!
# Testing a sorted list for duplicates

Each internal node checks the boundary between its two sublists. Even
copying the input at every level costs only a logarithmic factor.
-/

namespace OAI.LinearAlgebra.MatrixExponent

variable {a : Wire}

theorem wd_tree (w : ℕ) (a : Wire) : wd (tree w a) = 2 ^ w * wd a := by
  induction w with
  | zero => simp [tree]
  | succ w ih =>
    change wd (tree w a) + wd (tree w a) = _
    rw [ih, pow_succ]
    ring

private def edge (right : Bool) : (w : ℕ) → Val (tree w a) → Val a
  | 0, x => x
  | w + 1, x => edge right w (if right then x.2 else x.1)

private theorem edge_net (F : Type) [Field F] (right : Bool) (w : ℕ) :
    DNet F (tree w a) a (edge right w) (2 * wd (tree w a)) := by
  induction w with
  | zero => exact (DNet.id F a).mono (by change wd a ≤ 2 * wd a; omega)
  | succ w ih =>
    have h : DNet F (tree (w + 1) a) (tree w a)
        (fun x => if right then x.2 else x.1) (wd (tree (w + 1) a)) := by
      cases right
      · exact DNet.fst F _ _
      · exact DNet.snd F _ _
    apply (h.comp ih).mono
    change _ + 2 * wd (tree w a) ≤ 2 * (wd (tree w a) + wd (tree w a))
    simp only [wd]
    omega

variable [LinearOrder (Val a)]

private theorem edges (w : ℕ) (x : Val (tree w a))
    (hs : (flatten w x).Pairwise (· ≤ ·)) :
    edge false w x ∈ flatten w x ∧ edge true w x ∈ flatten w x ∧
      ∀ z ∈ flatten w x, edge false w x ≤ z ∧ z ≤ edge true w x := by
  induction w with
  | zero => simp [edge, flatten]
  | succ w ih =>
    obtain ⟨hl, hr, hcross⟩ := List.pairwise_append.mp hs
    obtain ⟨hmin, _, hb⟩ := ih x.1 hl
    obtain ⟨_, hmax, hc⟩ := ih x.2 hr
    refine ⟨List.mem_append_left _ hmin, List.mem_append_right _ hmax, ?_⟩
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact ⟨(hb z hz).1, hcross _ hz _ hmax⟩
    · exact ⟨hcross _ hmin _ hz, (hc z hz).2⟩

def adjacent : (w : ℕ) → Val (tree w a) → Bool
  | 0, _ => true
  | w + 1, x => (adjacent w x.1 && adjacent w x.2) &&
      decide (edge true w x.1 < edge false w x.2)

theorem adjacent_iff (w : ℕ) (x : Val (tree w a))
    (hs : (flatten w x).Pairwise (· ≤ ·)) :
    adjacent w x = true ↔ (flatten w x).Nodup := by
  induction w with
  | zero => simp [adjacent, flatten]
  | succ w ih =>
    obtain ⟨hl, hr, hcross⟩ := List.pairwise_append.mp hs
    obtain ⟨_, hmax, hb⟩ := edges w x.1 hl
    obtain ⟨hmin, _, hc⟩ := edges w x.2 hr
    rw [adjacent, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih _ hl, ih _ hr,
      flatten, List.nodup_append, and_assoc]
    apply and_congr_right'
    apply and_congr_right'
    constructor
    · intro h z hz y hy
      exact ne_of_lt (((hb z hz).2.trans_lt h).trans_le (hc y hy).1)
    · intro h
      exact lt_of_le_of_ne (hcross _ hmax _ hmin) (h _ hmax _ hmin)

theorem adjacent_net {F : Type} [Field F] {k : ℕ}
    (h : DNet F (.pair a a) .bit (fun x => decide (x.1 < x.2)) k) (w : ℕ) :
    DNet F (tree w a) .bit (adjacent w) (2 ^ w * (w + 1) * (8 * wd a + k + 4)) := by
  induction w with
  | zero =>
    apply ((DNet.discard F a).comp (DNet.table F .unit .bit (fun _ => true) (by decide))).mono
    simp
    omega
  | succ w ih =>
    let gate := DNet.table F (.pair .bit .bit) .bit (fun x => x.1 && x.2) (by decide)
    have children := (ih.par ih).comp gate
    have boundary := ((edge_net (a := a) F true w).par (edge_net F false w)).comp h
    apply ((children.pair boundary).comp gate).mono
    simp only [wd, wd_tree, pow_succ]
    have hp : 1 ≤ 2 ^ w := Nat.one_le_pow _ _ (by decide)
    nlinarith [Nat.mul_le_mul_right k hp]

end OAI.LinearAlgebra.MatrixExponent
