import OAI.Computability.VPVNP.RAMSortLayers

/-!
# Local replay of the distributed sorting layers

A site keeps its current records and reads the matching site's send field
only at a cross-site stride. The local check at every such layer compares
its outgoing field with its own pre-comparison block. For a fixed input all
send fields are uniquely determined by these checks, and the final records
at each site agree with the globally addressed bitonic network.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

/-- One comparator layer in an array with `2^b` positions. -/
@[ext] structure Stage (b : ℕ) where
  /-- Bitonic merge phase exponent, whose bit in the global wire index selects the comparison
  direction. -/
  phase : ℕ
  /-- Bit position toggled in the wire index to find its comparator partner in this layer. -/
  stride : ℕ
  stride_lt : stride < phase
  phase_le : phase ≤ b
  deriving DecidableEq

/-- The last `k` layers of phase `a`, in the order of execution. -/
def strides (b a : ℕ) (ha : a ≤ b) : (k : ℕ) → k ≤ a → List (Stage b)
  | 0, _ => []
  | k + 1, hk => ⟨a, k, hk, ha⟩ :: strides b a ha k (Nat.le_of_succ_le hk)

/-- All layers in phases one through `a` of a fixed-width array. -/
def phases (b : ℕ) : (a : ℕ) → a ≤ b → List (Stage b)
  | 0, _ => []
  | a + 1, ha => phases b a (Nat.le_of_succ_le ha) ++ strides b (a+1) ha (a+1) le_rfl

variable {α : Type*}

private def evaluate [LinearOrder α] {b : ℕ} (layers : List (Stage b)) (x : ℕ → α) : ℕ → α :=
  layers.foldl (fun state s ↦ comparatorLayer s.stride (phaseDirection s.phase) state) x

private theorem evaluate_strides [LinearOrder α] (b a : ℕ) (ha : a ≤ b) (k : ℕ) (hk : k ≤ a)
    (x : ℕ → α) :
    evaluate (strides b a ha k hk) x = runStrides k (phaseDirection a) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    change evaluate (strides b a ha k _) (comparatorLayer k (phaseDirection a) x) = _
    rw [ih, runStrides]

private theorem evaluate_phases [LinearOrder α] (b a : ℕ) (ha : a ≤ b) (x : ℕ → α) :
    evaluate (phases b a ha) x = runPhases a x := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [phases, evaluate, List.foldl_append]
    change evaluate (strides b (a+1) ha _ _) (evaluate (phases b a _) x) = _
    rw [ih, evaluate_strides, runPhases]

variable {h d : ℕ}

/-- Exactly one block is sent by each site on a cross-site layer. A local
layer has a unique empty field since its domain `h ≤ s.stride` is empty. -/
abbrev Sends (h d : ℕ) (s : Stage (h+d)) (α : Type*) :=
  h ≤ s.stride → Fin (2 ^ d) → Wires h α

/-- Chronologically arranged outgoing fields. Each receive is addressed to
the corresponding field of its partner site. -/
def Fields (h d : ℕ) (α : Type*) : List (Stage (h+d)) → Type _
  | [] => PUnit
  | s :: ss => Sends h d s α × Fields h d α ss

/-- Arithmetic address of the unique sender supplying this entire block. -/
def sourceSite (s : Stage (h+d)) (hc : h ≤ s.stride) (v : Fin (2 ^ d)) : Fin (2 ^ d) :=
  ⟨partner (s.stride - h) v, partner_lt v.isLt (by have := s.stride_lt; have := s.phase_le; omega)⟩

variable [LinearOrder α]

/-- Update one site's block. Internal strides read both records locally.
Cross-site strides read the partner's outgoing block at the same offset. -/
def localLayer (s : Stage (h+d)) (send : Sends h d s α) (v : Fin (2 ^ d))
    (current : Wires h α) (i : Fin (2 ^ h)) : α :=
  let g := v.val * 2 ^ h + i.val
  let other := if hc : h ≤ s.stride then send hc (sourceSite s hc v) i
    else current ⟨partner s.stride i, partner_lt i.isLt (Nat.lt_of_not_ge hc)⟩
  if g < partner s.stride g then lower (phaseDirection s.phase g) (current i) other
  else upper (phaseDirection s.phase g) other (current i)

/-- Sending the actual pre-comparison records produces the same local block
as the XOR comparator layer. -/
theorem localLayer_block (s : Stage (h+d)) (x : ℕ → α) (v : Fin (2 ^ d)) :
    localLayer s (fun _ u ↦ block h u.val x) v (block h v.val x) =
      block h v.val (comparatorLayer s.stride (phaseDirection s.phase) x) := by
  funext i
  by_cases hc : h ≤ s.stride
  · simp only [localLayer, hc, dite_true, block, comparatorLayer, sourceSite,
      partner_cross v.val i.isLt hc]
  · simp only [localLayer, hc, dite_false, block, comparatorLayer,
      partner_local v.val i.isLt (Nat.lt_of_not_ge hc)]

/-- All outgoing fields agree with this site's computed records. -/
def checks (v : Fin (2 ^ d)) :
    (ss : List (Stage (h+d))) → Fields h d α ss → Wires h α → Prop
  | [], _, _ => True
  | s :: ss, fields, current =>
    (∀ hc, fields.1 hc v = current) ∧ checks v ss fields.2 (localLayer s fields.1 v current)

/-- The site's final records, computed only from its local input and the
cross-site receive fields. -/
def replay (v : Fin (2 ^ d)) :
    (ss : List (Stage (h+d))) → Fields h d α ss → Wires h α → Wires h α
  | [], _, current => current
  | s :: ss, fields, current => replay v ss fields.2 (localLayer s fields.1 v current)

/-- The actual pre-comparison blocks sent throughout a sequence of layers. -/
def actual : (ss : List (Stage (h+d))) → (ℕ → α) → Fields h d α ss
  | [], _ => PUnit.unit
  | s :: ss, x => (fun _ v ↦ block h v.val x,
      actual ss (comparatorLayer s.stride (phaseDirection s.phase) x))

theorem checks_actual (ss : List (Stage (h+d))) (x : ℕ → α) (v : Fin (2 ^ d)) :
    checks v ss (actual ss x) (block h v.val x) := by
  induction ss generalizing x with
  | nil => trivial
  | cons s ss ih =>
    simp only [checks, actual, localLayer_block]
    exact ⟨fun _ ↦ trivial, ih _⟩

/-- The local send checks determine the entire exchange transcript uniquely. -/
theorem fields_eq_actual (ss : List (Stage (h+d))) (fields : Fields h d α ss) (x : ℕ → α)
    (hc : ∀ v, checks v ss fields (block h v.val x)) : fields = actual ss x := by
  induction ss generalizing x with
  | nil => cases fields; rfl
  | cons s ss ih =>
    rcases fields with ⟨f, fs⟩
    have hhead : f = fun _ v ↦ block h v.val x := funext fun h ↦ funext fun v ↦ (hc v).1 h
    subst f
    simp only [checks, localLayer_block] at hc
    exact Prod.ext rfl (ih fs _ (fun v ↦ (hc v).2))

private theorem replay_actual (ss : List (Stage (h+d))) (x : ℕ → α) (v : Fin (2 ^ d)) :
    replay v ss (actual ss x) (block h v.val x) = block h v.val (evaluate ss x) := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih =>
    simp only [replay, actual, localLayer_block]
    exact ih _

/-- A locally accepted exchange reconstructs the correct globally sorted
records at every site. -/
theorem replay_phases (fields : Fields h d α (phases (h+d) (h+d) le_rfl)) (x : ℕ → α)
    (hc : ∀ v, checks v _ fields (block h v.val x)) (v : Fin (2 ^ d)) :
    replay v _ fields (block h v.val x) = block h v.val (runPhases (h+d) x) := by
  rw [fields_eq_actual _ _ x hc, replay_actual, evaluate_phases]

/-- For fixed records there is exactly one assignment of cross-site send fields. -/
theorem existsUnique_fields (ss : List (Stage (h+d))) (x : ℕ → α) :
    ∃! fields : Fields h d α ss, ∀ v, checks v ss fields (block h v.val x) :=
  ⟨actual ss x, checks_actual ss x, fun fields hc ↦ fields_eq_actual ss fields x hc⟩

end RAMSort

end VPVNP
end Computability
end OAI
