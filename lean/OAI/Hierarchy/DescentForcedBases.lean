import OAI.Hierarchy.DescentColonyCover

namespace OAI
/-! # The number of base splits a single initial overload can force -/

namespace Hierarchy.DescentColonies
open scoped Classical BigOperators
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {k D : ℕ} {adj : V → V → Prop}

omit [Fintype V] [DecidableEq V] in
/-- Neighboring base depths differ by at most D/2. In particular an actual
path of m neighbor propagations changes the depth by at most mD/2. -/
theorem Reach.base_shift (b : V → ℕ)
    (smooth : ∀ v z,adj v z → 2*b v≤2*b z+D) {w v : V} {m : ℕ}
    (route : Reach adj w m v) : 2*b w≤2*b v+m*D := by
  induction route with
  | nil => simp
  | snoc route e ih =>
    have step := smooth _ _ e
    rw [Nat.add_mul]
    omega

private theorem hops_budget {m D initial base terminal : ℕ}
    (shift : 2*base≤2*terminal+m*D) (reach : terminal+m*D ≤ initial) :
    base ≤ initial ∧ m*D≤2*(initial-base) := by omega

/-- The forced bases at a fixed vertex share a single identifier for this
starting interval. The set therefore contains at most one base per reachable
vertex. -/
def fromMark (b : V → ℕ) (w : V) (j address : ℕ) : Finset (V × ℕ) :=
  (ball adj w (2*(j-b w)/D)).image fun v => (v,ancestorId k (b v) j address)

theorem fromMark_card {Δ g : ℕ} (degree : ∀v,(next adj v).card≤Δ) (branch : 2≤Δ)
    (logBound : Δ≤2^g) (spacing : 32*g≤D) (_positive : 0<D)
    (b : V → ℕ) (w : V) (j address : ℕ) :
    (fromMark (k:=k) (adj:=adj) (D:=D) b w j address).card ≤4*2^((j-b w+7)/8) := by
  let s := j-b w
  let m := 2*s/D
  have used : m*D≤2*s := Nat.div_mul_le_self _ _
  have work := Nat.mul_le_mul_left m spacing
  have exp : g*m≤(s+7)/8 := by
    have : 32*(g*m)≤2*s := by nlinarith only [used,work]
    omega
  have outer : Δ^m ≤ 2^((s+7)/8) := calc
    _ ≤ (2^g)^m := Nat.pow_le_pow_left logBound _
    _ = 2^(g*m) := (pow_mul ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) exp
  apply Finset.card_image_le.trans
  apply (ball_card degree branch w m).trans
  change 2*Δ^m ≤ 4*2^((s+7)/8)
  omega

/-- Every split of the actual base at v is charged to an overloaded starting
interval j at w lying at or below its own base and to the propagated base ID
in its bounded reach set. -/
theorem forced_source (positive : 0<D) (b : V → ℕ)
    (smooth : ∀v z,adj v z → 2*b v≤2*b z+D)
    {load : V → Block k → ℕ} {cap : ℕ} {v : V} {x : Block k}
    (split : Split load adj D cap v (b v) x) :
    ∃ w j y, cap<mass load w j y ∧ b w≤j ∧
      (v,group (b v) x)∈fromMark (k:=k) (adj:=adj) (D:=D) b w j (group j y) := by
  obtain ⟨w,j,y,hops,heavy,route,paid,align⟩ := split.origin
  have shift := route.base_shift b smooth
  have quota := hops_budget shift paid
  refine ⟨w,j,y,heavy,quota.1,Finset.mem_image.mpr ⟨v,?_,?_⟩⟩
  · exact frontier_subset_ball ((Nat.le_div_iff_mul_le positive).2 quota.2) route.mem_frontier
  · exact Prod.ext rfl ((ancestorId_group (by omega : b v≤j) y).trans align)

end
end Hierarchy.DescentColonies

end OAI
