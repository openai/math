import OAI.LinearAlgebra.SpectralBooks.ChordGraph.BoundedPatchReplacementWiring
import OAI.LinearAlgebra.SpectralBooks.TableProduct
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Products of local tables in the bit-width coordinates of a chord graph

A label on an edge of width `u + v` is split arithmetically into its two
consecutive blocks. The same split is used at both ends of every edge.
The local matrix entry for two independently applied tiles is the product
of the prescribed entries for the two blocks.
-/

open scoped BigOperators Classical

namespace LinearAlgebra.SpectralBooks.ChordGraph

noncomputable section

variable {k : ℕ}

/-- Decode the two fields of one edge label by quotient and remainder. -/
def splitWireIndex (u v : Widths k) (e : Chord k) :
    Index (u + v) e ≃ Index u e × Index v e :=
  (finCongr (by simp only [Finsupp.add_apply, pow_add] :
      2 ^ ((u + v) e) = 2 ^ (u e) * 2 ^ (v e))).trans finProdFinEquiv.symm

/-- Split every incident edge field at a site by that edge's own width. -/
def splitPortState (u v : Widths k) (i : Fin k) :
    State (u + v) i ≃ State u i × State v i :=
  (Equiv.piCongrRight (fun p : (portGraph k).Port i => splitWireIndex u v p.1.1)).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)

private def splitStates (u v : Widths k) :
    (∀ i, State (u + v) i) ≃ ((∀ i, State u i) × (∀ i, State v i)) :=
  (Equiv.piCongrRight (splitPortState u v)).trans (Equiv.arrowProdEquivProdArrow _ _ _)

private abbrev checks (g : Widths k) (x : ∀ i, State g i) : Prop :=
  ∀ e : Chord k,
    x ((portGraph k).tail e) ⟨(e,false), rfl⟩ = x ((portGraph k).head e) ⟨(e,true), rfl⟩

private theorem raw_coeff_checks (K : Type*) [Field K] (g : Widths k)
    (x : ∀ i, State g i) :
    (raw K g).coeff x = if checks g x then 1 else 0 := by
  classical
  dsimp only [raw, PortGraph.wiring]
  unfold checks
  split <;> rfl

/-- The equality checks defining the raw tensor split exactly over two
consecutive blocks of bits on every edge. -/
theorem raw_add_coeff (K : Type*) [Field K] (u v : Widths k) (x : ∀ i, State (u + v) i) :
    (raw K (u + v)).coeff x =
      (raw K u).coeff (fun i => (splitPortState u v i (x i)).1) *
      (raw K v).coeff (fun i => (splitPortState u v i (x i)).2) := by
  classical
  let left (i) := (splitPortState u v i (x i)).1
  let right (i) := (splitPortState u v i (x i)).2
  have split : checks (u + v) x ↔ checks u left ∧ checks v right := by
    constructor
    · intro h
      constructor
      · intro e
        exact congrArg (fun a => (splitWireIndex u v e a).1) (h e)
      · intro e
        exact congrArg (fun a => (splitWireIndex u v e a).2) (h e)
    · rintro ⟨hl, hr⟩ e
      exact (splitWireIndex u v e).injective (Prod.ext (hl e) (hr e))
  simp only [raw_coeff_checks]
  change (if checks (u + v) x then (1 : K) else 0) =
    (if checks u left then 1 else 0) * (if checks v right then 1 else 0)
  split <;> split <;> split <;> simp only [one_mul, zero_mul, mul_zero] <;> tauto

/-- The specified matrix entry of the product tile. A read uses one entry
from each fixed table, at the corresponding blocks of the two port states. -/
def productTable {K : Type*} [Mul K] {u v s t : Widths k}
    (M : ∀ i, State u i → State s i → K) (N : ∀ i, State v i → State t i → K)
    (i : Fin k) (x : State (u + v) i) (a : State (s + t) i) : K :=
  M i (splitPortState u v i x).1 (splitPortState s t i a).1 *
    N i (splitPortState u v i x).2 (splitPortState s t i a).2

/-- Multiplying the two fixed table entries at each site gives the tensor
product of the two local images in the original raw chord coordinates. -/
theorem productTable_action {K : Type*} [Field K] {u v s t : Widths k}
    (M : ∀ i, State u i → State s i → K) (N : ∀ i, State v i → State t i → K)
    (x : ∀ i, State (u + v) i) :
    (∑ a : ∀ i, State s i, (raw K s).coeff a * ∏ i, M i (splitPortState u v i (x i)).1 (a i)) *
      (∑ a : ∀ i, State t i, (raw K t).coeff a * ∏ i, N i (splitPortState u v i (x i)).2 (a i)) =
      ∑ a : ∀ i, State (s + t) i, (raw K (s + t)).coeff a * ∏ i, productTable M N i (x i) (a i) := by
  classical
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  symm
  apply Fintype.sum_equiv (splitStates s t) _ _
  intro a
  rw [raw_add_coeff]
  simp only [productTable, Finset.prod_mul_distrib]
  change _ = ((raw K s).coeff _ * _) * ((raw K t).coeff _ * _)
  ac_rfl

/-- Extract the numbered block of a wire by mixed-radix decoding. The first
block occupies the least significant bits. -/
def blockWireIndex {n : ℕ} (g : Fin n → Widths k) (e : Chord k) :
    Index (∑ j, g j) e ≃ (∀ j, Index (g j) e) :=
  (finCongr (by simp only [Finsupp.finsetSum_apply, Finset.prod_pow_eq_pow_sum] :
      2 ^ ((∑ j, g j) e) = ∏ j, 2 ^ (g j e))).trans finPiFinEquiv.symm

/-- Each block is extracted by integer division by the sizes of all
preceding blocks followed by reduction modulo the size of this block. -/
theorem blockWireIndex_val {n : ℕ} (g : Fin n → Widths k) (e : Chord k)
    (a : Index (∑ j, g j) e) (j : Fin n) :
    (blockWireIndex g e a j).val =
      (a.val / ∏ l : Fin j, 2^(g (Fin.castLE j.is_lt.le l) e)) % 2^(g j e) := rfl

/-- A particular bit in the table address reads the original wire at the
prefix bit offset. This permits accessing a small block in a wire whose
entire label spans many machine words. -/
theorem blockWireIndex_testBit {n : ℕ} (g : Fin n → Widths k) (e : Chord k)
    (a : Index (∑ j, g j) e) (j : Fin n) (b : Fin (g j e)) :
    (blockWireIndex g e a j).val.testBit b =
      a.val.testBit (b.val + ∑ l : Fin j, g (Fin.castLE j.is_lt.le l) e) := by
  rw [blockWireIndex_val, Finset.prod_pow_eq_pow_sum, Nat.testBit_mod_two_pow]
  simp only [b.isLt, decide_true, Bool.true_and, Nat.testBit_div_two_pow]

/-- Extract all the blocks from the port state, in a common order at both
ends of each wire. -/
def blockPortState {n : ℕ} (g : Fin n → Widths k) (i : Fin k) :
    State (∑ j, g j) i ≃ (∀ j, State (g j) i) :=
  (Equiv.piCongrRight (fun p : (portGraph k).Port i => blockWireIndex g p.1.1)).trans
    (Equiv.piComm _)

/-- A combined wire assignment passes all equality checks exactly when
each of its bit blocks passes the checks of its own wiring. -/
theorem raw_sum_coeff (K : Type*) [Field K] {n : ℕ} (g : Fin n → Widths k)
    (x : ∀ i, State (∑ j, g j) i) : (raw K (∑ j, g j)).coeff x =
      ∏ j, (raw K (g j)).coeff (fun i => blockPortState g i (x i) j) := by
  classical
  have split : checks (∑ j, g j) x ↔ ∀ j, checks (g j) (fun i => blockPortState g i (x i) j) := by
    constructor
    · intro h j e
      exact congrArg (fun a => blockWireIndex g e a j) (h e)
    · intro h e
      exact (blockWireIndex g e).injective (funext fun j => h j e)
  simp only [raw_coeff_checks]
  change (if checks (∑ j, g j) x then (1 : K) else 0) =
    ∏ j, (if checks (g j) (fun i => blockPortState g i (x i) j) then 1 else 0)
  rw [Fintype.prod_boole]
  by_cases h : checks (∑ j, g j) x
  · exact (ite_eq_left h).trans (ite_eq_left (split.mp h)).symm
  · exact (ite_eq_right h).trans (ite_eq_right (mt split.mpr h)).symm

/-- One factor table lookup per tile. The arguments are bit fields read
from the two original port states. -/
def tiledTable {K : Type*} [CommMonoid K] {n : ℕ} {g s : Fin n → Widths k}
    (M : ∀ j i, State (g j) i → State (s j) i → K)
    (i : Fin k) (x : State (∑ j, g j) i) (a : State (∑ j, s j) i) : K :=
  ∏ j, M j i (blockPortState g i x j) (blockPortState s i a j)

/-- The explicit product table realizes the product of the individual
local images, including when the tile types differ between blocks. -/
theorem tiledTable_action {K : Type*} [Field K] {n : ℕ} {g s : Fin n → Widths k}
    (M : ∀ j i, State (g j) i → State (s j) i → K)
    (Y : ∀ j, (∀ i, State (g j) i) → K)
    (hM : ∀ j x, Y j x = ∑ a, (raw K (s j)).coeff a * ∏ i, M j i (x i) (a i))
    (x : ∀ i, State (∑ j, g j) i) :
    (∏ j, Y j (fun i => blockPortState g i (x i) j)) =
      ∑ a : ∀ i, State (∑ j, s j) i, (raw K (∑ j, s j)).coeff a *
        ∏ i, tiledTable M i (x i) (a i) := by
  classical
  simp_rw [hM]
  rw [Fintype.prod_sum]
  symm
  let splitCfg : (∀ i, State (∑ j, s j) i) ≃ (∀ j i, State (s j) i) :=
    (Equiv.piCongrRight (blockPortState s)).trans (Equiv.piComm _)
  apply Fintype.sum_equiv splitCfg _ _
  intro a
  rw [raw_sum_coeff, Finset.prod_mul_distrib]
  change (∏ j, (raw K (s j)).coeff _) * (∏ i, ∏ j, _) = (∏ j, (raw K (s j)).coeff _) * ∏ j, ∏ i, _
  congr 1
  exact Finset.prod_comm

/-- Multiply the ordinary tile identities while keeping every original
table. A selector word chooses one table per block, and its local entry
is the product given in `tiledTable`. -/
theorem raw_tiled_sum {K : Type*} [Field K] {n : ℕ} {J : Fin n → Type*}
    [∀ j, Fintype (J j)] (g : Fin n → Widths k) (U : ∀ j, J j → Widths k)
    (z : ∀ j, J j → (∀ i, State (g j) i) → K)
    (M : ∀ j (w : J j) i, State (g j) i → State (U j w) i → K)
    (hz : ∀ j, (raw K (g j)).coeff = ∑ w, z j w)
    (hM : ∀ j (w : J j) x, z j w x = ∑ a, (raw K (U j w)).coeff a * ∏ i, M j w i (x i) (a i))
    (x : ∀ i, State (∑ j, g j) i) :
    (raw K (∑ j, g j)).coeff x =
      ∑ w : ∀ j, J j, ∑ a : ∀ i, State (∑ j, U j (w j)) i, (raw K (∑ j, U j (w j))).coeff a *
        ∏ i, tiledTable (fun j => M j (w j)) i (x i) (a i) := by
  classical
  rw [raw_sum_coeff]
  simp_rw [hz, Finset.sum_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun w _ => tiledTable_action (fun j => M j (w j))
    (fun j => z j (w j)) (fun j => hM j (w j)) x

end
end LinearAlgebra.SpectralBooks.ChordGraph

end OAI
