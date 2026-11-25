import OAI.Computability.NearSquareRoot.InterchangeTable

/-!
# Aligned finite tables on arrays with contiguous payloads

A row is a stream of records. Each record holds a stream of symbols, of
length at most `width i` on input `i`. Record boundaries and payload lengths
are common across the aligned rows. No descriptor giving the record lengths
has to be added to the input: the code reads the nested P192 tree delimiters.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication.Code IntegerMultiplication.Strip

private theorem stripe_bound {X : Type} (s : Series X) (v : X → Tree) {d c : ℕ}
    (hd : 1 ≤ d) (hv : ∀ x, (v x).count ≤ c * d) :
    (stripe s v).count ≤ (c+1)*(s.count*d+1) := by
  apply (stripe_size s v (c*d) hv).trans
  calc
    s.count*(c*d+1)+1 ≤ s.count*(c*d+d)+1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_left hd _)) _
    _ ≤ _ := by nlinarith

/-- The map is performed at every payload address across the separately
stored rows. The number of input records and the payload-width bound can
both vary at runtime. All zips, unzips and per-record table scans are
charged to the same stack-program budget. -/
theorem interchange_payload_table {A B I K L : Type} [Finite A] [Finite K] [Nonempty K]
    {P : I → Type} {D : (i : I) → P i → Type}
    (records : (i : I) → Series (P i)) (payload : (i : I) → (j : P i) → Series (D i j))
    (width : I → ℕ) (hwidth : ∀ i j, (payload i j).count ≤ width i)
    (srcRows : Series K) (dstRows : Series L) (v : (i : I) → K → (j : P i) → D i j → A)
    (src : A → Tree) (dst : B → Tree) (hs : Function.Injective src)
    (table : (K → A) → L → B) :
    Carries (fun i => (records i).count * ((width i : ℝ)+1)+1)
      (fun i => stripe srcRows fun k => stripe (records i) fun j =>
        stripe (payload i j) fun a => src (v i k j a))
      (fun i => stripe dstRows fun l => stripe (records i) fun j =>
        stripe (payload i j) fun a => dst (table (fun k => v i k j a) l)) := by
  let row (i : I) (k : K) (j : P i) := stripe (payload i j) (fun a => src (v i k j a))
  let result (i : I) (l : L) (j : P i) :=
    stripe (payload i j) (fun a => dst (table (fun k => v i k j a) l))
  let w (i : I) := (width i : ℝ)+1
  let volume (i : I) : ℝ := (records i).count * w i + 1
  let input (i : I) := stripe srcRows fun k => stripe (records i) (row i k)
  have hw (i : I) : 1 ≤ w i := by exact le_add_of_nonneg_left (by positivity)
  have hvol (i : I) : 1 ≤ volume i := by
    dsimp [volume,w]
    exact le_add_of_nonneg_left (by positivity)
  obtain ⟨U,hU⟩ := (Set.finite_range (fun a : A => (src a).count)).bddAbove
  have rowCells (i : I) (k : K) (j : P i) :
      (row i k j).count ≤ (U+1)*(width i + 1) := by
    have hh := stripe_bound (payload i j) (fun a => src (v i k j a)) (d := 1) (c := U)
      le_rfl (fun _ => by simpa using hU (Set.mem_range_self _))
    apply hh.trans
    simp only [Nat.mul_one]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (hwidth i j) 1)
  have hsmall : Volume volume input := by
    refine ⟨(U+3)*(srcRows.count+1), fun i => ?_⟩
    let n := (records i).count*(width i+1)+1
    have hx k : (stripe (records i) (row i k)).count ≤ (U+2)*n :=
      stripe_bound _ _ (by omega) (rowCells i k)
    have hh := stripe_bound srcRows (fun k => stripe (records i) (row i k)) (by dsimp [n]; omega) hx
    have H : (input i).count ≤ (U+3)*(srcRows.count+1)*n := by
      apply hh.trans
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left (U+3)
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add_left (show 1 ≤ n by dsimp [n]; omega) _
    dsimp [volume,w]
    exact_mod_cast H
  have base := Carries.idles hvol hsmall
  let k₀ := Classical.choice (inferInstance : Nonempty K)
  have baseRow := finite_cell srcRows (fun i k => stripe (records i) (row i k)) base k₀
  have eraseCell : Carries (fun ij : Sigma P => w ij.1)
      (fun ij => row ij.1 k₀ ij.2) (fun _ => Tree.atom false) := by
    refine fixture ?_ (fun ij : Sigma P => hw ij.1) (.atom false)
    exact ⟨U+1, fun ij => by dsimp [w]; exact_mod_cast rowCells ij.1 k₀ ij.2⟩
  have eraseRow := liftoff records (fun i => row i k₀) (fun _ _ => .atom false) w eraseCell
  have aligned := lay srcRows records row base (baseRow.chain eraseRow)
  have cell := interchange_aligned_table
    (I := Sigma P) (P := fun ij => D ij.1 ij.2) (fun ij => payload ij.1 ij.2)
    srcRows dstRows (fun ij k => v ij.1 k ij.2) src dst hs table
  have cell' := cell.larger (d := fun ij : Sigma P => w ij.1) (fun ij => by
    dsimp [w]; exact_mod_cast Nat.add_le_add_right (hwidth ij.1 ij.2) 1)
  have transformed := liftoff records (fun i j => stripe srcRows fun k => row i k j)
    (fun i j => stripe dstRows fun l => result i l j) w cell'
  exact unlay dstRows records result (aligned.chain transformed)

/-- For nonempty record streams the unit cost at the outer delimiter can
be absorbed, giving the usual `N * (width+1)` budget. -/
theorem interchange_payload_budget {I : Type} {n width : I → ℕ}
    {input output : I → Tree} (hn : ∀ i, 0 < n i)
    (h : Carries (fun i => (n i : ℝ) * ((width i : ℝ)+1)+1) input output) :
    Carries (fun i => (n i : ℝ) * ((width i : ℝ)+1)) input output := by
  have hw (i : I) : 1 ≤ (n i : ℝ)*((width i : ℝ)+1) := by
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hn i)
      (le_add_of_nonneg_left (by positivity))
  exact h.times hw 2 fun i => by dsimp; linarith [hw i]

end NearSquareRoot
end Computability
end OAI
