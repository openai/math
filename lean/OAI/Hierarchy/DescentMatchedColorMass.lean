import OAI.Hierarchy.DescentMatchedCost
import OAI.Hierarchy.DescentMatchedSlabs
import OAI.Hierarchy.DescentOccurrenceColors

namespace OAI
/-! # Coloring the ordered old occurrence streams retains the required actual pairs -/

namespace Hierarchy.DescentMatchedCost
open DescentWalshTables Finset
open scoped BigOperators Classical

/-- A supplied affine color on the original ordered streams gives the actual retained pair count. -/
theorem paired_of_bound {k : ℕ} {C U V : Type*} [Fintype C] [Fintype V] [DecidableEq V]
    (traffic : C → U → V → ℕ) (stream : C → List U) (address : C → U → Bits k) (B : ℕ)
    (cap : ∀ c u, u∈stream c → DescentPacking.live (traffic c) u ≤ B)
    (a : Bits k) (b : ZMod 2)
    (bound : let A := fun c => DescentPacking.slab (DescentPacking.live (traffic c)) (address c) (stream c);
      ∑ c, |∑ i, sign (binaryRow a i+b)*(A c i:ℝ)| ≤
        Real.sqrt ((B:ℝ)*Fintype.card C*∑ c,∑ i,(A c i:ℝ))) :
      let X : ℝ := ∑ c, (DescentPacking.amount (DescentPacking.live (traffic c)) (stream c):ℝ)
      let paired : C → ℕ := fun c => Fintype.card (DescentPacking.Matched (traffic c) B
        (DescentPacking.side (address c) a b false (stream c)) (DescentPacking.side (address c) a b true (stream c)))
      X/2 - Real.sqrt ((B:ℝ)*Fintype.card C*X)/2 - 2*B*Fintype.card V*Fintype.card C ≤ ∑ c,(paired c:ℝ) := by
  let A := fun c => DescentPacking.slab (DescentPacking.live (traffic c)) (address c) (stream c)
  have h := colored_overlap_of_bound A B a b bound
  let side := fun c flag => DescentPacking.side (address c) a b flag (stream c)
  let mass := fun c flag => DescentPacking.amount (DescentPacking.live (traffic c)) (side c flag)
  let paired := fun c => Fintype.card (DescentPacking.Matched (traffic c) B (side c false) (side c true))
  have positive (c : C) : mass c true=slab (fun i => decide (binaryRow a i+b=0)) (A c) := by
    simp [mass,side,DescentPacking.color_slab,slab,A]
  have negative (c : C) : mass c false=slab (fun i => !(decide (binaryRow a i+b=0))) (A c) := by
    simp [mass,side,DescentPacking.color_slab,slab,A]
  have tot (c : C) : (∑ i,(A c i:ℝ))=(DescentPacking.amount (DescentPacking.live (traffic c)) (stream c):ℝ) := by
    exact_mod_cast DescentPacking.slab_total (DescentPacking.live (traffic c)) (address c) (stream c)
  have per (c : C) : min (mass c true) (mass c false) ≤ paired c +Fintype.card V*(2*B) := by
    rw [min_comm]
    exact DescentPacking.matched_count (traffic c) B (side c false) (side c true)
      (fun i hi => cap c i (List.mem_of_mem_filter hi))
  have sumNat := sum_le_sum (s:=univ) (fun c _ => per c)
  rw [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul] at sumNat
  have real : (∑ c, min (mass c true:ℝ) (mass c false:ℝ)) ≤ (∑c,(paired c:ℝ)) + Fintype.card C * (Fintype.card V *(2*(B:ℝ))) := by
    exact_mod_cast sumNat
  dsimp only at h ⊢
  simp only [←positive,←negative,tot] at h
  change _ ≤ ∑c,(paired c:ℝ)
  nlinarith only [h,real]

/-- A common affine sign on all actual ordered colonies, with the discarded term bounded by
one whole thin pack per destination per colony. The right side counts matched bundle pairs. -/
theorem paired {k : ℕ} {C U V : Type*} [Fintype C] [Fintype V] [DecidableEq V]
    (traffic : C → U → V → ℕ) (stream : C → List U) (address : C → U → Bits k) (B : ℕ)
    (slabCap : ∀ c i, DescentPacking.slab (DescentPacking.live (traffic c)) (address c) (stream c) i ≤ B)
    (cap : ∀ c u, u∈stream c → DescentPacking.live (traffic c) u ≤ B) :
    ∃ (a : Bits k) (b : ZMod 2),
      let X : ℝ := ∑ c, (DescentPacking.amount (DescentPacking.live (traffic c)) (stream c):ℝ)
      let paired : C → ℕ := fun c => Fintype.card (DescentPacking.Matched (traffic c) B
        (DescentPacking.side (address c) a b false (stream c)) (DescentPacking.side (address c) a b true (stream c)))
      X/2 - Real.sqrt ((B:ℝ)*Fintype.card C*X)/2 - 2*B*Fintype.card V*Fintype.card C ≤ ∑ c,(paired c:ℝ) := by
  let A := fun c => DescentPacking.slab (DescentPacking.live (traffic c)) (address c) (stream c)
  obtain ⟨a,b,h⟩ := DescentPackingColors.exists_coloring (fun c i => (A c i:ℝ)) B
    (fun _ _ => Nat.cast_nonneg _) (fun c i => by exact_mod_cast slabCap c i)
  exact ⟨a,b,paired_of_bound traffic stream address B cap a b h⟩

end Hierarchy.DescentMatchedCost

end OAI
