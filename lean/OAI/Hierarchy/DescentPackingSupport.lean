import OAI.Hierarchy.DescentMatchedColorMass

namespace OAI
/-! # Whole-item packing loses capacity only at occupied thick destinations -/

namespace Hierarchy.DescentPacking
open scoped BigOperators Classical
noncomputable section
variable {I U V : Type*} [Fintype V] [DecidableEq V]

open private matched_of_complete from OAI.Hierarchy.DescentWholeItems
open private sum_packs sum_caps from OAI.Hierarchy.DescentMatchedSlabs

def positiveBins (cap : V → ℕ) : Finset V := Finset.univ.filter fun v => 0 < cap v

/-- Empty bins never contain any remaining capacity. Only positive initial capacities contribute loss. -/
theorem packing_loss_support (weight : I → ℕ) (input : List I) (cap : V → ℕ) (B : ℕ)
    (small : ∀ i ∈ input, weight i ≤ B) :
    let p := pack weight input cap
    min (input.map weight).sum (∑ v, cap v) ≤
      (∑ v, assigned weight v p.decisions) + B*(positiveBins cap).card := by
  let p := pack weight input cap
  change _ ≤ (∑ v, assigned weight v p.decisions) + _
  by_cases all : ∀ i, (i,none) ∉ p.decisions
  · have h := matched_of_complete weight p.decisions all
    have total : (p.decisions.map (fun x => weight x.1)).sum = (input.map weight).sum := by
      simpa only [List.map_map, Function.comp_def] using congrArg (fun xs : List I => (xs.map weight).sum) p.order
    rw [h, total]
    omega
  · push Not at all
    obtain ⟨i,hi⟩ := all
    have original : i ∈ input := p.order ▸ List.mem_map_of_mem (f:=Prod.fst) hi
    have smallRest (v : V) : p.remaining v ≤ B := ((p.missed i hi v).trans_le (small i original)).le
    have residual : (∑ v, p.remaining v) ≤ B*(positiveBins cap).card := by
      calc
        _ = ∑ v ∈ positiveBins cap, p.remaining v := by
          refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
          intro v _ outside
          have zero : cap v = 0 := by simpa [positiveBins] using outside
          have used := p.account v
          omega
        _ ≤ ∑ _v ∈ positiveBins cap, B := Finset.sum_le_sum fun v _ => smallRest v
        _ = _ := by simp [Nat.mul_comm]
    have balance : (∑ v, assigned weight v p.decisions) + (∑ v, p.remaining v) = ∑ v, cap v := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => p.account v
    omega

/-- The matched elements are the very same pairs of old thin and thick bundle indices. -/
theorem matched_count_support (traffic : U → V → ℕ) (B : ℕ) (thin thick : List U)
    (bounded : ∀ u ∈ thin, live traffic u ≤ B) :
    min (amount (live traffic) thin) (amount (live traffic) thick) ≤
      Fintype.card (Matched traffic B thin thick) + (2*B)*(positiveBins (fun v => Fintype.card (ThickPool traffic thick v))).card := by
  have h := packing_loss_support (amount (live traffic)) (thinPacks (live traffic) B thin)
    (fun v => Fintype.card (ThickPool traffic thick v)) (2*B) (thinPacks_small (live traffic) thin bounded)
  rw [sum_packs, thinPacks_flatten, sum_caps] at h
  have count := pairs_card (amount (live traffic)) (slabPacking traffic B thin thick).decisions
  exact h.trans_eq (congrArg (fun n => n + (2*B)*(positiveBins (fun v => Fintype.card (ThickPool traffic thick v))).card) count.symm)

omit [Fintype V] [DecidableEq V] in
/-- A positive thick-bin capacity has an original stream occurrence with positive traffic to that bin. -/
theorem thick_in_allow {k : ℕ} (traffic : U → V → ℕ) (stream : List U)
    (address : U → DescentWalshTables.Bits k) (a : DescentWalshTables.Bits k) (b : ZMod 2)
    (allow : Finset V) (covers : ∀ u ∈ stream, ∀ v, 0 < traffic u v → v ∈ allow) (v : V)
    (positive : 0 < Fintype.card (ThickPool traffic (side address a b true stream) v)) : v ∈ allow := by
  obtain ⟨⟨j,digit⟩⟩ := Fintype.card_pos_iff.mp positive
  exact covers _ (List.mem_of_mem_filter (List.get_mem _ j)) v ((Nat.zero_le digit.val).trans_lt digit.isLt)

end
end Hierarchy.DescentPacking

namespace Hierarchy.DescentMatchedCost
open DescentWalshTables DescentPacking Finset
open scoped BigOperators Classical

/-- For the chosen affine coloring, only its actual positive thick destinations contribute waste. -/
theorem paired_support_of_bound {k : ℕ} {C U V : Type*} [Fintype C] [Fintype V] [DecidableEq V]
    (traffic : C → U → V → ℕ) (stream : C → List U) (address : C → U → Bits k) (B : ℕ)
    (cap : ∀ c u, u ∈ stream c → live (traffic c) u ≤ B) (allow : C → Finset V) (K : ℕ)
    (a : Bits k) (b : ZMod 2)
    (cover : ∀ c v, 0 < Fintype.card (ThickPool (traffic c) (side (address c) a b true (stream c)) v) → v ∈ allow c)
    (count : ∀ c, (allow c).card ≤ K)
    (balanced : let A := fun c => DescentPacking.slab (live (traffic c)) (address c) (stream c);
      ∑ c, |∑ i, sign (binaryRow a i+b)*(A c i:ℝ)| ≤
        Real.sqrt ((B:ℝ)*Fintype.card C*∑ c,∑ i,(A c i:ℝ))) :
      let X : ℝ := ∑ c, (amount (live (traffic c)) (stream c):ℝ)
      let pairs : C → ℕ := fun c => Fintype.card (Matched (traffic c) B
        (side (address c) a b false (stream c)) (side (address c) a b true (stream c)))
      X/2 - Real.sqrt ((B:ℝ)*Fintype.card C*X)/2 - 2*B*K*Fintype.card C ≤ ∑ c,(pairs c:ℝ) := by
  let A := fun c => DescentPacking.slab (live (traffic c)) (address c) (stream c)
  have h := colored_overlap_of_bound A B a b balanced
  let subset := fun c flag => side (address c) a b flag (stream c)
  let mass := fun c flag => amount (live (traffic c)) (subset c flag)
  let pairs := fun c => Fintype.card (Matched (traffic c) B (subset c false) (subset c true))
  have positive (c : C) : mass c true = DescentMatchedCost.slab (fun i => decide (binaryRow a i+b=0)) (A c) := by
    simp [mass, subset, color_slab, DescentMatchedCost.slab, A]
  have negative (c : C) : mass c false = DescentMatchedCost.slab (fun i => !(decide (binaryRow a i+b=0))) (A c) := by
    simp [mass, subset, color_slab, DescentMatchedCost.slab, A]
  have tot (c : C) : (∑ i, (A c i:ℝ)) = (amount (live (traffic c)) (stream c):ℝ) := by
    exact_mod_cast slab_total (live (traffic c)) (address c) (stream c)
  have per (c : C) : min (mass c true) (mass c false) ≤ pairs c + 2*B*K := by
    rw [min_comm]
    have bound := matched_count_support (traffic c) B (subset c false) (subset c true)
      (fun u hu => cap c u (List.mem_of_mem_filter hu))
    have incl : positiveBins (fun v => Fintype.card (ThickPool (traffic c) (subset c true) v)) ⊆ allow c := by
      intro v hv
      exact cover c v (Finset.mem_filter.mp hv).2
    exact bound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left (2*B) ((Finset.card_le_card incl).trans (count c))) _)
  have sumNat := sum_le_sum (s:=univ) (fun c _ => per c)
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] at sumNat
  have real : (∑ c, min (mass c true:ℝ) (mass c false:ℝ)) ≤ (∑ c, (pairs c:ℝ)) + Fintype.card C*(2*(B:ℝ)*K) := by
    exact_mod_cast sumNat
  dsimp only at h ⊢
  simp only [←positive, ←negative, tot] at h
  change _ ≤ ∑ c, (pairs c:ℝ)
  nlinarith only [h, real]

/-- A single affine color on all colonies, with waste bounded by the actual per-colony destinations. -/
theorem paired_support {k : ℕ} {C U V : Type*} [Fintype C] [Fintype V] [DecidableEq V]
    (traffic : C → U → V → ℕ) (stream : C → List U) (address : C → U → Bits k) (B : ℕ)
    (slabCap : ∀ c i, DescentPacking.slab (live (traffic c)) (address c) (stream c) i ≤ B)
    (cap : ∀ c u, u ∈ stream c → live (traffic c) u ≤ B) (allow : C → Finset V) (K : ℕ)
    (cover : ∀ c a b v, 0 < Fintype.card (ThickPool (traffic c) (side (address c) a b true (stream c)) v) → v ∈ allow c)
    (count : ∀ c, (allow c).card ≤ K) :
    ∃ (a : Bits k) (b : ZMod 2),
      let X : ℝ := ∑ c, (amount (live (traffic c)) (stream c):ℝ)
      let pairs : C → ℕ := fun c => Fintype.card (Matched (traffic c) B
        (side (address c) a b false (stream c)) (side (address c) a b true (stream c)))
      X/2 - Real.sqrt ((B:ℝ)*Fintype.card C*X)/2 - 2*B*K*Fintype.card C ≤ ∑ c,(pairs c:ℝ) := by
  let A := fun c => DescentPacking.slab (live (traffic c)) (address c) (stream c)
  obtain ⟨a,b,h⟩ := DescentPackingColors.exists_coloring (fun c i => (A c i:ℝ)) B
    (fun _ _ => Nat.cast_nonneg _) (fun c i => by exact_mod_cast slabCap c i)
  exact ⟨a,b,paired_support_of_bound traffic stream address B cap allow K a b
    (fun c v => cover c a b v) count h⟩

end Hierarchy.DescentMatchedCost

end OAI
