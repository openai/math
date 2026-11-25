import OAI.Computability.BorderVNP.ShortenCubeEnumeration
import OAI.Computability.BorderVNP.ShortenPreparedLabels
import OAI.Computability.BorderVNP.PackedDeckMeanSamples
import OAI.Computability.BorderVNP.PackedDeckEnergyArrays

/-!
# Exact deck transport for prepared geometric bin counts

A whole-pack motion sends its old tile to the tile obtained by left
multiplication by its deck translation. Reading a bank at the new tile
therefore uses the inverse translation on the old address. The same
identity identifies the rational circuit mean with the actual geometric
sample law, including the speed permutation and all the Hecke words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PreparedBins

open Cover Cover.Frame Hecke Crossing Epoch PackMotions Packing SeedIntervals PackedDeckMean PackedDeckEnergy
open scoped Classical BorderVNP.Epoch.Cube

variable {D d n copies q m : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
    {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)
    (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
    (kind : Active input active → B.types) (lift : Active input active → Cube D → gamma 1)

/-- Count covariance under the left posttranslation in the actual sample tag. -/
theorem translated_count (i : Fin copies) (c : MotionCandidate (lattice 1) elliptic (Cube D) n)
    (t g : Cube D → Deck d) (b : B.Bin) :
    count (input i).layout (B.tag input active kind lift i (c.1,c.2,t)) (g,b) =
    count (input i).layout (B.tag input active kind lift i (c.1,c.2,1)) (t⁻¹*g,b) := by
  simp only [count_eq_sum]
  apply Finset.sum_congr rfl
  intro edge _
  by_cases ha : active i edge = true
  · simp [tag,sampledBin,ha,sampleAddress,shiftedAddress,Prod.ext_iff,eq_inv_mul_iff_mul_eq]
  · simp [tag,sampledBin,ha]

variable (enum : Fin q ≃ Cube D) (index : Fin m ≃ MotionCandidate (lattice 1) elliptic (Cube D) n)

/-- The finite array's actual candidate counts, before the deck pullback. -/
noncomputable def deckCounts (i : Fin copies) (j : Fin m) (b : B.Bin) (g : Fin q → Deck d) : ℕ :=
  count (input i).layout (B.tag input active kind lift i ((index j).1,(index j).2,1)) (g ∘ enum.symm,b)

/-- Turn the array's pullback into the corresponding forward physical posttranslation. -/
def deckSample (s : Fin m × (Fin q → Deck d)) : PackSample (lattice 1) elliptic (Cube D) d n :=
  ((index s.1).1,(index s.1).2,(s.2 ∘ enum.symm)⁻¹)

/-- Counts from the selected samples add up exactly to the updated circuit bank. -/
theorem joint_deck_count (choice : Fin copies → Fin m) (deck : Fin copies → Fin q → Deck d)
    (g : Fin q → Deck d) (b : B.Bin) :
    count (parallelPacks input).layout (jointBin input (B.tag input active kind lift)
      (fun i => deckSample enum index (choice i,deck i))) (g ∘ enum.symm,b) =
      ∑ i, B.deckCounts input active kind lift enum index i (choice i) b (deck i*g) := by
  rw [joint_count]
  apply Finset.sum_congr rfl
  intro i _
  have eq := B.translated_count input active kind lift i (index (choice i))
    ((deck i ∘ enum.symm)⁻¹) (g ∘ enum.symm) b
  rw [inv_inv] at eq
  exact eq

private theorem mean_reindex {J T G H : Type*} [Fintype J] [Group G] [Group H] [Fintype G] [Fintype H]
    (e : G ≃ H) (prob : J → ℚ) (C : J → T → H → ℕ) (b : T) (x : H) :
    mean prob C b x = mean prob (fun j t g => C j t (e g)) b 1 := by
  rw [mean_eq,mean_eq]
  apply Finset.sum_congr rfl
  intro j _
  rw [e.sum_comp (fun z => (C j b z : ℚ)),Fintype.card_congr e]

private theorem indexed_mean {I T : Type} [Fintype I] [inst : DecidableEq I]
    (label : Fin m ≃ MotionCandidate (lattice 1) elliptic I n)
    (C : Fin m → T → (I → Deck d) → ℕ) (b : T) (x : I → Deck d) :
    (∑ s : PackSample (lattice 1) elliptic I d n, packWeight (lattice 1) elliptic s *
      (C (label.symm (s.1,s.2.1)) b (s.2.2⁻¹*x) : ℚ)) =
      mean (fun j => motionProbability (lattice 1) elliptic (label j)) C b x := by
  have he : inst = fun _ _ => Classical.propDecidable _ := Subsingleton.elim _ _
  subst inst
  exact indexed_pack_mean_eq (lattice 1) elliptic label C b x

/-- The actual geometric bin mean, after reindexing the coordinate and candidate
sets, is the average of the circuit's real motion means. -/
theorem deck_binMean (g : Fin q → Deck d) (b : B.Bin) :
    binMean input (B.tag (d := d) (n := n) input active kind lift) (sampleProb d n) (g ∘ enum.symm,b) =
      (∑ i, motionMean (motionWeight (fun _ => fun j => motionProbability (lattice 1) elliptic (index j)))
        (moved (B.deckCounts input active kind lift enum index)) i (g,b)) / copies := by
  let C (i : Fin copies) (j : Fin m) (b : B.Bin) (x : Cube D → Deck d) :=
    count (input i).layout (B.tag input active kind lift i ((index j).1,(index j).2,1)) (x,b)
  let prob (j : Fin m) := motionProbability (lattice 1) elliptic (index j)
  let key := enum.arrowCongr (Equiv.refl (Deck d))
  unfold binMean
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have total : (∑ s : PackSample (lattice 1) elliptic (Cube D) d n,
      packWeight (lattice 1) elliptic s *
        (count (input i).layout (B.tag input active kind lift i s) (g ∘ enum.symm,b) : ℚ)) =
      mean prob (C i) b (g ∘ enum.symm) := by
    refine Eq.trans ?_ (indexed_mean index (C i) b (g ∘ enum.symm))
    apply Finset.sum_congr rfl
    rintro ⟨π,v,t⟩ _
    congr 2
    have hj := index.apply_symm_apply (π,v)
    simpa only [C,hj] using B.translated_count input active kind lift i (π,v) t (g ∘ enum.symm) b
  have changeKey := mean_reindex key prob (C i) b (g ∘ enum.symm)
  rw [changeKey] at total
  have realTotal := congrArg ((↑) : ℚ → ℝ) total
  simp only [Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast] at realTotal
  exact realTotal.trans (mean_cast (fun _ => prob) (B.deckCounts input active kind lift enum index) i (g,b))

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
