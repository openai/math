import OAI.Computability.BorderVNP.ShortenPublicPopulationInput

/-! # Moved bin addresses at the original public cable names

The prefix allocator reads the moved address at its stable cable number.
All rows of one pack use the same candidate and translation inputs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicPopulation

open Cover Cover.Frame Cover.AddressCircuit Epoch Crossing Packing PackMotions Hecke
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {D q n : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) (enum : Fin q ≃ Cube D)
    {M U σ : Type*} [Fintype M] [DecidableEq M] [Fintype U] [Fintype σ]
    (perm : M → Equiv.Perm (Cube D)) (word : M → ProductSample (lattice 1) elliptic (Cube D) n)

/-- A batch of chosen-motion addresses, prior to sorting or interval matching.
The address returned on each active edge is its actual sampled bin. -/
theorem jointRows_frames :
    ∃ C p : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d) (w copies : ℕ) {U σ : Type*} [Fintype U] [Fintype σ]
      (a : JointPins (↥B.types) M U σ q (d+2*n) (d+2*n+2*n) w copies),
      ∃ f : Frame σ (U × (ProductSlots q (d+2*n) ⊕ B.Bin)),
        f.size ≤ 1 + Fintype.card U*(C*(d+1)^p) ∧
        ∀ {P : Type} {bits : P → ℕ} {K : Type*} (input : Fin copies → Pack D P bits K)
          (active : ∀ i, (input i).layout.Edge → Bool)
          (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
          (L : PreparedBins.Labels B input active sites) (slot : (parallelPacks input).layout.Edge ↪ U)
          (pick : Fin copies → M) (shift : Fin copies → Cube D → Deck (d+2*n)) (x : σ → Bool),
          JointReads B enum a input active sites L slot pick shift x hd → ∀ z : Active input active,
            ∃ b, B.tag input active L.kind L.lift z.1 (perm (pick z.1),word (pick z.1),shift z.1) z.2.val = some b ∧
            ∀ j, f.eval x (slot ⟨z.1,z.2.val⟩,j) = PublicMovedBin.binWires B enum b j := by
  obtain ⟨C,p,rows⟩ := PublicMovedBin.activeMotionBin_frames B enum perm word
  refine ⟨C,p,?_⟩
  intro d hd w copies U σ instU instσ a
  obtain ⟨g,hg,sem⟩ := rows d hd
  let row (u : U) : Frame σ (ProductSlots q (d+2*n) ⊕ B.Bin) := g.subst (Frame.initial (a.dispatch u))
  obtain ⟨all,hall,he⟩ := exists_parallelFrames row
  refine ⟨all.select (fun uj => ⟨uj.1,uj.2⟩),?_,?_⟩
  · have h (u : U) : (row u).size ≤ C*(d+1)^p := by simpa [row] using hg
    have sum := Finset.sum_le_sum (s := Finset.univ) (fun u _ => h u)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] at sum
    simpa only [Frame.select_size] using hall.trans (Nat.add_le_add_left sum 1)
  · intro P bits K input active sites L slot pick shift x reads z
    obtain ⟨b,hb,bit⟩ := sem input active sites L z (pick z.1) (shift z.1)
    refine ⟨b,hb,fun j => ?_⟩
    let u := slot ⟨z.1,z.2.val⟩
    have source : (Frame.initial (a.dispatch u)).eval x = x ∘ a.dispatch u := funext (Frame.initial_eval _ _)
    simp only [Frame.select_eval,he,row,Frame.subst_eval]
    rw [source,reads.dispatch_value B enum a input active sites L slot pick shift x z]
    exact congrFun bit j

end Shortening.PublicPopulation

end BorderVNP
end Computability
end OAI
