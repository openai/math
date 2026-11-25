import OAI.Computability.BorderVNP.ShortenPublicPopulationAddresses
import OAI.Computability.BorderVNP.ShortenPublicPopulationJoint
import OAI.Computability.BorderVNP.ShortenPublicPopulationMovedRows

/-! # Numeric interval-directory input for the chosen whole-pack motions -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicPopulation

open Cover Cover.Frame Cover.AddressCircuit Epoch Crossing Packing PackMotions Hecke
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {D q n : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) (enum : Fin q ≃ Cube D)
    {M : Type*} [Fintype M] [DecidableEq M] (perm : M → Equiv.Perm (Cube D))
    (word : M → ProductSample (lattice 1) elliptic (Cube D) n)

/-- Every active named old cable presents its true numeric moved-bin address
to the directory. The stage preserves all raw endpoint, width, and activity
wires, so they can be used alongside this key for cutting and scattering. -/
theorem jointAddress_frames :
    ∃ C p : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d) (w copies : ℕ) {U σ : Type*} [Fintype U] [Fintype σ]
      (a : JointPins (↥B.types) M U σ q (d+2*n) (d+2*n+2*n) w copies),
      let r := Nat.clog 2 (Fintype.card B.Bin)
      ∃ f : Frame σ (σ ⊕ U × Fin (r+keyWidth q (d+2*n))),
        f.size ≤ 1 + Fintype.card U*(C*(d+1)^p) + Fintype.card U*r*(2*Fintype.card B.Bin+1) ∧
        (∀ x j, f.eval x (.inl j) = x j) ∧
        ∀ {P : Type} {bits : P → ℕ} {K : Type*} (input : Fin copies → Pack D P bits K)
          (active : ∀ i, (input i).layout.Edge → Bool)
          (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
          (L : PreparedBins.Labels B input active sites) (slot : (parallelPacks input).layout.Edge ↪ U)
          (pick : Fin copies → M) (shift : Fin copies → Cube D → Deck (d+2*n)) (x : σ → Bool),
          JointReads B enum a input active sites L slot pick shift x hd →
          Represents (addressedPins a.live a.width) (parallelPacks input).layout
            (jointTags B perm word input active sites L pick shift) slot
            (addressCode enum (binCode B.Bin)) (f.eval x) := by
  obtain ⟨C,p,make⟩ := jointRows_frames B enum perm word
  refine ⟨C,p,?_⟩
  intro d hd w copies U σ instU instσ a r
  obtain ⟨rows,hsize,values⟩ := make d hd w copies a
  let code := binCode B.Bin
  refine ⟨addressFrame code rows,(addressFrame_size _ _).trans (Nat.add_le_add_right hsize _),
    addressFrame_input _ _,?_⟩
  intro P bits K input active sites L slot pick shift x reads
  let tags := jointTags B perm word input active sites L pick shift
  have mask (e : (parallelPacks input).layout.Edge) : (tags e).isSome = active e.1 e.2 :=
    jointTags_mask B perm word input active sites L pick shift e
  refine addressFrame_represents enum code rows (parallelPacks input).layout tags slot a.live a.width x
    (fun e => (reads.live e).trans (mask e).symm) reads.empty ?_ ?_
  · intro e b hb
    let z : Active input active := ⟨e.1,e.2,by rw [← mask e,hb]; rfl⟩
    obtain ⟨c,hc,fields⟩ := values input active sites L slot pick shift x reads z
    have eq : c = b := Option.some.inj (hc.symm.trans hb)
    subst b
    refine ⟨fun j => fields (.inl j),fun b => ?_⟩
    have field : rows.eval x (slot e,.inr b) = PublicMovedBin.binWires B enum c (.inr b) := fields _
    rw [field]
    simp [PublicMovedBin.binWires]
  · intro e b hb
    exact reads.widths ⟨e.1,e.2,by rw [← mask e,hb]; rfl⟩

end Shortening.PublicPopulation

end BorderVNP
end Computability
end OAI
