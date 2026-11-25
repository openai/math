import OAI.Computability.BorderVNP.ShortenPreparedLabels
import OAI.Computability.BorderVNP.CoverPackRowFrame
import OAI.Computability.BorderVNP.CoverSiteMotionNeighbors

/-!
# Reading the actual sampled bin from a cable's source tile

A prepared segment type fixes its midpoint tangent frame relative to the
tile of its source endpoint. Its dynamic source tile and the common pack
translation suffice to recover the canonical moved midpoint tile and the
bin of the prepared chart. The emitted frame uses finite tables and deck
arithmetic, with the matrices and the factor permutation fixed by the pack
motion.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicMovedBin

open Cover Cover.Frame Cover.AddressCircuit Hecke Epoch Crossing PackMotions Framed
open scoped Classical

variable {q D n : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
variable (B : PreparedBins D S h η) (enum : Fin q ≃ Cube D)

/-- Integral representative of the source endpoint's tile, using the joint
lift of the relative segment in each factor. -/
noncomputable def sourceTile (t : B.types) (b : Cube D → gamma 1) (i : Cube D) : gamma 1 :=
  b i * (Catalog.toTile t.val.ends.1 i)⁻¹

/-- At every positive cover depth the source tile is the canonical address
of the projected source point, including tie-resolved boundaries. -/
theorem sourceTile_address (t : B.types) (b : Cube D → gamma 1)
    (l : ℕ) (hl : 0 < l) (i : Cube D) :
    addressAt l hl ((productProjection l (translatePoint b t.val.ends.1)) i) =
      (sourceTile B t b i : Deck l) := by
  cases l with
  | zero => omega
  | succ l =>
    change ((toBaseTile (gammaSL 1 (b i) • t.val.ends.1 i))⁻¹ : Deck (l+1)) = _
    rw [toBaseTile_smul, QuotientGroup.mk_mul, _root_.mul_inv_rev, QuotientGroup.mk_inv, inv_inv]
    rfl

private noncomputable def anchoredFrame (t : B.types) (j : Cube D) : SL :=
  gammaSL 1 (Catalog.toTile t.val.ends.1 j) * frameOfTangent (t.val.center j) (t.val.direction j)

private theorem source_frame (t : B.types) (b : Cube D → gamma 1) (p : Equiv.Perm (Cube D))
    (i : Cube D) :
    gammaSL 1 (sourceTile B t b (p i)) * anchoredFrame B t (p i) = sourceFrame t.val b p i := by
  simp [sourceTile, anchoredFrame, sourceFrame, mul_assoc]

/-- The deck name and relative bin of the exact whole-pack sample for this
oriented segment, prior to serialization into bits. -/
noncomputable def sampleBin {l : ℕ} (t : B.types) (b : Cube D → gamma 1)
    (p : Equiv.Perm (Cube D)) (word : ProductSample (lattice 1) elliptic (Cube D) n)
    (shift : Cube D → Deck l) : (Cube D → Deck l) × B.Bin :=
  (shiftedAddress shift (movedCarry t.val b p word), ⟨t, (B.chart t).code (configuration t.val b p word)⟩)

/-- Canonical tile bits and the one-hot relative bin of a sampled active edge. -/
noncomputable def binWires {l : ℕ} (a : (Cube D → Deck l) × B.Bin) :
    ProductSlots q l ⊕ B.Bin → Bool :=
  Sum.elim (productWires l (a.1 ∘ enum)) (fun u => decide (u=a.2))

private noncomputable def relativeBin (t : B.types) (p : Equiv.Perm (Cube D))
    (u : Fin q → SL) : B.Bin :=
  let z (i : Cube D) := frameCoordinates (u (enum.symm i))
  ⟨t, (B.chart t).code (WithLp.toLp 2 (fun i => (z i).1),
    fromAngles (speed t.val) p (fun i => (z i).2 ^ 2))⟩

/-- One circuit computes the exact moved midpoint tile and relative chart
bin for all segment types, source lifts, and common posttranslations. -/
theorem movedBin_frames (p : Equiv.Perm (Cube D))
    (word : ProductSample (lattice 1) elliptic (Cube D) n) :
    ∃ C k : ℕ, ∀ d : ℕ, 1 ≤ d →
      ∃ f : VPVNP.VerifierNetwork.Frame
        (↥B.types ⊕ (ProductSlots q (d+2*n) ⊕ ProductSlots q (d+2*n+2*n)))
        (ProductSlots q (d+2*n) ⊕ B.Bin), f.size ≤ C*(d+1)^k ∧
        ∀ (t : B.types) (b : Cube D → gamma 1) (shift : Cube D → Deck (d+2*n)),
          f.eval (rowInput t (shift ∘ enum)
            (fun j => (sourceTile B t b (enum j) : Deck (d+2*n+2*n)))) =
          binWires B enum (sampleBin B t b p word shift) := by
  let g (j : Fin q) := wordMatrix word (enum j)
  let perm := (enum.trans p).trans enum.symm
  let rel (t : B.types) (j : Fin q) := anchoredFrame B t (enum j)
  let code (t : B.types) (u : Fin q → SL) (i : B.Bin) := decide (i = relativeBin B enum t p u)
  obtain ⟨C,k,all⟩ := geometricPackRow_frames (T := ↥B.types) (I := B.Bin) (g := g)
    (fun j => wordMatrix_clears word (enum j))
  refine ⟨C,k,fun d hd => ?_⟩
  obtain ⟨f,hs,he⟩ := all d hd perm rel code
  refine ⟨f, hs, fun t b shift => ?_⟩
  let move (j : Fin q) := gammaSL 1 (shift (enum j)).out *
    (g j * (gammaSL 1 (sourceTile B t b (enum (perm j))) * rel t (perm j)))
  have motion (j) : move j = gammaSL 1 (shift (enum j)).out *
      (wordMatrix word (enum j) * sourceFrame t.val b p (enum j)) := by
    simp only [move, rel, perm, Equiv.trans_apply, Equiv.apply_symm_apply, source_frame, g]
  have tiles (j) : (frameCarry (move j) : Deck (d+2*n)) = (sampleBin B t b p word shift).1 (enum j) := by
    rw [motion, frameCarry_translate, QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rfl
  have frames (i : Cube D) : relativeFrame (move (enum.symm i)) =
      relativeFrame (wordMatrix word i * sourceFrame t.val b p i) := by
    rw [motion, relativeFrame_translate, Equiv.apply_symm_apply]
  have bin : relativeBin B enum t p (fun i => relativeFrame (move i)) = (sampleBin B t b p word shift).2 := by
    dsimp only [relativeBin, sampleBin]
    simp only [frames]
    rfl
  have hactual := he t (fun j => (shift (enum j)).out) (fun j => sourceTile B t b (enum j))
  simp only [QuotientGroup.out_eq'] at hactual
  rw [show shift ∘ enum = (fun j => shift (enum j)) from rfl, hactual]
  funext o
  cases o with
  | inl j =>
    change deckWires _ (frameCarry (move j.1) : Deck _) j.2 = _
    rw [tiles]
    rfl
  | inr i =>
    change decide (i = relativeBin B enum t p (fun j => relativeFrame (move j))) =
      decide (i = (sampleBin B t b p word shift).2)
    rw [bin]

/-- For an active physical cable the chart bin and midpoint tile computed
from its prepared type and lift are exactly the geometric sample tag. -/
theorem sampleBin_eq_tag {copies depth : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
    (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
    (kind : Active input active → B.types) (lift : Active input active → Cube D → gamma 1)
    (w : Active input active) (s : PackSample (lattice 1) elliptic (Cube D) depth n) :
    B.tag (d := depth) input active kind lift w.1 s w.2.val =
      some (sampleBin B (kind w) (lift w) s.1 s.2.1 s.2.2) := by
  simp only [PreparedBins.tag, sampledBin, dite_eq_left w.2.property]
  rfl

/-- The public tile address of an actual source site is the deck reduction
of the prepared segment's source lift. -/
theorem label_source_address {copies l : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
    (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
    (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) l)
    (L : PreparedBins.Labels B input active sites) (w : Active input active) (hl : 0 < l) :
    (fun j => addressAt l hl ((sites w.1 ((input w.1).layout.src w.2.val)) (enum j))) =
      (fun j => (sourceTile B (L.kind w) (L.lift w) (enum j) : Deck l)) := by
  rw [← L.src w]
  exact funext (fun j => sourceTile_address B (L.kind w) (L.lift w) l hl (enum j))

/-- At a physical old cable row, the source address comes directly from
the placed source site. The resulting output bits encode precisely the
actual sampled tag for that edge. -/
theorem activeMovedBin_frames (p : Equiv.Perm (Cube D))
    (word : ProductSample (lattice 1) elliptic (Cube D) n) :
    ∃ C k : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d),
      ∃ f : VPVNP.VerifierNetwork.Frame
        (↥B.types ⊕ (ProductSlots q (d+2*n) ⊕ ProductSlots q (d+2*n+2*n)))
        (ProductSlots q (d+2*n) ⊕ B.Bin), f.size ≤ C*(d+1)^k ∧
        ∀ {copies : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
          (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
          (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
          (L : PreparedBins.Labels B input active sites) (w : Active input active)
          (shift : Cube D → Deck (d+2*n)),
          ∃ a : (Cube D → Deck (d+2*n)) × B.Bin,
            B.tag (d := d+2*n) input active L.kind L.lift w.1 (p,word,shift) w.2.val = some a ∧
            f.eval (rowInput (L.kind w) (shift ∘ enum) (fun j => addressAt _ (by omega)
              ((sites w.1 ((input w.1).layout.src w.2.val)) (enum j)))) = binWires B enum a := by
  obtain ⟨C,k,H⟩ := movedBin_frames B enum p word
  refine ⟨C,k,fun d hd => ?_⟩
  obtain ⟨f,hs,he⟩ := H d hd
  refine ⟨f,hs,fun input active sites L w shift => ?_⟩
  refine ⟨sampleBin B (L.kind w) (L.lift w) p word shift,
    sampleBin_eq_tag B input active L.kind L.lift w (p,word,shift), ?_⟩
  rw [label_source_address B enum input active sites L w]
  exact he _ _ _

end Shortening.PublicMovedBin

end BorderVNP
end Computability
end OAI
