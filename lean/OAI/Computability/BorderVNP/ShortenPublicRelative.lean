import OAI.Computability.BorderVNP.ShortenProfileCatalog
import OAI.Computability.BorderVNP.CoverPackRowFrame

/-!
# Finite relative site table for one shortening motion

A row stores the site's normalized position in the old catalog and the product
deck address of its tile. The chosen permutation and cleared matrices act on
the whole lifted point. The relative output depends only on the old catalog
entry and the low residues. The separate posttranslation affects its tile.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicRelative

open Crossing Catalog Epoch Cover Cover.AddressCircuit
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {I : Type*} [Fintype I] {q D m : ℕ} {K : Type*} [Field K]

/-- Integral lift of the tile containing each coordinate. -/
noncomputable def carry (x : HyperbolicHost I) : I → gamma 1 :=
  fun i => (toTile x i)⁻¹

omit [Fintype I] in
/-- Recovering a lifted point uses the carry of its own tile, including on seams. -/
theorem carry_smul_normalize (x : HyperbolicHost I) (i : I) :
    gammaSL 1 (carry x i) • normalize x i = x i := by
  change gammaSL 1 (toTile x i)⁻¹ • (gammaSL 1 (toTile x i) • x i) = x i
  rw [map_inv,inv_smul_smul]

/-- Actual lifted site after the permuted motion and the shared posttranslation. -/
noncomputable def moved (p : Pattern I D) (n : Fin p.moves) (shift : I → gamma 1)
    (x : HyperbolicHost I) : HyperbolicHost I :=
  translatePoint shift (motion (p.perm n) (p.matrix n) x)

/-- Contents of the relative point table at a low address, before any deep
level, tile translation or histogram has been chosen. -/
noncomputable def lowSite (p : Pattern I D) (n : Fin p.moves) (t : HyperbolicHost I)
    (key : I → Deck (1 + 2*p.depth)) : HyperbolicHost I :=
  WithLp.toLp 2 fun i =>
    Cover.Frame.relativeFrame (Cover.Frame.movedLowFrame (p.matrix n i)
      (key (p.perm n i)) (t (p.perm n i)).toSL2R) • UpperHalfPlane.I

private theorem frame_position (p : Pattern I D) (n : Fin p.moves)
    (shift : I → gamma 1) (x : HyperbolicHost I) (i : I) :
    (gammaSL 1 (shift i) * (p.matrix n i *
      (gammaSL 1 (carry x (p.perm n i)) * (normalize x (p.perm n i)).toSL2R))) •
        UpperHalfPlane.I = moved p n shift x i := by
  rw [mul_smul,mul_smul,mul_smul,UpperHalfPlane.toSL2R_smul_I,carry_smul_normalize]
  rfl

/-- The fixed table yields the exact normalized position of every lifted site.
All left posttranslations and all representatives of the same low key agree. -/
theorem lowSite_exact (p : Pattern I D) (n : Fin p.moves) (shift : I → gamma 1)
    (x : HyperbolicHost I) :
    lowSite p n (normalize x) (fun i => (carry x i : Deck (1 + 2*p.depth))) =
      normalize (moved p n shift x) := by
  ext1 i
  let j := p.perm n i
  let g := gammaSL 1 (shift i) * (p.matrix n i *
    (gammaSL 1 (carry x j) * (normalize x j).toSL2R))
  have hf : Cover.Frame.relativeFrame g = Cover.Frame.relativeFrame
      (Cover.Frame.movedLowFrame (p.matrix n i) (carry x j : Deck (1 + 2*p.depth))
        (normalize x j).toSL2R) := by
    dsimp only [g]
    rw [Cover.Frame.relativeFrame_translate,Cover.Frame.moved_relative_eq (p.clears n i)]
  change Cover.Frame.relativeFrame _ • UpperHalfPlane.I = _
  rw [← hf,Cover.Frame.relativeFrame,mul_smul,show g • UpperHalfPlane.I = _ from
    frame_position p n shift x i]
  rfl

/-- Successor catalog name of the moved site. The two members of a tie use
the same normalization and the catalog is shared by all choices of profile. -/
noncomputable def movedIndex (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) (n : Fin p.moves) (shift : I → gamma 1)
    (x : HyperbolicHost I) (hx : normalize x ∈ S) : ↥(p.nextSites e S) :=
  ⟨normalize (moved p n shift x),Finset.mem_union_left _
    (p.mem_movedSites S n x hx shift)⟩

/-- Finite lookup of the successor catalog index. An out-of-catalog row
has no index. Every input row arising from a physical lift has one. -/
noncomputable def lowIndex (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) (n : Fin p.moves) (t : ↥S)
    (key : I → Deck (1 + 2*p.depth)) : Option ↥(p.nextSites e S) :=
  if h : lowSite p n t.val key ∈ p.nextSites e S then some ⟨_,h⟩ else none

/-- All deep lifts of a catalogued row select its actual successor index
from the fixed table, before its high tile address is computed. -/
theorem lowIndex_exact (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) (n : Fin p.moves) (shift : I → gamma 1)
    (x : HyperbolicHost I) (hx : normalize x ∈ S) :
    lowIndex p e S n ⟨normalize x,hx⟩ (fun i => (carry x i : Deck (1 + 2*p.depth))) =
      some (movedIndex p e S n shift x hx) := by
  have h := lowSite_exact p n shift x
  have hm := (movedIndex p e S n shift x hx).property
  change normalize (moved p n shift x) ∈ p.nextSites e S at hm
  simp only [lowIndex,dite_eq_left (h ▸ hm),Option.some.injEq,Subtype.ext_iff]
  exact h

/-- Integral displacement supplied by the same low-residue table in one
factor. Its value is independent of the modulus at which it will be used. -/
noncomputable def lowCarry (p : Pattern I D) (n : Fin p.moves) (t : HyperbolicHost I)
    (i : I) (key : Deck (1 + 2*p.depth)) : gamma 1 :=
  Cover.Frame.frameCarry (Cover.Frame.movedLowFrame (p.matrix n i) key (t (p.perm n i)).toSL2R)

/-- The output deck name is the posttranslation times the modular correction
times the integral carry from the fixed table, with the permuted source factor. -/
theorem carry_exact (p : Pattern I D) (n : Fin p.moves) (shift : I → gamma 1)
    (x : HyperbolicHost I) (i : I) {d : ℕ} (hd : 1 ≤ d) :
    (carry (moved p n shift x) i : Deck (d+2*p.depth)) =
      (shift i : Deck (d+2*p.depth)) * Cover.Frame.placedTile (p.clears n i) hd
        (fun key => (lowCarry p n (normalize x) i key : Deck (d+2*p.depth)))
        (carry x (p.perm n i) : Deck (d+2*p.depth+2*p.depth)) := by
  change ((Cover.Frame.toBaseTile (moved p n shift x i))⁻¹ : Deck _) = _
  rw [← frame_position p n shift x i]
  change (Cover.Frame.frameCarry (_ * _) : Deck _) = _
  rw [Cover.Frame.frameCarry_translate,QuotientGroup.mk_mul,
    Cover.Frame.moved_carry_eq (p.clears n i) hd]
  rfl

/-- The canonical product tile wires of a lifted point. Enumerating the
factors only numbers the wires; the tile itself is obtained by normalization. -/
noncomputable def tileWord (enum : Fin q ≃ I) (l : ℕ) (x : HyperbolicHost I) :
    ProductSlots q l → Bool :=
  productWires l (fun i => (carry x (enum i) : Deck l))

/-- Wires read by one retained record in a pack. -/
noncomputable def siteInput (enum : Fin q ≃ I) (S : Finset (HyperbolicHost I))
    (l z : ℕ) (shift : I → gamma 1) (x : HyperbolicHost I) (hx : normalize x ∈ S) :
    ↥S ⊕ (ProductSlots q l ⊕ ProductSlots q z) → Bool :=
  rowInput (⟨normalize x,hx⟩ : ↥S) (fun i => (shift (enum i) : Deck l))
    (fun i => (carry x (enum i) : Deck z))

/-- Exact semantics of a moved public site row. The two outputs are the deep
tile address and the unique one-hot index in the next round's catalog. -/
def SiteRow (enum : Fin q ≃ I) (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) (n : Fin p.moves) (d : ℕ)
    (f : Frame (↥S ⊕ (ProductSlots q (d+2*p.depth) ⊕ ProductSlots q (d+2*p.depth+2*p.depth)))
      (ProductSlots q (d+2*p.depth) ⊕ ↥(p.nextSites e S))) : Prop :=
  ∀ shift x (hx : normalize x ∈ S),
    f.eval (siteInput enum S _ _ shift x hx) =
      Sum.elim (tileWord enum _ (moved p n shift x))
        (fun t => decide (t = movedIndex p e S n shift x hx))

set_option maxHeartbeats 1200000 in
/-- For a fixed motion every retained site's address and successor index are
computed by a shared Boolean circuit polynomial in the cover depth. -/
theorem siteRow_frames (enum : Fin q ≃ I) (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) (n : Fin p.moves) :
    ∃ C k : ℕ, ∀ d : ℕ, 1 ≤ d → ∃ f, SiteRow enum p e S n d f ∧ Frame.size f ≤ C*(d+1)^k := by
  let g (i : Fin q) := p.matrix n (enum i)
  let perm := (enum.trans (p.perm n)).trans enum.symm
  let types (t : ↥S) (j : Fin q) := (t.val (enum j)).toSL2R
  let classify (_ : ↥S) (u : Fin q → Cover.Frame.SL) (v : ↥(p.nextSites e S)) :=
    decide (v.val = WithLp.toLp 2 (fun i => u (enum.symm i) • UpperHalfPlane.I))
  obtain ⟨C,k,h⟩ := geometricPackRow_frames (T := ↥S) (I := ↥(p.nextSites e S))
    (g := g) (fun i => p.clears n (enum i))
  refine ⟨C,k,?_⟩
  intro d hd
  obtain ⟨f,hsize,he⟩ := h d hd perm types classify
  refine ⟨f,?_,hsize⟩
  intro shift x hx
  let old : ↥S := ⟨normalize x,hx⟩
  let mtx (i : Fin q) := gammaSL 1 (shift (enum i)) *
    (g i * (gammaSL 1 (carry x (enum (perm i))) * types old (perm i)))
  have hpos (i) : mtx i • UpperHalfPlane.I = moved p n shift x (enum i) := by
    simpa only [mtx,g,perm,Equiv.trans_apply,Equiv.apply_symm_apply,types,old]
      using frame_position p n shift x (enum i)
  have hrel : WithLp.toLp 2 (fun i => Cover.Frame.relativeFrame (mtx (enum.symm i)) •
      UpperHalfPlane.I) = normalize (moved p n shift x) := by
    ext1 i
    change Cover.Frame.relativeFrame _ • UpperHalfPlane.I = _
    rw [Cover.Frame.relativeFrame,mul_smul,hpos,Equiv.apply_symm_apply]
    rfl
  rw [siteInput,he]
  funext j
  cases j with
  | inl j =>
    change deckWires _ (Cover.Frame.frameCarry (mtx j.1) : Deck _) j.2 = _
    rw [Cover.Frame.frameCarry,hpos]
    rfl
  | inr j =>
    change decide (j.val = WithLp.toLp 2 (fun i => Cover.Frame.relativeFrame (mtx (enum.symm i)) •
      UpperHalfPlane.I)) = decide (j = movedIndex p e S n shift x hx)
    rw [hrel]
    exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq,Subtype.ext_iff]; rfl)

end Shortening.PublicRelative

end BorderVNP
end Computability
end OAI
