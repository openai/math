import OAI.Computability.BorderVNP.ShortenPublicPopulation
import OAI.Computability.BorderVNP.CoverDeckProductKey
import OAI.Computability.BorderVNP.CoverProductPlacementFrame

/-! # Numeric bin addresses from moved product-tile wires

A marker combines the canonical quaternion wires with the finite relative-bin
ordinal. The same key is obtained on a moved row by rewiring its tile and bin
fields. The population network therefore needs one marker per geometric address,
independently of the gaps in its numerical key space.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicPopulation

open Cover Cover.AddressCircuit ParseBatchCounts ParseBatchSort ParseBatchLookup PackedHistogram
open VPVNP.VerifierNetwork (Frame)

variable {q l r w D : ℕ} {U σ : Type*} {B : Type}

/-- Fixed numerical encoding for the finite relative-bin alphabet, including an empty alphabet. -/
noncomputable def binCode (B : Type) [Fintype B] :
    B ↪ Fin (2^(Nat.clog 2 (Fintype.card B))) :=
  (Fintype.equivFin B).toEmbedding.trans (Fin.castLEEmb (Nat.le_pow_clog (by decide) _))

/-- Key of a legal pair consisting of a moved tile and a relative bin. -/
noncomputable def tileBinCode (q l : ℕ) (b : B ↪ Fin (2^r)) :
    ((Fin q → Deck l) × B) ↪ Fin (2^(r+keyWidth q l)) where
  toFun a := numberWords _ (prepend (keyWord q l a.1) ((numberWords r).symm (b a.2)))
  inj' := by
    intro a c h
    have he := (numberWords _).injective h
    apply Prod.ext
    · apply (productKey q l).injective
      apply congrArg (numberWords _)
      funext j
      simpa only [prepend_high] using congrFun he (highPin r j)
    · apply b.injective
      apply (numberWords r).symm.injective
      funext j
      simpa only [prepend_low] using congrFun he (lowPin (keyWidth q l) j)

/-- Join the moved tile's actual physical slots and the relative-bin wires without gates. -/
def tilePins (active : U → σ) (tile : U → ProductSlots q l → σ) (rel : U → Fin r → σ)
    (width : U → Fin w → σ) : Pins U σ (r+keyWidth q l) w where
  active := active
  key u := prepend (tile u ∘ (keySlots q l).symm) (rel u)
  width := width

/-- Rewiring a valid tile and relative field yields its numeric bin key. -/
theorem tilePins_address (active : U → σ) (tile : U → ProductSlots q l → σ)
    (rel : U → Fin r → σ) (width : U → Fin w → σ) (x : σ → Bool)
    (b : B ↪ Fin (2^r)) (u : U) (a : (Fin q → Deck l) × B)
    (ht : x ∘ tile u = productWires l a.1) (hb : x ∘ rel u = (numberWords r).symm (b a.2)) :
    value (x ∘ (tilePins active tile rel width).key u) = (tileBinCode q l b a).val := by
  have hp : x ∘ (tile u ∘ (keySlots q l).symm) = keyWord q l a.1 := by
    funext j
    exact congrFun ht ((keySlots q l).symm j)
  change value (x ∘ prepend _ _) = value (prepend _ _)
  rw [prepend_map,hp,hb]

variable [Fintype U] [Fintype B] [Fintype σ]
variable {P : Type*} {bits : P → ℕ} (N : Crossing.Network D P bits)
    (bin : N.Edge → Option ((Fin q → Deck l) × B)) (slot : N.Edge ↪ U)
    (active : U → σ) (tile : U → ProductSlots q l → σ) (rel : U → Fin r → σ)
    (width : U → Fin w → σ) (code : B ↪ Fin (2^r))

/-- Exact bin populations on all legal product-tile addresses of a sparse moved table. -/
theorem tileFrame_count (x : σ → Bool)
    (enabled : ∀ e, x (active (slot e)) = (bin e).isSome)
    (empty : ∀ u, u ∉ Set.range slot → x (active u) = false)
    (tileWord : ∀ e a, bin e = some a → x ∘ tile (slot e) = productWires l a.1)
    (binWord : ∀ e a, bin e = some a → x ∘ rel (slot e) = (numberWords r).symm (code a.2))
    (widthWord : ∀ e a, bin e = some a → value (x ∘ width (slot e)) = N.width e)
    (fits : ∀ a, SeedIntervals.count N bin a < 2^w) (a : (Fin q → Deck l) × B) :
    value (fun j => (frame (tilePins active tile rel width) (tileBinCode q l code)).eval x (a,j)) =
      SeedIntervals.count N bin a :=
  frame_count _ _ _ _ _ _ ⟨enabled, empty, fun e a he =>
    tilePins_address _ _ _ _ _ _ _ _ (tileWord e a he) (binWord e a he), widthWord⟩ fits a

/-- Size on the actual cover: one marker per legal tile/bin pair. The key has
ninety bits per cover level per factor, plus the relative-bin ordinal. -/
theorem tileFrame_size :
    let n := Fintype.card U + Fintype.card (Fin q → Deck l)*Fintype.card B
    (frame (tilePins active tile rel width) (tileBinCode q l code)).size ≤
      2*(n+1)*laneCost (Nat.clog 2 n) (r+q*(30*(l+1)*3)) w := by
  simpa only [Fintype.card_prod] using frame_size (tilePins active tile rel width) (tileBinCode q l code)

end Shortening.PublicPopulation

end BorderVNP
end Computability
end OAI
