import OAI.Computability.BorderVNP.ShortenPublicPopulationNamed
import OAI.Computability.BorderVNP.ShortenPublicMotionBin

/-! # Public operands of the combined moved-bin population

Old rows retain stable cable names. A pack's selected motion and posttranslation
are shared across its rows. Each live cable reads the catalog type selected from
its endpoints, the canonical tile of its source endpoint, and its old width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicPopulation

open Cover Cover.AddressCircuit Epoch Crossing Packing PackMotions Hecke
open scoped Classical

/-- Wire references for moved-row dispatch, after the shared endpoint-table join. -/
structure JointPins (T M U σ : Type*) (q l deep w copies : ℕ) where
  /-- Pack owning a reserved row. -/
  home : U → Fin copies
  /-- Active positive segment bit. -/
  live : U → σ
  /-- Binary width of the named cable. -/
  width : U → Fin w → σ
  /-- One-hot oriented relative segment type. -/
  kind : U → T → σ
  /-- Canonical product tile of the source endpoint. -/
  source : U → ProductSlots q deep → σ
  /-- Candidate motion index, one-hot and shared by its whole pack. -/
  choice : Fin copies → M → σ
  /-- Product deck posttranslation, shared by the same pack. -/
  shift : Fin copies → ProductSlots q l → σ

variable {T M U σ : Type*} {q l deep w copies : ℕ}

/-- The row reads its own type and source, and the move and shift of its pack. -/
def JointPins.dispatch (a : JointPins T M U σ q l deep w copies) (u : U) :
    M ⊕ (T ⊕ (ProductSlots q l ⊕ ProductSlots q deep)) → σ :=
  Sum.elim (a.choice (a.home u)) (Sum.elim (a.kind u) (Sum.elim (a.shift (a.home u)) (a.source u)))

variable {D n d : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) (enum : Fin q ≃ Cube D)
    (a : JointPins (↥B.types) M U σ q (d+2*n) (d+2*n+2*n) w copies)
    {P : Type} {bits : P → ℕ} {K : Type*}
    (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
    (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
    (L : PreparedBins.Labels B input active sites) (slot : (parallelPacks input).layout.Edge ↪ U)
    [DecidableEq M] (pick : Fin copies → M) (shift : Fin copies → Cube D → Deck (d+2*n))
    (x : σ → Bool)

/-- Values read by occupied cable slots and the per-copy motion bank. -/
structure JointReads (hd : 1 ≤ d) : Prop where
  /-- The stable name retains the original pack number. -/
  owner : ∀ e, a.home (slot e) = e.1
  /-- A positive charged old cable is a live segment. -/
  live : ∀ e, x (a.live (slot e)) = active e.1 e.2
  /-- Padding is inactive. -/
  empty : ∀ u, u ∉ Set.range slot → x (a.live u) = false
  /-- The active row width is the old cable width. -/
  widths : ∀ z : Active input active, ParseBatchSort.value (x ∘ a.width (slot ⟨z.1,z.2.val⟩)) =
    (input z.1).layout.width z.2.val
  /-- Source and destination were classified jointly by this prepared catalog. -/
  kinds : ∀ z : Active input active, x ∘ a.kind (slot ⟨z.1,z.2.val⟩) = fun t => decide (t=L.kind z)
  /-- The site-table join returns the occupied edge's actual source tile. -/
  sources : ∀ z : Active input active, x ∘ a.source (slot ⟨z.1,z.2.val⟩) = productWires _ (fun j =>
    addressAt _ (by omega) ((sites z.1 ((input z.1).layout.src z.2.val)) (enum j)))
  /-- Shared one-hot candidate selected for each input pack. -/
  choices : ∀ i, x ∘ a.choice i = fun m => decide (m = pick i)
  /-- Shared final deck translation selected for each input pack. -/
  shifts : ∀ i, x ∘ a.shift i = productWires _ (shift i ∘ enum)

/-- The complete operand word at an active row is the physical row input
of the finite-motion classifier at exactly the motion selected by its owner. -/
theorem JointReads.dispatch_value {hd : 1 ≤ d}
    (reads : JointReads B enum a input active sites L slot pick shift x hd) (z : Active input active) :
    x ∘ a.dispatch (slot ⟨z.1,z.2.val⟩) =
      Sum.elim (fun j => decide (j = pick z.1)) (rowInput (L.kind z) (shift z.1 ∘ enum)
        (fun j => addressAt _ (by omega) ((sites z.1 ((input z.1).layout.src z.2.val)) (enum j)))) := by
  have ho := reads.owner ⟨z.1,z.2.val⟩
  funext j
  rcases j with j | (j | (j | j))
  · simpa only [Function.comp_apply, JointPins.dispatch, Sum.elim_inl, ho] using congrFun (reads.choices z.1) j
  · exact congrFun (reads.kinds z) j
  · simpa only [Function.comp_apply, JointPins.dispatch, Sum.elim_inr, Sum.elim_inl, ho, rowInput] using
      congrFun (reads.shifts z.1) j
  · exact congrFun (reads.sources z) j

end Shortening.PublicPopulation

end BorderVNP
end Computability
end OAI
