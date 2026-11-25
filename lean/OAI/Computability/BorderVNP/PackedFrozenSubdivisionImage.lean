import OAI.Computability.BorderVNP.PackedFrozenSubdivisionTape
import OAI.Computability.BorderVNP.PackedSubdivisionPrivatePrograms
import OAI.Computability.BorderVNP.PackedFrozenTapeSections

/-! # Full private row history through physical subdivision

Original sites retain all earlier immutable records and append the chosen endpoint
copies. An inserted relay receives its one equality row. The shared Boolean tape
translates only the earlier owner keys and concatenates both source rectangles.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision.Gates

open Crossing Shortening Shortening.PublicCapacity ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical
open private limits from OAI.Computability.BorderVNP.PackedSubdivisionSlices

variable {D np extra C C' d d' k k' w : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    {N : Network D P bits} {s : Shape} {σ : Type*} [Fintype σ]
variable (old : Rows s N) (route : N.WireRoutes) (fit : ∀ e, route.interior e ≤ extra)
variable (portID : P ↪ Fin np)
variable (oldF : CellAddressCircuit.Fields s.sites s.edges np C d k w σ)
variable (newF : CellAddressCircuit.Fields (s.sites+extra*s.edges) ((extra+1)*s.edges) np C' d' k' w σ)
variable (work extent : Fin s.sites → Fin w → σ) (present : Fin ((extra+1)*s.edges) → σ)
local notation3 "G" => N.subdivide route
local notation3 "rows" => old.subdivide route extra fit
variable {x : σ → Bool}
local notation3 "st" => (table oldF newF work extent).eval x
local notation3 "F" => tableFields oldF newF present
variable (prior : Site.Programs N)
variable (oldData : Views.EndpointData N oldF old.site old.edge portID x)
variable (newData : Views.EndpointData (N.subdivide route) newF (old.subdivide route extra fit).site
  (old.subdivide route extra fit).edge portID x)
variable (oldFit : ∀ v, incoming N v < 2^w) (newFit : ∀ v, incoming (N.subdivide route) v < 2^w)
variable (live : ∀ i, x (present i) = true ↔ i ∈ Set.range (old.subdivide route extra fit).edge)
variable (shape : ∀ e, route.interior e = 0 ∨ route.interior e = extra)
variable (hw : ∀ v, value (x ∘ work (old.site v)) = (prior v).program.work)
variable (he : ∀ v, value (x ∘ extent (old.site v)) = (prior v).program.size)

open FrozenTape
variable {R B : Type*} [Fintype R] [Fintype B] (S : Schema R B) (previous : Frame σ (FrozenTape.Pins R B d))

/-- Actual successor codebook on the reserved prefix of original site rows. -/
noncomputable def retainedCodes : Fin s.sites ↪ Fin (2^d') := (Fin.castAddEmb (extra*s.edges)).trans newF.sites

/-- Translate old frozen owner keys to the true retained addresses and append new sparse words. -/
noncomputable def completeTape :=
  appendFrame ((FrozenTape.rekey oldF.sites (retainedCodes newF)).subst previous)
    (tapeFrame oldF newF work extent present)

omit [Fintype P] in
/-- The previous complete image, transported to the successor codes, occupies exactly
the old sites. No inserted relay receives an inherited record from this transport. -/
theorem carrySection (prior : N.Site → Site)
    (before : S.Image (previous.eval x) ((old.site.trans oldF.sites).trans Fin.valEmbedding) prior) :
    S.Section (((FrozenTape.rekey oldF.sites (retainedCodes newF)).subst previous).eval x)
      (((rows).site.trans newF.sites).trans Fin.valEmbedding)
      (Sum.elim (fun v => (prior v).rows) (fun _ => [])) := by
  let f := FrozenTape.rekey (R:=R) (B:=B) oldF.sites (retainedCodes newF)
  have original : S.Block (previous.eval x) (fun v => (oldF.sites (old.site v)).val)
      (fun v => (prior v).rows.map marked) := before.toSection _
  have translated := original.rekey S oldF.sites (retainedCodes newF)
  have codeEq (v : N.Site) : (retainedCodes newF (old.site v)).val = (newF.sites ((rows).site (.inl v))).val := rfl
  have ev : (f.subst previous).eval x = f.eval (previous.eval x) := funext fun i => Frame.subst_eval _ _ _ _
  change S.Section ((f.subst previous).eval x) _ _
  rw [ev]
  constructor
  · intro r hr en
    obtain ⟨v,kv⟩ := translated.owners r hr en
    exact ⟨.inl v,kv.trans (codeEq v)⟩
  · rintro (v | j)
    · exact translated.atSite v
    · apply translated.fresh S
      intro v eqn
      have h := ((rows).site.injective (newF.sites.injective (Fin.ext ((codeEq v).symm.trans eqn))))
      cases h

include oldData newData oldFit newFit live shape hw he in
/-- One fixed tape circuit exports the entire chronological, canonically marked
private row list for every site of the true subdivided network. -/
theorem completeTape_image
    (before : S.Image (previous.eval x) ((old.site.trans oldF.sites).trans Fin.valEmbedding)
      (fun v => (prior v).program))
    (room : ∀ v, (prior v).program.size + incoming G (.inl v) < 2^w) (one : 1 < 2^w) :
    (S.append (tapeSchema s.edges np extra w)).Image
      ((completeTape oldF newF work extent present previous).eval x)
      (((rows).site.trans newF.sites).trans Fin.valEmbedding)
      (fun v => (subdividePrivatePrograms N route old.edge (rows).edge portID prior v).program) := by
  let previousRows := Sum.elim (fun v => (prior v).program.rows) (fun _ : (e : N.Edge) × Fin (route.interior e) => [])
  let id := (((rows).site.trans newF.sites).trans Fin.valEmbedding)
  let stages := fun v => (prior v).program
  let fresh := addedRecords old route fit portID stages
  let rekeyed := (FrozenTape.rekey oldF.sites (retainedCodes newF)).subst previous
  have oldSection : S.Section (rekeyed.eval x) id previousRows :=
    carrySection old route fit oldF newF S previous stages before
  have newSection : (tapeSchema s.edges np extra w).Section ((tapeFrame oldF newF work extent present).eval x) id fresh :=
    tapeBlock old route fit portID oldF newF work extent present stages oldData newData oldFit newFit live shape hw he
      (fun v => (prior v).size) room one
  have h := appendFrame_section S (tapeSchema s.edges np extra w) rekeyed (tapeFrame oldF newF work extent present)
    x id previousRows fresh oldSection newSection
  apply h.image _ _
  rintro (v | j)
  · exact (Site.retain_rows (stages v) _ _).symm
  · rfl

/-- The complete tape charges the previous block, the one sparse owner-key translation,
and the subdivision's own nine-field frame, without expanding private factor entries. -/
theorem completeTape_size :
    (completeTape oldF newF work extent present previous).size =
      previous.size + (FrozenTape.rekey (R:=R) (B:=B) oldF.sites (retainedCodes newF)).size +
        (frozen oldF newF work extent present).size := by
  simp [completeTape,appendFrame_size,Frame.subst_size,tapeFrame_size]

end Packing.Inherited.Subdivision.Gates

end BorderVNP
end Computability
end OAI
