import OAI.Computability.BorderVNP.PackedBottomReports
import OAI.Computability.BorderVNP.DiagonalTallySidecar

/-! # Source names and physical bytes in the bottom report directory

A weighted verifier vertex carries a parameter and a binary exponent position.
These two immutable names are stored in the opaque site's sidecar. The private
truth factor uses only the selected wire and the relative report lane. Placement
determines the compact absolute use-bit addresses after the site is delivered.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open Crossing CellSparse GridBoxes
open scoped Classical

/-- An original report label carrying two immutable source names. -/
def sourceTag (parameter place : ℕ) : Port := ⟨parameter,place,0⟩

/-- The private serialized sidecar, in the same order as the compact report records. -/
def positions (next : ℕ) (fs : List Factor) : List TallySidecar.Position :=
  (sidecar next fs).map (fun x => ⟨x.1.base,x.1.copyStride,x.2⟩)

/-- The actual packet stores one three-word sidecar position per designated unary row. -/
@[simp] theorem positions_length (next : ℕ) (fs : List Factor) :
    (positions next fs).length = count fs := by simp [positions]

/-- Ordered relative lane addresses of the real private sidecar. -/
theorem positions_ranks (next : ℕ) (fs : List Factor) :
    (positions next fs).map TallySidecar.Position.stagedReportRel = List.range' next (count fs) := by
  simpa only [positions,List.map_map,Function.comp_def] using sidecar_ranks next fs

/-- The names recovered from a physical private factor. -/
def factorTag : Factor → Option Port
  | .unary _ p => some p
  | _ => none

/-- Original labels survive the staging pass exactly in their stored source order. -/
theorem sidecar_tags (next : ℕ) (fs : List Factor) :
    (sidecar next fs).map Prod.fst = fs.filterMap factorTag := by
  induction fs generalizing next with
  | nil => rfl
  | cons f fs ih => cases f <;> simp [sidecar,List.filterMap_cons,factorTag,ih]

/-- The source names actually serialized are those from the original unary entries. -/
theorem positions_labels (next : ℕ) (fs : List Factor) :
    (positions next fs).map (fun p => (p.parameter,p.place)) =
      (fs.filterMap factorTag).map (fun t => (t.base,t.copyStride)) := by
  rw [← sidecar_tags next]
  simp [positions,List.map_map,Function.comp_def]

/-- Word-level scan of the staged site's actual delivered bytes. -/
theorem received_position_words {description w : ℕ} (m : VPVNP.BurstRAM.Memory w)
    (slot H bodyCap orig : ℕ) (fs : List Factor)
    (hbox : (Packet.Source.boxBody (stage orig fs)).length ≤ bodyCap)
    (hsize : H+bodyCap+(TallySidecar.bits H (positions orig fs)).length ≤ description)
    (received : ∀ j : Fin description, (m (slot+j.val)).val =
      (Packet.Source.siteWithTally H bodyCap (stage orig fs) (TallySidecar.bits H (positions orig fs)) j).toNat) :
    DiagonalTallyBits.WordsAt m (slot+H+bodyCap) (TallySidecar.words H (positions orig fs)) :=
  TallySidecar.delivered_words m slot H bodyCap (stage orig fs) (positions orig fs) hbox hsize received

/-- Labels on the abstract local rule, before its incidence lanes are placed. -/
def ruleTag {D : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits} {v : N.Site} :
    Rule N v → Option Port
  | .truth _ => none
  | .unary _ p => some p

/-- Encoding actual fine-site rules at a cell preserves all and only the weighted tags. -/
theorem factorTag_rule {D : ℕ} {P C : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → C) (c : C) {m n : ℕ} (edges : N.Edge ↪ Fin m) (ports : P ↪ Fin n)
    (v : {v : N.Site // cell v = c}) (order : CellBox.Lane N v.val ≃ Fin (Fintype.card (CellBox.Lane N v.val)))
    (r : Rule N v.val) :
    factorTag (ruleFactor N cell c edges ports v order r) = ruleTag r := by cases r <;> rfl

/-- The staged private sidecar of a real grid cell enumerates its actual unary sources
in the original site directory order; ordinary Boolean checks do not add entries. -/
theorem grid_labels {D : ℕ} {P C : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → C) (c : C) {m n s : ℕ} (sites : N.Site ↪ Fin s)
    (edges : N.Edge ↪ Fin m) (ports : P ↪ Fin n) (rules : ∀ v : {v : N.Site // cell v = c}, Rule N v.val)
    (next : ℕ) :
    (positions next (factors N cell c sites edges ports rules)).map (fun p => (p.parameter,p.place)) =
      ((siteList N cell c sites).filterMap (fun v => ruleTag (rules v))).map (fun p => (p.base,p.copyStride)) := by
  rw [positions_labels]
  simp [factors,List.filterMap_map,factorTag_rule]

open VPVNP VPVNP.BooleanTranscript ParseBatch ParseBatchTrees ParseBatchVerifier

/-- A designated source contributes the correct name and place for the *rewired*
physical verifier, independently of the truth table at all ordinary sites. -/
theorem verifier_tag_at {X W J R : Type} [Fintype X] [Fintype W] [Fintype J] [CommSemiring R]
    {s : ℕ} (c : Circuit (X ⊕ W) s) (weighted : J → W) (weight : J → Bool → R)
    (parameter place : J → ℕ) (j : J) :
    ruleTag (verifierRule c weighted weight (fun k => sourceTag (parameter k) (place k))
      (BooleanLayout.weightSite c weighted j)) = some (sourceTag (parameter j) (place j)) := by
  have h : ∃ k, BooleanLayout.weightSite c weighted k = BooleanLayout.weightSite c weighted j := ⟨j,rfl⟩
  have he := (BooleanLayout.weightSite c weighted).injective h.choose_spec
  simp only [verifierRule,dite_eq_left h,ruleTag,he]

/-- An ordinary rewired verifier site never generates a weighted sidecar row. -/
theorem verifier_tag_other {X W J R : Type} [Fintype X] [Fintype W] [Fintype J] [CommSemiring R]
    {s : ℕ} (c : Circuit (X ⊕ W) s) (weighted : J → W) (weight : J → Bool → R)
    (tag : J → Port) (v : (BooleanLayout.layout c weighted).Site)
    (h : ¬ ∃ k, BooleanLayout.weightSite c weighted k = v) :
    ruleTag (verifierRule c weighted weight tag v) = none := by
  simp only [verifierRule,dite_eq_right h,ruleTag]

/-- In the original parse batch, the emitted private metadata uses the actual
grammar parameter of this weighted vertex and the integer index of its exponent bit. -/
theorem query_tag_at {m g n r : ℕ} (d : Fin n) (trees : VerifierNetwork.Frame (BatchPins m g n r d) Unit)
    (code : GrammarLabel (Fin m × Bool) (Fin g) n → ℕ) (j : WeightSites m g r d) :
    ruleTag (queryRule d trees (fun p k => sourceTag (code p) k)
      (BooleanLayout.weightSite (verifier d trees) weightedPin j)) =
      some (sourceTag (code j.1) j.2.val) := by
  have h : ∃ k : WeightSites m g r d, BooleanLayout.weightSite (verifier d trees) weightedPin k =
      BooleanLayout.weightSite (verifier d trees) weightedPin j := ⟨j,rfl⟩
  have he := (BooleanLayout.weightSite (verifier d trees) weightedPin).injective h.choose_spec
  simp only [queryRule,dite_eq_left h,ruleTag,he]

/-- Subdivision preserves each original sidecar tag; intermediate hop checks
never become listed sources. -/
theorem routed_tag {D : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits) (routes : N.WireRoutes)
    (original : ∀ v, Rule N v) (v : (N.subdivide routes).Site) :
    ruleTag (routedRule N routes original v) = v.elim (fun x => ruleTag (original x)) (fun _ => none) := by
  cases v with
  | inl v => cases h : original v <;> simp only [routedRule,h,ruleTag,Sum.elim_inl]
  | inr => rfl

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
