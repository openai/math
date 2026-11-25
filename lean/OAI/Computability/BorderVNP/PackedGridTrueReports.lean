import OAI.Computability.BorderVNP.PackedGridWitnessAlive
import OAI.Computability.BorderVNP.PackedBottomReportSources

/-! # Recovering the unique live seed reports from the actual physical unary wires -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridBoxes

open Crossing CellSparse BottomReports Diagonal.CellEntries
open scoped Classical
variable {D : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits} (rules : ∀ v, Rule N v)

/-- Read the underlying selected wire at every unary site, before any claims are supplied. -/
def sourceBit : N.Tables Bool := fun v a x => match rules v with
  | .truth _ => false
  | .unary l _ => readLane v a x l

variable {Cell Q : Type} [Fintype Cell] [DecidableEq Cell]
    (cell : N.Site → Cell) (position : Cell → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (hidden : ∀ i, N.InsideAssignment cell i) {src dst : Q → Cell} {H : ℕ}
    (packing : (N.cellNetwork cell position).ChannelPacking src dst H)

/-- A cell's genuine report assignment reads each claimed source name at its
actual physical vertex. Absent source names are assigned false. -/
noncomputable def trueReports (c : Cell) (a : {q : Q // src q = c ∨ dst q = c} → Fin H → Bool)
    (x : ∀ p : {p : P // cell (N.attach p) = c}, Fin (bits p.val) → Bool) (p : Port) : Bool :=
  if hp : ∃ v : {v : N.Site // cell v = c}, ruleTag (rules v.val) = some p then
    cellRead cell position hidden packing (sourceBit rules) c hp.choose a x else false

variable (unique : ∀ v w p, ruleTag (rules v) = some p → ruleTag (rules w) = some p → v = w)
include unique

/-- Each named live factor gets its own actual physical source bit. -/
theorem trueReports_at (c : Cell) (v : {v : N.Site // cell v = c}) (a x p) (hv : ruleTag (rules v.val) = some p) :
    trueReports rules cell position hidden packing c a x p =
      cellRead cell position hidden packing (sourceBit rules) c v a x := by
  have hp : ∃ u : {v : N.Site // cell v = c}, ruleTag (rules u.val) = some p := ⟨v,hv⟩
  have he : hp.choose = v := Subtype.ext (unique _ _ p hp.choose_spec hv)
  rw [trueReports,dite_eq_left hp,he]

/-- The physically recovered report function passes all actual report comparisons
in its cell, even on private assignments that fail ordinary Boolean checks. -/
theorem trueReports_correct (c : Cell) (v : {v : N.Site // cell v = c}) (a x) :
    cellRead cell position hidden packing
      (reportTable rules (trueReports rules cell position hidden packing c a x)) c v a x = true := by
  change (rules v.val).reportOK _ (trueReports rules cell position hidden packing c a x) = true
  cases hv : rules v.val with
  | truth f => rfl
  | unary l p =>
    rw [Rule.reportOK,trueReports_at rules cell position hidden packing unique c v a x p (by rw [hv]; rfl)]
    unfold cellRead fineFactor sourceBit
    rw [hv]
    exact beq_self_eq_true _

/-- Any assignment passing the comparisons agrees with the physically recovered
reports on every genuinely present source label, without a nonzero-tag hypothesis. -/
theorem trueReports_unique (c : Cell) (v : {v : N.Site // cell v = c}) (a x p)
    (hv : ruleTag (rules v.val) = some p) (use : Port → Bool)
    (ok : cellRead cell position hidden packing (reportTable rules use) c v a x = true) :
    use p = trueReports rules cell position hidden packing c a x p := by
  rw [trueReports_at rules cell position hidden packing unique c v a x p hv]
  change (rules v.val).reportOK _ use = true at ok
  cases hr : rules v.val with
  | truth => simp [hr,ruleTag] at hv
  | unary l p' =>
    have he : p' = p := by simpa only [hr,ruleTag,Option.some.injEq] using hv
    subst p
    rw [hr,Rule.reportOK] at ok
    unfold cellRead fineFactor sourceBit
    rw [hr]
    exact (eq_of_beq ok).symm

end Packing.GridBoxes

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse BottomReports GridBoxes Diagonal.CellEntries GridPlacement Cover TeamContraction
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical
variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {Gadget : Type} (report : WeightSites n g r d → Port)

/-- Use the same equality instance as the actual conditioned deck-grid table. -/
noncomputable local instance trueReportDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _

private theorem original_ruleTag {v : (wiredFine G d D W.trees).Site} {p : Port}
    (h : ruleTag (W.originalRule report v) = some p) :
    ∃ j, BooleanLayout.weightSite (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d) j = v ∧ report j = p := by
  unfold originalRule verifierRule at h
  split at h
  · rename_i hj
    exact ⟨hj.choose,hj.choose_spec,Option.some.inj h⟩
  · cases h

/-- The named unary slots of the prewired sparse verifier remain unique after
subdivision, with exactly one physical old vertex per published source name. -/
theorem routed_ruleTag_iff (v : (W.routedFine position).Site) (p : Port) :
    ruleTag (W.routedRules position report v) = some p ↔
      ∃ j, W.routedPowerSite position j = v ∧ report j = p := by
  rw [routedRules,routed_tag]
  rcases v with v | hop
  · constructor
    · intro h
      obtain ⟨j,hv,hp⟩ := W.original_ruleTag report h
      exact ⟨j,congrArg Sum.inl hv,hp⟩
    · rintro ⟨j,hv,rfl⟩
      obtain rfl := Sum.inl.inj hv
      have hn : ∃ k, BooleanLayout.weightSite (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d) k =
          BooleanLayout.weightSite (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d) j := ⟨j,rfl⟩
      have he := (BooleanLayout.weightSite (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d)).injective hn.choose_spec
      simp only [Sum.elim_inl,originalRule,verifierRule,dite_eq_left hn,Rule.inDimension,ruleTag,he]
  · simp [routedPowerSite]

/-- On each hidden and public bit assignment the actual seed's survival is exactly
zero padding and all sparse checks, with the report function computed from its
fine wires and no externally supplied report-correctness hypothesis. -/
theorem seed_alive_trueReports (inject : Function.Injective report) (z : W.Hidden position) (c a x) :
    let uses := trueReports (W.routedRules position report) (cell position W.route) position z
      (routedPacking position W.route (fun _ => le_rfl)) c a x
    W.seedTags (Gadget := Gadget) position z c a x ≠ 0 ↔
      padOK (routedPacking position W.route (fun _ => le_rfl)) c a x ∧
      ∀ v, cellRead (cell position W.route) position z (routedPacking position W.route (fun _ => le_rfl))
        (guard (W.routedRules position report) uses) c v a x = true := by
  intro uses
  apply W.seed_alive_checked position report z uses c a x
  intro v
  apply trueReports_correct
  intro i k p hi hk
  obtain ⟨j,hj,hjp⟩ := (W.routed_ruleTag_iff position report i p).mp hi
  obtain ⟨l,hl,hlp⟩ := (W.routed_ruleTag_iff position report k p).mp hk
  exact hj.symm.trans ((congrArg (W.routedPowerSite position) (inject (hjp.trans hlp.symm))).trans hl)

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
