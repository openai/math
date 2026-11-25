import OAI.Computability.BorderVNP.DiagonalSignedSeedSchedule
import OAI.Computability.BorderVNP.DiagonalEnrichedSiteWiring

/-! # The signed query network before the actual later literals and field advice -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing Packing Packing.DeckGrid Cover TeamScales TeamContraction ProcessorSlots
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar MvPolynomial
open RoutingISA RoutingISA.Evaluator CellEntries PackedHistoryCircuit.Normalized
open FieldProcessor (Scale freeWidth)
open scoped BigOperators Classical

/-- A single named verifier reads all later literal data of this native site
table on its original registered interior and exterior wiring. -/
def PrewiredSignedQuery {pc : ℕ} (D k size R r w ec a pins link axes depth : ℕ)
    (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc 64 32 8)
    (fit : fitsWith physical 64 32 r w a R link (k+1) ec)
    (order : Fin (Fintype.card (Fin axes → Deck (depth+2))) ≃ (Fin axes → Deck (depth+2))) : Prop :=
    ∃ witness : WiredWitness
      (tapeTemplate (R := R) (r := r) (link := link) (k := k) (regs := 64) (w := w) (e := ec) (width := w+1)
        (a := setupWidth (w+1) (k+1)+(prefixCapacity r 32 64 w (k+1)+1+a)) physical fit pins)
      (Fin.last k) D axes depth order (0 : ParseTable.State (Fin (k+1) × Bool) size),
    ∀ (position : (Fin axes → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
      (L Gadget : Type) [CommRing L] (values : Gadget → L)
      (data : SiteData R r 64 32 w a) (team : Fin (R+1)) (pin : Fin pins → Bool)
      (ext : Exterior R r link → Bool),
      let installed := wiringWith physical P data pins link (k+1) ec fit
      (∑ z : witness.Hidden position, (witness.seedGrid position).value
        (fun v wires x => interpret values (witness.seedTags position z v wires x))
        (fun t _ => publicBits installed team pin ext t)) =
      MvPolynomial.map (Int.castRingHom L) (∑ int : Wires.Edge r 64 w ec (w+1) → Bool,
        ∏ t, labelQuery (Fin.last k) (0 : ParseTable.State (Fin (k+1) × Bool) size) (installed.word pin ext int team t))

set_option maxHeartbeats 1400000 in
/-- Polynomially many requested coefficient slots can be wired before
any literal or pin choice on this actual program. -/
theorem prewiredSignedQuery {pc : ℕ} (D k size R r w ec a pins link axes depth : ℕ)
    (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc 64 32 8)
    (fit : fitsWith physical 64 32 r w a R link (k+1) ec)
    (order : Fin (Fintype.card (Fin axes → Deck (depth+2))) ≃ (Fin axes → Deck (depth+2)))
    (hr : (k+1+size+2)^24 ≤ r) : PrewiredSignedQuery D k size R r w ec a pins link axes depth physical P fit order := by
  obtain ⟨witness⟩ := exists_tapeWitness (R := R) (r := r) (link := link) (k := k)
    (regs := 64) (w := w) (e := ec) (width := w+1) (D := D) (pins := pins)
    (a := setupWidth (w+1) (k+1)+(prefixCapacity r 32 64 w (k+1)+1+a)) physical fit order size hr
  refine ⟨witness,?_⟩
  intro position L Gadget _ values data team pin ext
  exact WiredWitness.tape_seed_value (D := D) (q := axes) (depth := depth) (R := R) (r := r)
    (pins := pins) (link := link) (k := k) (regs := 64) (w := w) (e := ec) (width := w+1)
    (a := setupWidth (w+1) (k+1)+(prefixCapacity r 32 64 w (k+1)+1+a))
    (order := order) (s := size) (Gadget := Gadget) (E := L)
    physical fit witness position values (data.enrichedFree physical P (k+1) ec link) team pin ext

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {G : PaidIdentity F D m}
    (cube : FixedCube K) {S : SiteSchedule G} {extra E d Q A B j : ℕ}
    {scales : EpochScales S (cube.pred+1) extra} (b : JointSchedule scales (E+1) d Q A B j)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1400000 in
/-- Choose the named private verifier for the actual signed table, sorter and
selected team geometry before the field-specific reader packet, the machine's
literal contents, or either pin is known. All those later choices use its
original site names, routed fine assignments and degree-component query. -/
theorem LengthBudget.fixed_signed_query {cut k : ℕ} (bound : LengthBudget b cut (k+1))
    (axes depth pins : ℕ) (order : Fin (Fintype.card (Fin axes → Deck (depth+2))) ≃ (Fin axes → Deck (depth+2))) :
    let n := k+1
    let r := stretch b.ρ n
    let size := stretch b.σ n
    let R := b.physical.teamsPred n
    let w := b.physical.word n
    let ξ := (scales.τ:ℝ)/5
    let link := TeamScales.link ξ (R+1) n
    let ec := Wires.sortExponent (block ξ n)
    let eval := signedBody (cube.cubeID G)
    let P := (withStartup eval).program
    let physical := cube.signedSiteProgram G
    let a := freeWidth physical scales.α 32 64 r w n
    ∀ geo : Scale physical ((withStartup eval).slots+1) 64 32 scales.α ξ r n R w ec,
    PrewiredSignedQuery D k size R r w ec a pins link axes depth physical P geo.fits order := by
  intro n r size R w ξ link ec eval P physical a geo
  exact prewiredSignedQuery D k size R r w ec a pins link axes depth physical P geo.fits order bound.replication

end Diagonal

end BorderVNP
end Computability
end OAI
