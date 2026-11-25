import OAI.Computability.BorderVNP.DiagonalNativeTimedArenaChecks
import OAI.Computability.BorderVNP.DiagonalNativeSiteMacro
import OAI.Computability.BorderVNP.CellSparseExteriorDriver
import OAI.Computability.BorderVNP.DiagonalNativeSignedTags

/-! # The single signed site table for a fixed shortening and prime-field cube -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open VPVNP BurstRAM Branch Crossing TeamScales TeamContraction TeamContraction.ProcessorSlots
open RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine TeamSite Filter _root_.OAI.Computability.BorderVNP.Cube
open FieldProcessor (Scale freeWidth)
open scoped Classical BigOperators

variable {D m : ℕ} {F K : Type*} [Field F] [Field K] (G : PaidIdentity F D m) (cube : FixedCube K)

local notation "entries" => TableEntry cube.pred cube.b cube.h cube.copies cube.width

/-- Number each scalar position in the shared reader's own coordinate order. -/
noncomputable def FixedCube.scalarNumber : G.Entry ⊕ entries ↪ ℕ :=
  (Fintype.equivFin (G.Entry ⊕ entries)).toEmbedding.trans Fin.valEmbedding

/-- Literal table of cube scalar IDs used by the native packet and tally operations. -/
noncomputable def FixedCube.cubeID (v : entries) : ℕ := cube.scalarNumber G (Sum.inr v)

/-- Original shortening and cube entries always address separate scalar words,
including when their field values are equal or vanish. -/
theorem FixedCube.paid_ne_cube (i : G.Entry) (v : entries) :
    cube.scalarNumber G (.inl i) ≠ cube.cubeID G v := by
  intro h
  have eq := (cube.scalarNumber G).injective h
  cases eq

/-- The universal machine's actual finite program. Its only private routine
restores the occupied external spans, translates the original directory and
executes its checks. Its physical timer covers every malformed input too.
This table is fixed before the length, possible border circuit, or field chart. -/
noncomputable def FixedCube.signedSiteProgram : UniversalMachine.Program :=
  TimedProcessor.machine (signedProgram (cube.cubeID G)).program
    (siteLibrary SparseExterior.driver) (fun _ => some false)

/-- Joint startup, address and exterior-rejection checks on a single length
for the actual sparse signed site program. -/
def SignedSitesAt [NeZero D]
    {S : PackedHistoryCircuit.Normalized.SiteSchedule G} {extra E d Q A B j : ℕ}
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule s (E+1) d Q A B j)
    (φ : K →+* F) (q : ℕ) (f : ℕ → ℕ) (c k n : ℕ) : Prop :=
    let eval := signedBody (cube.cubeID G)
    let lib := siteLibrary SparseExterior.driver
    let mark : Fin 8 → Option Bool := fun _ => some false
    let physical := cube.signedSiteProgram G
    let ξ := (s.τ:ℝ)/5
    let r := stretch b.ρ n
    let H := b.physical
    let W := H.word n
    let R := H.teamsPred n
    let T := f (adviceScale b.σ b.ρ n)
    let e := Wires.sortExponent (block ξ n)
    ∃ geo : Scale physical ((withStartup eval).slots+1) 64 32 s.α ξ r n R W e,
    ∀ {l size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
      {common : CommonField G (φ ∘ cube.table) q l size ord} (chart : AdvisedBranch common)
      [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
      (reader : ChosenReader chart (R+1) r (H.multBits n) (H.tally n) W (T+6)),
      reader.charge ≤ c*(T+1)^k → ∀ (L : Routing.WireLayout (R+1) r (H.link n)), 0 < L.header →
      let free := freeWidth physical s.α 32 64 r W n
      let arena := programArena physical R r W n free (link ξ (R+1) n) L.header reader.packetBitCount
      ∀ (valuation entry totals : Fin (R+1) → ℕ) (extension : Fin (R+1) → Fin 81 → Word W),
        let pack := fun u => reader.packetAt (ReaderPlacement.inArena arena (valuation u) (entry u) (totals u) (extension u))
        AllocatedPacketModes eval lib mark geo L.header reader.packetBitCount pack ∧
        AllocatedPacketReady eval lib mark geo L.header reader.packetBitCount pack ∧
        AllocatedPacketRejects eval lib mark geo L.header reader.packetBitCount pack

set_option maxRecDepth 4500 in
/-- All sufficiently large lengths simultaneously support the genuine fixed
signed program, sparse private library and both checked startup modes.
The uniform cutoff precedes the common advice field and every later reader. -/
theorem JointSchedule.eventually_fixed_signed_sites [NeZero D]
    {S : PackedHistoryCircuit.Normalized.SiteSchedule G} {extra E d Q A B j : ℕ}
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule s (E+1) d Q A B j)
    (φ : K →+* F) (q : ℕ) (f : ℕ → ℕ) (hf : PolynomiallyBounded f) (c k : ℕ) :
    ∀ᶠ t : ℕ in atTop, SignedSitesAt G cube b φ q f c k (t+1) := by
  exact b.eventually_chosen_packet_checks (G := G) (aux := φ ∘ cube.table) (q := q) f hf c k
    (signedBody (cube.cubeID G)) (signedBody_withoutAccept _) (siteLibrary SparseExterior.driver)
    (fun _ => some false) (fun _ => (by decide : (none : Option Bool) ≠ some false))

end Diagonal

end BorderVNP
end Computability
end OAI
