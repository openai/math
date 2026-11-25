import OAI.Hierarchy.DescentDatedSeedPublicCode
import OAI.Hierarchy.DescentDatedSeedBooted
import OAI.Hierarchy.DescentDatedSeedBootTariff
import OAI.Hierarchy.DescentTerminalFullPins
import OAI.Hierarchy.DescentPrivateHeaderCheap

namespace OAI
/-! # One native startup across every proposal in the original candidate alphabet -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentSixParty DescentSixParty.SeedNamed DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed
open DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall
open DescentColonies DescentSIMDLookup DescentPackedColony DescentOperandStateBanks DescentSeedInitialTable
open DescentExteriorShelf DescentExterior DescentTerminalFullPins Computability.BorderVNP.Crossing
open ThreeFlat Routing CorrectionBatch DescentGL DescentTerminalChipPins DescentTerminalPorts
open Catalyst ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.Diagonal
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F A : Type} [Field F] {S : AtomSchedule} {G : PoweredGadget F} {q ε : ℝ}
    {k cp p wire s z₀ H w j r t K W q' piece rows : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k) (publicWide : Fintype.card (Vertex X)≤H)
    (l : Layout) (header : ℕ)
local notation "g₀" => S.groupCount 0
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "i" => operands X l k H g₀
local notation "top" => endAddress X l H g₀ k
local notation "M" => l.packedLanes

theorem public_price (initialWords : ℕ) (initialBefore : initialWords≤l.base)
    (verdictBefore : DescentPackedSeed.rows X S.copies l.seedWidth w+1≤l.base) (active : 0<chunks g₀ l.operandLanes) :
    (initialWords+(clock X l w H g₀ k S.copies+10)+
      7*DescentStaticWordColumn.names (publicProgram (A:=A) X digits publicWide l header (w:=w)))*(w+1)
       ≤ 2815*(top+1)*(w+1) := by
  have old:=physical_bound (A:=A) X (Equiv.refl _) digits hs l w initialWords initialBefore verdictBefore active
  have names : DescentStaticWordColumn.names (DescentPrivateHeader.clearHeader w header)=15 := by
    change DescentStaticWordColumn.names (ProtocolRAM.scan w header 1 (.lit 0))=15
    rw [DescentStaticWordColumn.names_scan]
    rfl
  unfold publicProgram
  rw [DescentStaticWordColumn.names_seq,names]
  nlinarith [Nat.zero_le ((w+1)*top)]

variable {c : (initialGroup X S.copies s).Choice}
    (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z₀) (wire:=wire) c digits)
    (wide : Fintype.card o.raw.V≤H)
    (seed : Select X S.copies l.seedWidth → A) (lo C grain : ℕ) (ss : List (Source A))
    (publicRows codes : ℕ)
local notation "E" => ExteriorCount X
local notation "origin" => end_ (lo+extent grain ss) C grain
local notation "extra" => DescentTerminalPublicIdentity.total K W q' piece codes rows publicRows
local notation "verdict" => DescentTerminalPackedSeedFlags.endInput X S.copies l.seedWidth w ([] : List (Source A))
local notation "entries" => DescentPackedSeed.rows X S.copies l.seedWidth w
variable (outer : Catalyst.Port ((2^(j+(j+r))*t)*p)
      (CorrectionFrame.copiesWidth (2^(j+(j+r))*t) X.width) → Bool)
    (ballot : Candidate (A ⊕ Hidden (ExteriorCount X) j r t) K W q' piece rows → Bool) (floor : ℕ)
local notation "raw" => DescentTerminalFullPins.header X S.copies l.seedWidth w seed lo C grain ss publicRows codes outer ballot
local notation "prior" => Root.countedAt X S.copies l.seedWidth w seed (ballot∘history) raw
local notation "done" => DescentPrivateHeader.initialized header (output X (Equiv.refl _) digits hs l prior)

/-- The directory and program are fixed by the public original graph, width, and padding.
A reached-world witness is used only to specify what the same computed words mean. -/
theorem public_run (wideSeed : 2*digitsNeeded l.seedWidth≤w)
    (signedWidth : DescentSignedCableCodec.width 3 256*M≤w) (fieldsFit : l.operandBits*l.operandLanes≤w)
    (seedFits : verdict+(entries+1)<2^w) (seedBefore : verdict+(entries+1)≤lo)
    (privateAfter : origin+17*span j r t E+extra≤header) (early : header<l.base)
    (later : top≤floor) (room : floor<2^w) :
    (publicProgram (A:=A) X digits publicWide l header (w:=w)).Exec raw done
      (clock X l w H g₀ k S.copies+10) ∧ done header=0 ∧
    stageVenue o.source (source_hosts X o wide) (i) M l.fieldBits floor (roster X hs) done ∧
    (done (verdict+entries)=0 ↔ DescentSeedRoot.valid X (((ballot∘history)∘Sum.inl)∘seed)) ∧
    Loaded origin (fun _=>LinearEquiv.refl _ _) (DescentExterior.publicRows X outer) ((ballot∘history)∘Sum.inr) done ∧
    (∀a,a≠header → a<verdict ∨ verdict+(entries+1)≤a → a<l.base ∨ top≤a → done a=raw a) :=
  initialized_run X o wide l seed lo C grain ss origin extra (DescentExterior.publicRows X outer) (ballot∘history)
    (DescentTerminalPublicIdentity.back (ballot∘chip) w codes publicRows) header floor wideSeed signedWidth
    fieldsFit seedFits seedBefore le_rfl privateAfter early later room

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
