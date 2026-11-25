import OAI.Hierarchy.DescentDatedSeedNodeProgram
import OAI.Hierarchy.DescentDatedVenueFloor
import OAI.Hierarchy.DescentDatedSeedPublicExtras
import OAI.Hierarchy.DescentDatedNodeMetadataSeed
import OAI.Hierarchy.DescentDatedVenueBelow

namespace OAI
/-! # The physically reached original tape including the two permanent node pages -/
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

local notation "chart" => nodeChart l k H g₀
local notation "Q" => nodeArities X publicWide l
local notation "finish" => (chart).seedEnd top

theorem node_price (initialWords : ℕ) (before : initialWords≤l.base)
    (verdictBefore : DescentPackedSeed.rows X S.copies l.seedWidth w+1≤l.base) (active : 0<chunks g₀ l.operandLanes) :
    (initialWords+(clock X l w H g₀ k S.copies+10+(chart).seedTicks)+
      7*DescentStaticWordColumn.names (nodeProgram (A:=A) X digits publicWide l header (w:=w)))*(w+1)
       ≤ 2930*(finish+1)*(w+1) := by
  have old:=public_price (A:=A) X digits publicWide l header (w:=w) initialWords before verdictBefore active
  have price:=(chart).seedPrice top w Q
  have high : top+(chart).names*(chart).rows≤finish:=Nat.le_add_right ..
  have top_le : top ≤ finish := (Nat.le_add_right ..).trans high
  have rows_le : (chart).names*(chart).rows ≤ finish := (Nat.le_add_left ..).trans high
  have original := old.trans (Nat.mul_le_mul_right (w+1)
    (Nat.mul_le_mul_left 2815 (Nat.add_le_add_right top_le 1)))
  have added : ((chart).seedTicks + 7*DescentStaticWordColumn.names
      ((chart).seedProgram top w Q)) * (w+1) ≤ 115*(finish+1)*(w+1) := by
    rw [price]
    exact Nat.mul_le_mul_right _ (by omega)
  unfold nodeProgram
  rw [DescentStaticWordColumn.names_seq]
  nlinarith only [original, added]

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
variable (outer : Catalyst.Port (2^(j+(j+r))*t*p)
    (CorrectionFrame.copiesWidth (2^(j+(j+r))*t) X.width) → Bool)
    (ballot : Candidate (A ⊕ Hidden (ExteriorCount X) j r t) K W q' piece rows → Bool)
local notation "raw" => DescentTerminalFullPins.header X S.copies l.seedWidth w seed lo C grain ss publicRows codes outer ballot
local notation "prior" => Root.countedAt X S.copies l.seedWidth w seed (ballot∘history) raw
local notation "done" => DescentPrivateHeader.initialized header (output X (Equiv.refl _) digits hs l prior)


local notation "final" => (chart).seedImage top Q done

theorem node_start (wideSeed : 2*digitsNeeded l.seedWidth≤w)
    (signedWidth : DescentSignedCableCodec.width 3 256*M≤w) (fieldsFit : l.operandBits*l.operandLanes≤w)
    (seedFits : verdict+(entries+1)<2^w) (seedBefore : verdict+(entries+1)≤lo)
    (privateAfter : origin+17*span j r t E+extra≤header) (early : header<l.base) (space : finish<2^w) :
    (nodeProgram (A:=A) X digits publicWide l header (w:=w)).Exec raw final
      (clock X l w H g₀ k S.copies+10+(chart).seedTicks) ∧ final header=0 ∧
    stageVenue o.source (source_hosts X o wide) (i) M l.fieldBits finish (roster X hs) final ∧
    (∀(f : Fin 2) (x : Block k),Reads ((chart).seedBank top f x) ((chart).seedField Q f) l.operandLanes final) ∧
    (∀a,a<top ∨ finish≤a → final a=done a) := by
  have endBefore : top≤finish := (Nat.le_add_right top _).trans (Nat.le_add_right ..)
  have oldSpace:=endBefore.trans_lt space
  have old:=public_run X digits publicWide l header o wide seed lo C grain ss publicRows codes outer ballot top
    wideSeed signedWidth fieldsFit seedFits seedBefore privateAfter early le_rfl oldSpace
  have second:=(chart).seedIssued top Q done space
  have low:=fences X l H g₀ k
  have baseBefore : l.base≤top:=low.1.trans (low.2.1.trans low.2.2)
  refine ⟨?_,(second.2.1 header (.inl (early.trans_le baseBefore))).trans old.2.1,?_,
    (fun f x=>(chart).seedRead top Q done f x),second.2.1⟩
  · intro P' R' K' machine
    exact Procedure.Exec.then old.1 second.1 machine
  · apply stageVenue_mono o.source (source_hosts X o wide) (i) M l.fieldBits top (roster X hs) final (by
      dsimp [DescentDatedNodeMetadata.Chart.seedEnd]
      omega)
    apply stageVenue_below o.source (source_hosts X o wide) (i) M l.fieldBits top (roster X hs) done final old.2.2.1
    · intro x j
      have wire:=wire_room (H:=H) (G:=g₀) (d:=k) X l top le_rfl oldSpace x.val j.val
      exact (Nat.add_le_add_left wire.2 _).trans wire.1.2.2
    · intro a lt
      exact second.2.1 a (.inl lt)

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
