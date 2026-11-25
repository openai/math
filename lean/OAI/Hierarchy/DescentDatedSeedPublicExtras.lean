import OAI.Hierarchy.DescentDatedSeedPublic

namespace OAI
/-! # Allowed startup instructions and original seed words after header clearance -/
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

/-- The original cell-zero count survives the private-header clear. -/
theorem public_count (wideSeed : 2*digitsNeeded l.seedWidth≤w)
    (signedWidth : DescentSignedCableCodec.width 3 256*M≤w) (fieldsFit : l.operandBits*l.operandLanes≤w)
    (seedFits : verdict+(entries+1)<2^w) (seedBefore : verdict+(entries+1)≤lo)
    (privateAfter : origin+17*span j r t E+extra≤header) (early : header<l.base)
    (room : top<2^w) :
    done 0=((S.copies*Fintype.card (Vertex X):ℕ):Word w) := by
  have low : lo≤origin := by
    dsimp only [end_,DescentPackedProfileInstall.dict]
    omega
  have apart : (0:ℕ)≠header := by omega
  rw [DescentPrivateHeader.initialized_frame header _ 0 apart]
  exact source_count X (Equiv.refl _) digits hs l w seed lo C grain ss origin extra
    (DescentExterior.publicRows X outer) (ballot∘history)
    (DescentTerminalPublicIdentity.back (ballot∘chip) w codes publicRows)
    wideSeed signedWidth fieldsFit seedFits seedBefore le_rfl (by omega) room

include o wide in
/-- All seven retained operand columns contain the original packed seed
values after clearing the private header. The statement also covers padded hosts. -/
theorem public_operand (fieldsFit : l.operandBits*l.operandLanes≤w) (early : header<l.base) (room : top<2^w)
    (f : DescentOperandStateBanks.Field) (arg : Fin (3*l.groupsPerNode)) (x : Block k) (r₀ : Row H g₀ l.operandLanes) :
    let loaded : DescentDatedPriorOperand.Layout:=⟨2^k,1,3*l.groupsPerNode,H,g₀,l.operandLanes,l.operandBits-2⟩
    let first:=Seed.Physical.bankStart X (operandBase X l H g₀) k g₀ l.operandLanes
    done ((DescentDatedPriorOperand.previousBank loaded first x (page f arg)).base+(row _ _ _ r₀).val)=
      ((data (Seed.Physical.value X hs (Equiv.refl _) digits l.groupsPerNode l.operandBits 1 arg.val f x) r₀).val:Word w) := by
  intro loaded first
  let a:=(DescentDatedPriorOperand.previousBank loaded first x (page f arg)).base+(row _ _ _ r₀).val
  have baseBound:=(fences X l H g₀ k).1
  have above : header<a := by
    dsimp only [a,first,DescentDatedPriorOperand.previousBank,Seed.Physical.bankStart,Seed.Columns.first,
      Seed.Columns.maskBase,Seed.stampStart]
    omega
  rw [DescentPrivateHeader.initialized_frame header _ a (Nat.ne_of_gt above)]
  exact source_operand X o wide l prior fieldsFit room f arg x r₀

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
