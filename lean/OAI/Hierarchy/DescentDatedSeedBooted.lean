import OAI.Hierarchy.DescentDatedSeedCleared
import OAI.Hierarchy.DescentDatedSeedInput

namespace OAI
/-! # Date-zero execution on the original extended bit tape -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentSixParty DescentSixParty.SeedNamed DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed
open DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall
open DescentPacking.PackedMatch.Local.Stage DescentColonies DescentSIMDLookup DescentPackedColony DescentSharedCableNames
open DescentExteriorShelf DescentExterior DescentSeedInitialTable Computability.BorderVNP.Crossing
open Catalyst ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.Diagonal
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {S : AtomSchedule} {G : PoweredGadget F} {q ε : ℝ}
    {k cp p wire s z₀ H w e j r t : ℕ} (X : Approximation F cp p)
    {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k}
    (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z₀) (wire:=wire) c digits)
    (wide : Fintype.card o.raw.V≤H) (l : Layout)
variable (seed : Select X S.copies l.seedWidth → P) (lo C grain : ℕ) (ss : List (Source P))
    (origin extra : ℕ) (x : Fin e → Plane j r → Fin t → Bool) (z : P⊕Hidden e j r t → Bool)
    (back : Memory w) (header floor : ℕ)
local notation "g₀" => S.groupCount 0
local notation "M" => l.packedLanes
local notation "hs" => originalHosts X o wide
local notation "i" => operands X l k H g₀
local notation "top" => endAddress X l H g₀ k
local notation "frontSize" => origin+17*span j r t e
local notation "raw" => Root.appended frontSize extra
  (Root.packedImage X S.copies l.seedWidth w seed lo C grain ss origin x z) back
local notation "counted" => Root.countedAt X S.copies l.seedWidth w seed z raw
local notation "middle" => output X (Equiv.refl _) digits hs l counted
local notation "done" => DescentPrivateHeader.initialized header middle
local notation "first" => program (A:=P) X (Equiv.refl _) digits hs l w
local notation "verdict" => DescentTerminalPackedSeedFlags.endInput X S.copies l.seedWidth w ([] : List (Source P))
local notation "entries" => DescentPackedSeed.rows X S.copies l.seedWidth w

theorem initialized_run (wideSeed : 2*digitsNeeded l.seedWidth≤w)
    (signedWidth : DescentSignedCableCodec.width 3 256*M≤w) (fieldsFit : l.operandBits*l.operandLanes≤w)
    (seedFits : verdict+(entries+1)<2^w) (seedBefore : verdict+(entries+1)≤lo)
    (shelves : end_ (lo+extent grain ss) C grain≤origin) (privateAfter : frontSize+extra≤header)
    (early : header<l.base) (later : top≤floor) (room : floor<2^w) :
    ((first).seq (DescentPrivateHeader.clearHeader w header)).Exec raw done
      (clock X l w H g₀ k S.copies+10) ∧ done header=0 ∧
    stageVenue o.source (source_hosts X o wide) (i) M l.fieldBits floor (roster X hs) done ∧
    (done (verdict+entries)=0 ↔ DescentSeedRoot.valid X ((z∘Sum.inl)∘seed)) ∧
    Loaded origin (fun _=>LinearEquiv.refl _ _) x (z∘Sum.inr) done ∧
    (∀a,a≠header → a<verdict ∨ verdict+(entries+1)≤a →
      a<l.base ∨ top≤a → done a=raw a) := by
  let before:=run X (Equiv.refl _) digits hs l w seed lo C grain ss origin extra x z back
    wideSeed signedWidth fieldsFit seedFits seedBefore shelves (by omega) (later.trans_lt room)
  let clear:=source_after_clear X o wide l counted signedWidth fieldsFit floor later room header early
  have low : lo≤end_ (lo+extent grain ss) C grain := by
    dsimp only [end_,DescentPackedProfileInstall.dict]
    omega
  refine ⟨?_,clear.2.1,clear.2.2.1,?_,?_,?_⟩
  · intro P' R' K' machine
    exact Procedure.Exec.then before.1 clear.1 machine
  · rw [DescentPrivateHeader.initialized_frame header middle _ (by omega)]
    exact before.2.2.1
  · intro col idx live
    have ord:=col.isLt
    have add:=Nat.mul_le_mul_right (span j r t e) (show col.val+1≤17 by omega)
    rw [Nat.succ_mul] at add
    change done (origin+col.val*span j r t e+idx)=_
    rw [DescentPrivateHeader.initialized_frame header middle _ (by omega)]
    exact before.2.2.2.1 col idx live
  · intro a apart old outside
    exact (DescentPrivateHeader.initialized_frame header middle a apart).trans
      (before.2.2.2.2 a old outside)

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
