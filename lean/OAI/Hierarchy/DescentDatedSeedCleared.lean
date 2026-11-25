import OAI.Hierarchy.DescentDatedSeedOrigin
import OAI.Hierarchy.DescentDatedVenueFrame
import OAI.Hierarchy.DescentPrivateHeader

namespace OAI
/-! # First-date sources after the actual ten-instruction private-counter clear -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSixParty DescentSixParty.SeedNamed DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed
open DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames DescentColonies DescentSIMDLookup DescentPackedColony
open Catalyst ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentSeedInitialTable
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {S : AtomSchedule} {G : PoweredGadget F} {q ε : ℝ}
    {k cp p wire s z H w : ℕ} (X : Approximation F cp p)
    {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k}
    (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z) (wire:=wire) c digits)
    (wide : Fintype.card o.raw.V≤H) (l : Layout)
local notation "g₀" => S.groupCount 0
local notation "M" => l.packedLanes
local notation "hs" => originalHosts X o wide
local notation "i" => operands X l k H g₀
local notation "top" => endAddress X l H g₀ k
local notation "src" => fun m=>output X (Equiv.refl _) digits hs l m

omit [Field F] in
theorem venue_lower (H G d : ℕ) : VenueFrom (operands X l d H G) 3 l.base := by
  have fs:=fences X l H G d
  have dir : l.base≤directoryBase X l H G d := fs.1.trans fs.2.1
  have table (n : ℕ) : l.base≤(DescentSeedInitialTable.bank (directoryBase X l H G d) H G M 3 n).base :=
    dir.trans (Nat.le_add_right ..)
  refine ⟨fun j=>table (8+j.val),table 0,table 1,table 2,table 3,?_,table 4,?_⟩
  · intro x j
    change l.base≤l.base+_+_
    omega
  · intro x
    exact ⟨table 5,trivial⟩

theorem source_after_clear (m : Memory w) (signedWidth : DescentSignedCableCodec.width 3 256*M≤w)
    (fieldsFit : l.operandBits*l.operandLanes≤w) (floor : ℕ) (later : top≤floor) (room : floor<2^w)
    (header : ℕ) (early : header<l.base) :
    let current:=src m
    let initial:=DescentPrivateHeader.initialized header current
    (DescentPrivateHeader.clearHeader w header).Exec current initial 10 ∧ initial header=0 ∧
    stageVenue o.source (source_hosts X o wide) (i) M l.fieldBits floor (roster X hs) initial ∧
    (∀a,l.base≤a→initial a=current a) := by
  intro current initial
  have below:=fences X l H g₀ k
  have cap:=below.1.trans (below.2.1.trans (below.2.2.trans later))
  have extent : header+1<2^w:=by omega
  have keep (a) (high : l.base≤a) : initial a=current a :=
    DescentPrivateHeader.initialized_frame header current a (by omega)
  exact ⟨DescentPrivateHeader.initialize_run header current extent,
    DescentPrivateHeader.initialized_read header current,
    stageVenue_frame o.source (source_hosts X o wide) (i) M l.fieldBits floor l.base
      (roster X hs) current initial (source_resident X o wide l m signedWidth fieldsFit floor later room)
      (venue_lower X l H g₀ k) keep,keep⟩

end
end Hierarchy.DescentDatedSeedStartup

end OAI
