import OAI.Hierarchy.DescentSeedOriginCapacity
import OAI.Hierarchy.DescentDatedStageVenue
import OAI.Hierarchy.DescentDatedSeedResident

namespace OAI
/-! # Native zero-date input after identifying the original named world -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSixParty DescentSixParty.SeedNamed DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed
open DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames DescentColonies DescentSIMDLookup DescentPackedColony
open Catalyst ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentSeedInitialTable DescentOperandStateBanks
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {S : AtomSchedule} {G : PoweredGadget F} {q ε : ℝ}
    {k z wire s H w : ℕ}


private theorem transportVenue {P : Type} {d : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F d P bits}
    (prior : Reached W G q ε S k 0 z 3 wire s) (eqn : world prior=W')
    (room : @Fintype.card prior.V prior.finite ≤ H)
    (after : @Fintype.card (SeedNamed.transport prior eqn).V (SeedNamed.transport prior eqn).finite ≤ H)
    (io : Dated.Operands) (lanes countBits roof : ℕ) (rs : Fin H→Fin 3→Option (Fin H)) (m : Memory w)
    (before : stageVenue (reached prior) room io lanes countBits roof rs m) :
    stageVenue (SeedNamed.transport prior eqn) after io lanes countBits roof rs m := by
  cases eqn
  exact before

variable {cp p : ℕ} (X : Approximation F cp p)
    {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k}
    (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z) (wire:=wire) c digits)
    (wide : @Fintype.card o.raw.V o.raw.finite ≤ H) (l : Layout)
local notation "g₀" => S.groupCount 0
local notation "M" => l.packedLanes
local notation "hs" => originalHosts X o wide
local notation "i" => operands X l k H g₀
local notation "top" => endAddress X l H g₀ k
local notation "m₁" => fun m=>output X (Equiv.refl _) digits hs l m

set_option maxHeartbeats 600000 in
/-- The actual original branch start consumes the populated matcher banks,
without a fresh operand table or any hypothesis on an arbitrary reindexing. -/
theorem source_resident (m : Memory w) (signedWidth : DescentSignedCableCodec.width 3 256*M≤w)
    (fieldsFit : l.operandBits*l.operandLanes≤w) (floor : ℕ) (later : top≤floor) (room : floor<2^w) :
    AtVenue (W:=initial_world X S.copies s (S.groupCount 0) k digits c) (G:=G) (S:=S)
      (q:=q) (ε:=ε) (k:=k) (z:=z) (wire:=wire) (s:=s) (H:=H) (w:=w)
      o.source (source_hosts X o wide) (i) M l.fieldBits floor (roster X hs) (m₁ m) := by
  have before : stageVenue (reached o.raw) wide (i) M l.fieldBits floor (roster X hs) (m₁ m) := by
    unfold stageVenue
    exact resident X o wide l m signedWidth fieldsFit floor later room
  unfold Origin.source
  exact transportVenue (W:=(initialGroup X S.copies s).state c)
    (W':=initial_world X S.copies s (S.groupCount 0) k digits c) (G:=G) (S:=S)
    (q:=q) (ε:=ε) (k:=k) (z:=z) (wire:=wire) (s:=s) (H:=H) (w:=w)
    o.raw (linked_world X c digits o.seed) wide (source_hosts X o wide) (i) M l.fieldBits floor
    (roster X hs) (m₁ m) before

theorem source_operand (m : Memory w) (fieldsFit : l.operandBits*l.operandLanes≤w) (room : top<2^w)
    (f : DescentOperandStateBanks.Field) (arg : Fin (3*l.groupsPerNode)) (x : Block k) (r : Row H g₀ l.operandLanes) :
    let loaded : DescentDatedPriorOperand.Layout:=⟨2^k,1,3*l.groupsPerNode,H,g₀,l.operandLanes,l.operandBits-2⟩
    let first:=Seed.Physical.bankStart X (operandBase X l H g₀) k g₀ l.operandLanes
    m₁ m ((DescentDatedPriorOperand.previousBank loaded first x (page f arg)).base+(row _ _ _ r).val)=
      ((data (Seed.Physical.value X hs (Equiv.refl _) digits l.groupsPerNode l.operandBits 1 arg.val f x) r).val:Word w) :=
  operand_read X (Equiv.refl _) digits hs l m fieldsFit room f arg x r

end
end Hierarchy.DescentDatedSeedStartup

end OAI
