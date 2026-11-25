import OAI.Hierarchy.DescentSeedResidentSigned
import OAI.Hierarchy.DescentSeedInitialCensus

namespace OAI
/-! # All genuine physical source words at the first ordinary date -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSixParty DescentSixParty.SeedNamed DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed
open DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames DescentColonies DescentSIMDLookup DescentPackedColony
open Catalyst ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentSeedInitialTable
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {S : AtomSchedule} {G : PoweredGadget F} {q ε : ℝ}
    {k cp p wire s z H w : ℕ} (X : Approximation F cp p)
    {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k}
    (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z) (wire:=wire) c digits)
    (wide : Fintype.card o.raw.V≤ H) (l : Layout)
local notation "T" => placed o.raw
local notation "g₀" => S.groupCount 0
local notation "hosts" => o.raw.vertex.trans (Fin.castLEEmb wide)
local notation "physicalHosts" => originalHosts X o wide
local notation "sourceOrder" => Function.Embedding.trans (Reached.order (reached o.raw)) Fin.valEmbedding
local notation "i" => operands X l k H g₀
local notation "top" => endAddress X l H g₀ k
local notation "dir" => directoryBase X l H g₀ k
local notation "source" => fun m=>output X (Equiv.refl _) digits physicalHosts l m

/-- The first matcher can issue every source lookup on one genuine native
output, with its original signed, actor, charged and hub data. -/
theorem resident (m : Memory w) (signedWidth : DescentSignedCableCodec.width 3 256*l.packedLanes≤ w)
    (fieldsFit : l.operandBits*l.operandLanes≤ w) (floor : ℕ) (later : top≤ floor) (room : floor<2^w) :
    Accessible ((i).ports 3) (i).actors H g₀ l.packedLanes w floor ∧
    Mounted ((i).ports 3) (roster X physicalHosts) (source m) g₀ l.packedLanes ∧
    Reads (i).actors (Prepare.actors T (Function.Embedding.refl _) hosts) l.packedLanes (source m) ∧
    (∀(x : Block k) (j : Fin (2*(T).cap)), Reads ((i).wire x.val j.val) (fun h g=>
      DescentSignedCableCodec.encode (Prepare.signed T sourceOrder S (reached o.raw).valid
        (Function.Embedding.refl _) hosts x j h g)) l.packedLanes (source m)) ∧
    (i).hubs.Fits w floor ∧ H≤(i).hubs.size ∧
    (∀h : Fin H,source m ((i).hubs.base+h.val)=((Census.hub T hosts h).val:Word w)) ∧
    (∀x,((i).atoms x).Fits w floor) ∧
    (∀x : Block k,DescentPackedZip.Source ((i).atoms x.val)
      (fun h g=>Census.count T (Equiv.refl _) hosts l.fieldBits h g x) l.packedLanes (source m)) := by
  have census:=DescentSeedInitialTable.node_inputs X o wide (M:=l.packedLanes) dir l.wire l.history l.seedWidth
    l.fieldBits (operandMem X (Equiv.refl _) digits physicalHosts l m)
  have shape:=static_census X (Equiv.refl _) digits physicalHosts l m floor later room
  refine ⟨initial_access X l floor later room,initial_mounted X (Equiv.refl _) digits physicalHosts l m,
    census.1,DescentSeedInitialTable.signed_on_final X o wide l m signedWidth fieldsFit (later.trans_lt room),
    shape.1,shape.2.1,census.2.1,shape.2.2.1,?_⟩
  intro x
  exact DescentPackedZip.source_column (DescentSeedInitialTable.bank dir H g₀ l.packedLanes 3 5) floor
    (shape.2.2.1 x.val).1 _ _ (DescentSeedInitialTable.capacities H g₀ l.packedLanes 3).2.2 (census.2.2 x)

end
end Hierarchy.DescentDatedSeedStartup

end OAI
