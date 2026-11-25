import OAI.Hierarchy.DescentNamedOriginalArchive
import OAI.Hierarchy.DescentSeedPrimitiveEncoding

namespace OAI
/-! # The seed primitive dictionary in the original named coordinates -/
namespace Hierarchy.DescentSixParty.SeedNamed.Palette
open DescentCompiler DescentKernelHistory DescentInitialHost DescentPrimitivePalette Chronology Catalyst
noncomputable section
variable {F : Type} [Field F]

/-- Physical names change boundary operands. They leave every original scalar label intact. -/
def transported {P U : Type} {D : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F D P bits}
    {G : PoweredGadget F} {S : AtomSchedule} {k z wire s : ℕ} {q fee : ℝ}
    (raw : Reached W G q fee S k 0 z 3 wire s) (a : Archive W) (same : world raw=W')
    {dict : U→List (List Bool)→F} (old : Encoding U dict a.bit) :
    let named : Archive W':=same ▸ renamedArchive a (site raw) (edge raw)
    Encoding U dict named.bit := by
  cases same
  exact ⟨old.code,old.correct⟩

private structure StoredEncoding where
  destination : Type
  value : destination

open private transportArchive from OAI.Hierarchy.DescentNamedOriginalArchive in
private def storeTransport {P U : Type} {D : ℕ} {bits : P → ℕ} {W W' : MarkedWorld F D P bits}
    {G : PoweredGadget F} {S : AtomSchedule} {k z wire s : ℕ} {q fee : ℝ}
    (raw : Reached W G q fee S k 0 z 3 wire s) (a : Archive W) (same : world raw = W')
    {dict : U → List (List Bool) → F} (old : Encoding U dict a.bit) : StoredEncoding where
  destination := Encoding U dict (transportArchive (renamedArchive a (site raw) (edge raw)) same).data.bit
  value := transported raw a same old

set_option maxHeartbeats 400000 in
private def storedAtOrigin {cp pins : ℕ} {X : Approximation F cp pins} {G : PoweredGadget F} {S : AtomSchedule}
    {q fee : ℝ} {k s z wire p : ℕ}
    {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies≃Fin (S.groupCount 0)×DescentColonies.Block k}
    (o : Origin (G:=G) (q:=q) (fee:=fee) (z:=z) (wire:=wire) X c digits)
    (op : RotorSpec) (menu : Runnable F op) : StoredEncoding :=
  storeTransport (U := Label G s z op) (dict := dictionary G op menu p)
    o.raw (seedArchive X S.copies s c) (linked_world X c digits o.seed)
    (seeded (G := G) (Z := z) (p := p) op menu X c)

def originEncoding {cp pins : ℕ} {X : Approximation F cp pins} {G : PoweredGadget F} {S : AtomSchedule}
    {q fee : ℝ} {k s z wire p : ℕ}
    {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies≃Fin (S.groupCount 0)×DescentColonies.Block k}
    (o : Origin (G:=G) (q:=q) (fee:=fee) (z:=z) (wire:=wire) X c digits)
    (op : RotorSpec) (menu : Runnable F op) : (storedAtOrigin (p := p) o op menu).destination :=
  (storedAtOrigin (p := p) o op menu).value

end
end Hierarchy.DescentSixParty.SeedNamed.Palette

end OAI
