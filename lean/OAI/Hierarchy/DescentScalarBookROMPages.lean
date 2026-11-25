import OAI.Hierarchy.DescentAtomBookCompactor
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! The literal compactor and field insertion pages are shared by all destination books. -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.ROM
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentPackedZip
noncomputable section

/-- Fixed layout for the actual receiver: target test, selected scalar
occupancy, compact move, then one field-insertion page for each local slot. -/
def pairIndex {W : ℕ} (j : Fin (3+W)) (s : Fin 2) :=finProdFinEquiv (j,s)

def receiver {D K cap b n m K' M : ℕ} (i : Fin ((3+DescentPackedActorMask.nodes D K cap)*2)) : Page :=
  let j : Fin (3+DescentPackedActorMask.nodes D K cap) × Fin 2 := finProdFinEquiv.symm i
  (Fin.addCases (motive:=fun _=>Fin 2→Page)
    (fun t : Fin 3=>![binary (DescentPackedActorMask.target n (DescentPackedActorMask.actors D cap)) M,
    binary (DescentPackedActorMask.occupied D K cap m) M,binary (DescentPackedLocalAtoms.pack b (DescentPackedActorMask.nodes D K cap) K') M] t)
    (fun v : Fin (DescentPackedActorMask.nodes D K cap)=>binary (Gather.setField (d:=b) v) M) j.1) j.2

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.ROM

end OAI
