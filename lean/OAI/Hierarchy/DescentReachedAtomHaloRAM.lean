import OAI.Hierarchy.DescentAtomBookCompactor
import OAI.Hierarchy.DescentHaloWalkRAM
import OAI.Hierarchy.DescentSortedRoster

namespace OAI
/-! # Compact the scalar fields fetched through the actual sorted donor ports -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M a w D k K cap n mb : ℕ}
local notation "P" => breadth D
local notation "donors" => (breadth D*2^k)
local notation "actors" => DescentPackedActorMask.actors donors cap
local notation "nodes" => DescentPackedActorMask.nodes donors K cap

def bookRoot (D k K cap : ℕ) (j : Fin (DescentPackedActorMask.nodes (breadth D*2^k) K cap)) : Fin (breadth D) :=
  (finProdFinEquiv.symm (finProdFinEquiv.symm j : Fin (breadth D*2^k)×Fin (K+cap*6)).1).1

def bookBlock (D k K cap : ℕ) (j : Fin (DescentPackedActorMask.nodes (breadth D*2^k) K cap)) : Fin (2^k) :=
  (finProdFinEquiv.symm (finProdFinEquiv.symm j : Fin (breadth D*2^k)×Fin (K+cap*6)).1).2

def bookItem (D k K cap : ℕ) (j : Fin (DescentPackedActorMask.nodes (breadth D*2^k) K cap)) : Fin (K+cap*6) :=(finProdFinEquiv.symm j).2

/-- Each source-rack buffer is a genuine previously published old field or
newborn field at one old block and local ordinal. Query and count arrays
live at the receiver. All donor banks go through the physical halo. -/
theorem run_halo (T : TablesAt) (gates : Fin nodes→Tables) (ports : Ports P) (bank : Fin (2^k)→Fin (K+cap*6)→Bank)
    (want addr counts : Expr) (out K' : ℕ) (m : Memory w) (walks : Fin H→Fin P→Option (Fin H))
    (wired : Mounted ports (DescentSortedRoster.indexed walks) m G M)
    (access : ∀b t,Accessible ports (bank b t) H G M w out)
    (old : Fin (2^k)→Fin (K+cap*6)→Fin H→Fin G→Cell a) (published : ∀b t,Reads (bank b t) (old b t) M m)
    (wanted : Fin H→Fin G→Cell n) (address : Fin H→Fin G→Fin actors→Cell n) (count : Fin H→Fin G→Fin donors→Cell mb)
    (wants : Source want wanted M m) (locations : Source addr (fun h g=>encode n actors (address h g)) M m)
    (tallies : Source counts (fun h g=>encode mb donors (count h g)) M m)
    (targetRoom : DescentPackedZip.Fits T.targets want addr n (n*actors) M out w)
    (actorRoom : DescentPackedZip.Fits T.actors (T.targets.read want addr) counts (1*actors) (mb*donors) M out w)
    (fieldRoom : Gather.Bounds (w:=w) (d:=a) (M:=M) gates (fun j=>peerExpr ports (bank (bookBlock D k K cap j) (bookItem D k K cap j)) H (bookRoot D k K cap j)) out)
    (resultRoom : DescentPackedZip.Fits T.emitted (masked T want addr counts) (Gather.assembly gates (fun j=>peerExpr ports (bank (bookBlock D k K cap j) (bookItem D k K cap j)) H (bookRoot D k K cap j))) (1*nodes) (a*nodes) M out w)
    (room : out+H*chunks G M<2^w) (targetROM : Static T.targets (DescentPackedActorMask.target n actors) M m)
    (actorROM : Static T.actors (DescentPackedActorMask.occupied donors K cap mb) M m) (fieldROM : ∀j,Static (gates j) (Gather.setField (d:=a) j) M m)
    (resultROM : Static T.emitted (DescentPackedLocalAtoms.pack a nodes K') M m) :
    let src:=fun j=>peerExpr ports (bank (bookBlock D k K cap j) (bookItem D k K cap j)) H (bookRoot D k K cap j)
    let e:=resultExpr T gates src want addr counts;let state:=image out (H*chunks G M) e m
    let mask:=fun h g=>DescentPackedActorMask.occupied donors K cap mb (DescentPackedActorMask.target n actors (wanted h g) (encode n actors (address h g))) (encode mb donors (count h g))
    let field:=fun h g j=>(DescentSortedRoster.indexed walks h (bookRoot D k K cap j)).elim 0 (fun v=>old (bookBlock D k K cap j) (bookItem D k K cap j) v g)
    (scan w out (H*chunks G M) e).Exec m state (4+(H*chunks G M)*(2*e.work+4)) ∧
      (∀p : Row H G M,state (out+(row H G M p).val)=((data (fun h g=>DescentPackedLocalAtoms.pack a nodes K' (mask h g) (encode a nodes (field h g))) p).val:Word w)) ∧ CheapCode (scan w out (H*chunks G M) e) :=by
  intro src e state mask field
  apply run T gates src want addr counts out K' m targetRoom actorRoom fieldRoom resultRoom room targetROM actorROM fieldROM resultROM wanted address count field wants locations tallies
  intro j
  exact peerSource ports (bank (bookBlock D k K cap j) (bookItem D k K cap j)) out (access _ _) _ m wired _ (published _ _) (bookRoot D k K cap j)

end
end Hierarchy.DescentOrdinaryAtomFieldRAM

end OAI
