import OAI.Computability.BorderVNP.CubeRouteExteriorTables

/-! # Physical wire-layout independence for genuine exterior-indexed public executions -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube LocalRow CubeArena CubeHeaderInstall Crossing Physical MeanChoice LabelIndex
open BorderVNP.TeamContraction BorderVNP.Routing BorderVNP.RoutingISA.Transmission

/-- All executions on the common packed network and copied header yield one compact data list, one ordered
routing table, and one typed wire layout. The common group and cell owners follow from the label and
directory programs on the separate processor memories. The calibrated layout fields are the actual
outputs of the public budget guard and descriptor writers. -/
theorem packed_exterior_layouts {R w D : ℕ} {T : Type*} (team : T → Fin (R+1)) (ref : T) (a : CubeArena.Layout) (frame controls : ℕ) (axis : Fin (a.n+1))
    (pub : T → Arg → Word w) (mac : T → TeamOpcode.Macros w 8)
    (banks afterLabels : T → Bank w) (mem selected : T → Memory w)
    (trace : T → List (TeamRAM.Event w)) (final : T → ℕ → ℕ)
    (f : T → BroadcastFrame) (old : T → Fin 81 → Word w)
    (fresh profile gates outputs bits off ell : ℕ) (raw : List Bool)
    (pins : ∀ u, BootPins (pub u) (f u) (jointFields (a.extension (old u)) fresh profile gates outputs bits off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) raw (mem u))
    (fit : ∀ u, LabelPrefixFits (pub u 0).val w (readings (mem u)))
    (labelRun : ∀ u, Runs (pub u) (mac u) (.seq LabelIndex.directoryProgram NativeIntervals.prepare)
      (banks u) (mem u) (trace u) (afterLabels u) (selected u))
    (count : ∀ u, readings (mem u) ((pub u 0).val+11)=a.cells) (room : a.stop < 2^w)
    (rows : Sym2 (Fin a.header.d) → Fin (a.n+1) → ℕ) (axes : a.header.a=a.n+1) (positive : 0 < a.header.d)
    {P : Type*} {pinWidth : P → ℕ} (N : Network D P pinWidth) (cell : N.Site → Fin a.cells)
    {A : Type*} [Fintype A] (recv : A → Fin a.cells) (width : A → ℕ)
    {r link : ℕ} (directory : Packing.Directory.Layout) (pp lp : T → ℕ → ℕ × ℕ)
    {I : Type*} [Fintype I] (hostCell : I → Fin a.cells) (id : I ↪ ℕ) (bitsAt : I → ℕ)
    (placed : ∀ u, Packing.Directory.BankPlacement directory (pp u) (lp u) I hostCell id bitsAt)
    (keys : ∀ u k, (placed u).key k=(placed ref).key k) (bounds : directory.DestinationBounds)
    (L : T → WireLayout (R+1) r link) (teams : R+1=a.teams) :
    let dir := fun u => LabelIndex.layout (pub u 0).val (readings (mem u))
    let cells := fun u => finCongr ((count u).symm : a.cells=(dir u).cells)
    let input := fun u => powerHeaderImage a (f u).dst (readings (selected u))
    let group := fun u (g : Fin a.header.d) => TeamNative.owner R ((weightLayout a frame axis.val).weight (input u)) g.val
    let owner := fun u => a.receivingOwner frame axis R (input u)
    ∀ (edges : ∀ u, N.CrossingEdge cell ↪ Fin (dir u).cableCount) (data : ∀ u, A ↪ Fin (dir u).deliveryCount),
      (∀ u, RowPlacement (networkRows N cell recv width) (fromTables (dir u) (readings (mem u)) (fit u).endpoints)
        (cells u) ((edges u).sumMap (data u))) →
      (∀ u, NativeEntry a frame controls axis R (input u) (readings (mem u)) (final u)) →
      (∀ u, DirectorySources a frame controls axis (fun m => a.ScannerWords frame (team u).val axis.val
        (fun g => (group u g).val) (readings (pub u)) m rows) w (final u)) →
      (∀ u, (L u).header=raw.length ∧ (L u).width=tableWidth (exteriorTable a frame directory (pp u) (lp u))
        (exteriorRows a directory (pp u) (lp u) (owner u) ⟨axis,rows⟩ (group u)) teams) →
      ∀ u, directory.directory (pp u) (lp u)=directory.directory (pp ref) (lp ref) ∧
        exteriorTable a frame directory (pp u) (lp u)=exteriorTable a frame directory (pp ref) (lp ref) ∧
        exteriorRows a directory (pp u) (lp u) (owner u) ⟨axis,rows⟩ (group u) =
          exteriorRows a directory (pp ref) (lp ref) (owner ref) ⟨axis,rows⟩ (group ref) ∧
        (L u).width=(L ref).width ∧ L u=L ref := by
  intro dir cells input group owner edges data labelPlace native sources calibrated
  have owners := packed_exterior_owners team ref a frame controls axis pub mac banks afterLabels mem selected trace final
    f old fresh profile gates outputs bits off ell raw pins fit labelRun count room rows axes positive
    N cell recv width edges data labelPlace native sources
  exact exterior_tables_of_placement ref a directory pp lp frame hostCell id bitsAt placed keys bounds
    owner ⟨axis,rows⟩ group owners L raw.length teams calibrated

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
