import OAI.Computability.BorderVNP.CubeRouteTeamOwners
import OAI.Computability.BorderVNP.CubeLabelCommonTeams

/-! # Canonical owner tables across arbitrary exterior and team indices -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube LocalRow CubeArena CubeHeaderInstall Crossing Physical MeanChoice LabelIndex

/-- The native public prefix on every indexed exterior/team input computes one common group and cell assignment
from the actual compacted network. All label and demand words and their table bases
are read from the corresponding native histories. -/
theorem packed_exterior_owners {R w D : ℕ} {T : Type*} (team : T → Fin (R+1)) (ref : T) (a : CubeArena.Layout) (frame controls : ℕ) (axis : Fin (a.n+1))
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
    {A : Type*} [Fintype A] (recv : A → Fin a.cells) (width : A → ℕ) :
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
      ∀ u, group u=group ref ∧ ∀ c < a.cells, owner u c=owner ref c := by
  intro dir cells input group owner edges data place native sources
  obtain ⟨_,lab,grp,own,pair,host,rec,stop⟩ := a.writer_order
  obtain ⟨_,labelsEnd,startData,dataEnd,widthBase⟩ := arena_label_arrays a
  have powEnd : a.powerBase+a.n+1=a.groupWeights := by simp only [CubeArena.Layout.groupWeights,Nat.add_assoc]
  have alph : a.alphabet ≤ a.alphabet^2 := by
    rw [pow_two]; exact Nat.le_mul_of_pos_right _ (pow_pos positive _)
  have f48 (u : T) := (pins u).arenaOperand a (old u) fresh profile gates outputs bits off ell
    (k:=48) (value:=a.publicBase) rfl (by omega)
  have f51 (u : T) := (pins u).arenaOperand a (old u) fresh profile gates outputs bits off ell
    (k:=51) (value:=a.demands) rfl (by omega)
  have f56 (u : T) := (pins u).arenaOperand a (old u) fresh profile gates outputs bits off ell
    (k:=56) (value:=a.alphabet) rfl (by omega)
  have f57 (u : T) := (pins u).arenaOperand a (old u) fresh profile gates outputs bits off ell
    (k:=57) (value:=a.widthBase) rfl (by omega)
  have asc {k l : ℕ} (h : k=l) : (List.finRange l).map (finCongr h).symm=List.finRange k := by
    subst l; simp
  have same := GroupWeights.common_selected_words N cell recv width pub mac banks mem selected trace afterLabels labelRun fit
    (a.alphabet-1) (List.finRange a.cells) cells edges data place (fun u => asc _) (fun u => congrArg (·-1) (f56 u)) (fun u => by
      change (dir u).data+(dir u).cells ≤ readings (mem u) ((pub u 0).val+57)
      have d51 : (dir u).data=a.demands := f51 u
      have d11 : (dir u).cells=a.cells := count u
      have d57 : readings (mem u) ((pub u 0).val+57)=a.widthBase := f57 u
      rw [d51,d11,d57]; exact dataEnd)
  apply native_exterior_owners team ref a frame controls axis (fun u => (f u).dst) (fun u => readings (selected u))
    (fun u => readings (mem u)) final (fun u => readings (pub u)) rows axes positive native sources
  intro u c hc
  have word := same u ref ⟨c,hc⟩
  change readings (selected u) (readings (mem u) ((pub u 0).val+48)+c) =
      readings (selected ref) (readings (mem ref) ((pub ref 0).val+48)+c) ∧
      readings (selected u) ((dir u).data+c)=readings (selected ref) ((dir ref).data+c) at word
  have label (t : T) : readings (mem t) ((pub t 0).val+48)=a.publicBase := f48 t
  have demand (t : T) : (dir t).data=a.demands := f51 t
  rwa [label,label,demand,demand] at word

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
