import OAI.Computability.BorderVNP.DiagonalPositiveCoreReceived
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsDirectory

/-! # Enumerating the original cell banks from the compact native report directories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.ReceivedRows

open RoutingISA TypedTaskBuilder DiagonalTallyCellReports ReportDirectory Packing.BundleDirectory
open Packing.BottomReports CellSparse
open scoped Classical

variable {T C : ℕ} (layout : Fin T → ReportLayout)
    (d : Fin T → Packing.BundleDirectory.Layout) (rows : Fin T → CellControlRows.Layout)
    (host : ∀ u, Fin (d u).bundles → Fin (d u).cells) (source : ∀ u, Fin (d u).bundles → ReportBundle)
    (prior : Fin T → ℕ → ℕ) (digits : ∀ u, ℕ → Fin (layout u).gadgets → Fin (layout u).countWidth → Bool)
    (team : Fin C → Fin T)
    (size : ∀ u,(rows u).cells=C) (nativeTeam : ∀ u,(rows u).team=u.val)
    (stored : ∀ u (c : Fin C),(rows u).owner (grouped (d u) (host u) (source u) (prior u)) c.val=(team c).val)

local notation3 "middle" u => grouped (d u) (host u) (source u) (prior u)
local notation3 "directory" u => directoryCells (d u) (rows u) (layout u) (host u) (source u) (middle u) (digits u)

private theorem atDirectory (u : Fin T) (i : Fin (directory u).length) :
    (directory u).get i = directoryCell (d u) (rows u) (layout u) (host u) (source u)
      (middle u) (digits u) (globalCell (rows u).toLayout (middle u) i.val) :=
  List.get_ofFn _ i

private noncomputable def localOrder (u : Fin T) :
    Fin (directory u).length ≃ {c : Fin C // team c=u} := by
  refine (finCongr (List.length_ofFn)).trans ((ownedOrder (rows u).toLayout (middle u)).symm.trans
    (Equiv.subtypeEquiv (finCongr (size u)) ?_))
  intro j
  change (rows u).owner (middle u) j.val=(rows u).team ↔ team (Fin.cast (size u) j)=u
  rw [nativeTeam u,← Fin.val_inj,← stored u (Fin.cast (size u) j)]
  rfl

/-- The actual marker-free grouped directory and compact native owner scan
enumerate every original cell exactly once, using their global cell numbers.
Only the stored owner words and team frame numbers enter this proof. -/
noncomputable def ofDirectories : ReceivedRows layout C where
  cells := fun u => directory u
  order := (Equiv.sigmaCongrRight (localOrder layout d rows host source prior digits team size nativeTeam stored)).trans
    (Equiv.sigmaFiberEquiv team)
  number := by
    intro u i
    have lim : i.val < (rows u).before (middle u) (rows u).cells := by
      simpa only [directoryCells,List.length_ofFn] using i.isLt
    change ((directory u).get i).number=(localOrder layout d rows host source prior digits team size nativeTeam stored u i).val.val
    rw [atDirectory layout d rows host source prior digits u i]
    change globalCell (rows u).toLayout (middle u) i.val=_
    rw [globalCell,dite_eq_left lim]
    rfl

local notation3 "received" => ofDirectories layout d rows host source prior digits team size nativeTeam stored

/-- The grouped native directory presents this cell on its actual owning team. -/
theorem ofDirectories_owner (u : Fin T) (i : Fin ((received).cells u).length) :
    team ((received).order ⟨u,i⟩)=u :=
  (localOrder layout d rows host source prior digits team size nativeTeam stored u i).property

/-- At its global numeral the emitted row has precisely the stable filter of
all original bundle source ordinals, even if the filter is empty. -/
theorem ofDirectories_bundles (u : Fin T) (i : Fin ((received).cells u).length) :
    (((received).cells u).get i).bundles =
      (sourceRows (host u) ((received).order ⟨u,i⟩).val).map (source u) := by
  rw [← (received).number u i]
  change ((directory u).get i).bundles=(sourceRows (host u) ((directory u).get i).number).map (source u)
  rw [atDirectory layout d rows host source prior digits u i]
  rfl

/-- On the actual one-copy physical payload, the stable group has exactly the
marked copy count required by the native private validator. Its uses may be
resampled on any candidate report tape. -/
theorem ofDirectories_useCount (u : Fin T) (i : Fin ((received).cells u).length)
    (bundle : Fin (d u).bundles → Bundle) (body : Fin (d u).bundles → List Factor)
    (bank : Fin (d u).bundles → ℕ → Bool)
    (payload : ∀ j,source u j=physicalBundle (bundle j).header (body j) (bundle j).factors (bank j))
    (tape : ℕ → Bool) (offset : ℕ) :
    ((tapeBundles tape offset (((received).cells u).get i).bundles).map ReportBundle.useCount).sum=
      (((sourceRows (host u) ((received).order ⟨u,i⟩).val).map bundle).map Bundle.useBits).sum := by
  rw [ofDirectories_bundles]
  simp only [tapeBundles_useCount,List.map_map,Function.comp_def,payload,physicalBundle,ReportBundle.useCount,
    positions_length,Bundle.useBits]

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
