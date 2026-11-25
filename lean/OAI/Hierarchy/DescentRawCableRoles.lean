import OAI.Hierarchy.DescentDonorChipLookup
import OAI.Hierarchy.DescentNativeDonorROM
import OAI.Hierarchy.DescentRawCableRoster
import OAI.Hierarchy.DescentStarKeys

namespace OAI
/-! # Reading all ordinary overlap flags from the donor's old endpoint records -/

namespace Hierarchy.DescentRawCablePanel
open DescentSIMDLookup DescentSixParty GadgetNetwork DescentHostDirectory
open Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section

private theorem represented (l : Bool) (j : Fin 6) : cluster l (representative (cluster l j))=cluster l j := by
  decide +revert

variable {I P C V : Type} [Fintype I] {d : ℕ} {bits : P→ℕ} (N : Network d P bits)
  (pick : I×Fin 2↪N.Edge) (layout : Bool) (pack : N.Site→C)
local notation "node" => newSite N pick layout pack

omit [Fintype I] in
theorem anchored (i : I) (j : Fin 6) :
    node (.inr (i,j))=node (.inl (StarKeys.endpoint N pick i (cluster layout j))) := by
  have physical (r : Fin 3) :
      node (.inl (StarKeys.endpoint N pick i r))=node (.inr (i,representative r)) := by
    fin_cases r
    · exact source_merge N pick layout pack i 0
    · exact target_merge N pick layout pack i 0
    · exact target_merge N pick layout pack i 1
  exact (Quot.sound (Join.privateWire i j _ (represented layout j).symm)).trans (physical _).symm

/-- The original selected cable itself is the first absorbed leg. -/
theorem picked_old (i : I) (s : Fin 2) :
    node (source N (.inl (pick (i,s))))=node (target N pick (.inl (pick (i,s)))) := by
  simpa [source,target,selected_pick] using source_merge N pick layout pack i s

theorem picked_arm (i : I) (s : Fin 2) :
    node (source N (.inr (.inl (i,s))))=node (target N pick (.inr (.inl (i,s)))) :=
  (target_merge N pick layout pack i s).symm

variable {a loc c : ℕ}
local notation "E" => Cell (loc+1+a)

variable [Fintype V] [DecidableEq V] (rank : V↪ℕ) (key : Merged N pick layout pack→Key V)
  (k g slots : ℕ) (hub : V→Bool) (valid : ∀u,key u∈keys k slots)
  (fits : 2^(k+1)*slots≤2^a)
local notation "primary" => fun u : N.Site => key (node (Sum.inl u))
local notation "pre" => fun u=>packedNumber rank k slots (key (node u))
local notation "post" => fun u=>packedNumber rank k slots (mergeHub hub k g (key (node u)))

include valid fits in
omit [DecidableEq V] in
theorem old_read (e : N.Edge) (left right : Cell loc)
    (same : left=right ↔ (primary (N.src e)).1=(primary (N.dst e)).1) (units : Cell c) :
    oldCable k g slots (GadgetNetwork.selected N pick e).isSome
      (rooted k slots loc a hub (primary (N.src e)) left)
      (rooted k slots loc a hub (primary (N.dst e)) right) units=
      cell (decide (pre (source N (.inl e))=pre (target N pick (.inl e))))
        (decide (post (source N (.inl e))=post (target N pick (.inl e)))) units := by
  cases chosen : GadgetNetwork.selected N pick e with
  | none=>
    simpa [oldCable,source,target,chosen] using rooted_read rank k g slots loc a c hub
      (primary (N.src e)) (primary (N.dst e)) (valid _) (valid _) fits left right same units
  | some t=>
    obtain rfl:=selected_spec N pick chosen
    have joined:=picked_old N pick layout pack t.1 t.2
    dsimp only
    simp [oldCable,joined]

include valid fits in
omit [DecidableEq V] in
theorem motif_read (i : I) (s : Fin 8) (addr : Fin 3→Cell loc)
    (same : ∀j l,addr j=addr l ↔ (primary (StarKeys.endpoint N pick i j)).1=(primary (StarKeys.endpoint N pick i l)).1)
    (sizes : Fin 8→Cell c) :
    motif k g slots layout
      (fun j=>rooted k slots loc a hub (primary (StarKeys.endpoint N pick i j)) (addr j)) sizes s=
      cell (decide (pre (source N (.inr (.inr (i,s))))=pre (target N pick (.inr (.inr (i,s))))))
        (decide (post (source N (.inr (.inr (i,s))))=post (target N pick (.inr (.inr (i,s)))))) (sizes s) := by
  simpa only [motif,source,target,anchored N pick layout pack] using
    rooted_read rank k g slots loc a c hub
      (primary (StarKeys.endpoint N pick i (cluster layout (supplySrc s))))
      (primary (StarKeys.endpoint N pick i (cluster layout (supplyDst s))))
      (valid _) (valid _) fits _ _ (same _ _) (sizes s)

omit [Fintype V] [DecidableEq V] in
theorem arm_read (i : I) (s : Fin 2) (units : Cell c) :
    cell true true units=
      cell (decide (pre (source N (.inr (.inl (i,s))))=pre (target N pick (.inr (.inl (i,s))))))
        (decide (post (source N (.inr (.inl (i,s))))=post (target N pick (.inr (.inl (i,s)))))) units := by
  dsimp only
  simp [picked_arm N pick layout pack i s]

end
end Hierarchy.DescentRawCablePanel

end OAI
