import OAI.Hierarchy.DescentResetStemStoredChart
import OAI.Hierarchy.DescentResetPeerUnionRAM

namespace OAI
/-! # The occupied compact register addresses resolve to their original graph actors -/
namespace Hierarchy.DescentSixParty.ResetInput
open DescentDenseHostOrder DescentCommonHost DescentResetStemMaskedPorts DescentResetStemKeyReindex
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits} {price ε : ℝ}
    {h C height : ℕ} (Z : ResetInput A price ε h C height) (T : Terminals Z)
variable {H H₀ pad : ℕ} (vertex : Z.V↪Fin H)
set_option quotPrecheck false in
local notation "VN" => ↥(Z.commonNames T)
local notation "count" => Fintype.card VN
local notation "denseId" => denseHostRank Z T vertex
local notation "decode" => DescentStageEdgeReceipt.dense (denseId)

def compactRack (i : Fin pad) : Option VN :=if e:i.val<count then some ((decode).symm ⟨i.val,e⟩) else none

theorem rack_located (i : Fin pad) (u : VN) (placed : Z.compactRack T vertex i=some u) : i.val<count :=by
  by_contra nei
  rw [compactRack, dite_eq_right nei] at placed
  cases placed

theorem rack_idle (i : Fin pad) (empty : Z.compactRack T vertex i=none) : count≤ i.val:=by
  by_contra! occupied
  rw [compactRack, dite_eq_left occupied] at empty
  cases empty

theorem rack_index (i : Fin pad) (u : VN) (placed : Z.compactRack T vertex i=some u) :
    (denseId) u=⟨i.val,Z.rack_located T vertex i u placed⟩ :=by
  have lo:=Z.rack_located T vertex i u placed
  have at_ : (decode).symm ⟨i.val,lo⟩=u:=Option.some.inj (by simpa only [compactRack,dite_eq_left lo] using placed)
  exact (congrArg (fun v => (denseId) v) at_.symm).trans ((decode).apply_symm_apply _)

theorem rack_registers (isHub : Z.V→Bool) (i : Fin pad) (u : VN) (placed : Z.compactRack T vertex i=some u) :
    let j : Fin count:=⟨i.val,Z.rack_located T vertex i u placed⟩
    Z.rawAtIndex T vertex j=Z.rawHostRank T vertex u ∧
    Z.parentIndex T vertex j=vertex (position Z.graph u.val) ∧
    priorHub vertex isHub (Z.parentIndex T vertex j)=isHub (position Z.graph u.val) :=by
  intro j
  have selected : (denseId) u=j:=Z.rack_index T vertex i u placed
  simp only [←selected,Z.rawAtIndex_at,Z.parentIndex_read,priorHub_at,and_self]

theorem rack_owner (present : 0<pad→0<H) (i : Fin pad) (u : VN) (placed : Z.compactRack T vertex i=some u) :
    paddedParent (Z.parentIndex T vertex) (le_refl H) present i=vertex (position Z.graph u.val) :=by
  have selected:=Z.rack_index T vertex i u placed
  apply Fin.ext
  simpa only [paddedParent,dite_eq_left (Z.rack_located T vertex i u placed),←selected,Fin.val_castLE] using
    congrArg Fin.val (Z.parentIndex_read T vertex u)

end
end Hierarchy.DescentSixParty.ResetInput

namespace Hierarchy.DescentResetPeerUnionRAM
open DescentSortedRoster
open scoped Classical
variable {H : ℕ} {V : Type*} [DecidableEq V]

/-- Remove the extra self entry of the four-candidate classifier using its
independently measured self-incidence bit. -/
theorem measured_neighbors (found : Fin H→Fin 3→Option (Fin H)) (name : V↪Fin H)
    (neighbors : V→Finset V) (u : V)
    (four : present (selfPeers found) (name u)=(insert u (neighbors u)).map name)
    (absent : (∀j,found (name u) j≠some (name u)) ↔ u∉neighbors u) :
    present found (name u)=(neighbors u).map name := by
  rw [self_present,Finset.map_insert] at four
  ext x
  by_cases same : x=name u
  · subst x
    have none_ : name u∉present found (name u) ↔ u∉neighbors u :=by
      simpa only [present,Finset.mem_filter,Finset.mem_univ,true_and,not_exists] using absent
    simpa using (not_congr none_)
  · have member:=Finset.ext_iff.mp four x
    simpa only [Finset.mem_insert,same,false_or] using member

end Hierarchy.DescentResetPeerUnionRAM

end OAI
