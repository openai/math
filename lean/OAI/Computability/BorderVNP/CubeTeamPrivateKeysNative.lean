import OAI.Computability.BorderVNP.CubeTeamPrivateKeys
import OAI.Computability.BorderVNP.CubeTeamPrivateKeysTrials
import OAI.Computability.BorderVNP.CubeScatterPaddingBanks
import OAI.Computability.BorderVNP.CubeTeamRowFold

/-! # Equality with the private tape of the actual symbol-row dispatcher

Each strict side consumes the packet row's private choices. Both singleton
orientations of a strict pair use the shared stream. The diagonal program
consumes the selected singleton digits. The outer dispatcher concatenates
these words exactly in the public square-counter order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube

open Physical Physical.Owned Scatter RoutingISA.Owned

variable {n d blocks b h K s : ℕ} {Team : Type*} {select : Packet n d blocks → Selector n K h}
variable {i : Fin (n+1)} {owner : Fin d → Team}

/-- The ordinary row-data constructors receive the payload lookup of the actual
distributed assignment. The two physical bank addresses are supplied at entry. -/
def Scatter.Assignment.bankData (f : Assignment.Choices b s select i owner) (packetBase singleBase : ℕ) :
    Padding.Banks.Data n d blocks b h K s :=
  ⟨i,packetBase,singleBase,select,Assignment.demands f,Assignment.supplies f,
    SingleRowData.extendSlots (fun z => Assignment.lookup f (.inl z))⟩

/-- Private bits of the native role executed on this directed view, at its real
selector and crossing addresses. -/
def Padding.Banks.Data.privateRowBits (A : Padding.Banks.Data n d blocks b h K s)
    (v : Fin d × Fin d) (sel cross : ℕ) : List Bool :=
  if lo : v.1 < v.2 then rowChoices packetTrialValid (A.packet ⟨v,lo⟩ false sel cross).choices
  else if hi : v.2 < v.1 then rowChoices packetTrialValid (A.packet ⟨v.swap,hi⟩ true sel cross).choices
  else
    let D := A.single v.1 v.2 sel cross
    rowChoices D.selected D.localBits

/-- The strict packet stage consumes exactly its ordered key values. -/
theorem Scatter.Assignment.strictRow_bits (f : Assignment.Choices b s select i owner)
    (packetBase singleBase : ℕ) (pair : Symbols d) (high : Bool) (sel cross : ℕ) :
    rowChoices packetTrialValid ((Assignment.bankData f packetBase singleBase).packet pair high sel cross).choices =
      (strictPrivateKeys select i b s pair high).map (Assignment.lookup f) := by
  rw [PacketRowData.rowChoices_eq_visits,strictPrivateKeys,List.map_flatMap]
  apply List.flatMap_congr
  intro p _
  exact packetPrivateKeys_choices b s select i p high f

/-- Raw private bits on any directed view are obtained by reading its genuine
physical keys. All invalid packet and singleton trials contribute zero bits. -/
theorem Scatter.Assignment.privateRowBits_eq (f : Assignment.Choices b s select i owner)
    (packetBase singleBase : ℕ) (v : Fin d × Fin d) (sel cross : ℕ) :
    (Assignment.bankData f packetBase singleBase).privateRowBits v sel cross =
      (rowPrivateKeys select i b s v).map (Assignment.lookup f) := by
  unfold Padding.Banks.Data.privateRowBits rowPrivateKeys
  by_cases lo : v.1 < v.2
  · rw [dite_eq_left lo,dite_eq_left lo]
    exact Assignment.strictRow_bits f _ _ _ _ _ _
  rw [dite_eq_right lo,dite_eq_right lo]
  by_cases hi : v.2 < v.1
  · rw [dite_eq_left hi,dite_eq_left hi]
    exact Assignment.strictRow_bits f _ _ _ _ _ _
  rw [dite_eq_right hi,dite_eq_right hi,SingleRowData.rowChoices_eq_visits]
  have same : v.1 = v.2 := (le_of_not_gt hi).antisymm (le_of_not_gt lo)
  simp only [Padding.Banks.Data.single,Scatter.Assignment.bankData,same,ite_true,List.map_map]
  apply List.map_congr_left
  intro z _
  exact SingleRowData.extendSlots_apply (fun key => Assignment.lookup f (.inl key)) z

/-- The bit callback indexed by the native outer counter. Out-of-range values
are immaterial to the finite scan. -/
def Padding.Banks.Data.privateTapeAt (A : Padding.Banks.Data n d blocks b h K s)
    (l : TeamRowPrepare.Layout) (q : ℕ) : List Bool :=
  if hq : q < d*d then A.privateRowBits (TeamRows.pairAt d ⟨q,hq⟩) (l.view q) (l.crossing q) else []

private theorem range_val (m : ℕ) : List.range m = (List.finRange m).map Fin.val := by
  apply List.ext_getElem <;> simp

/-- The bijection's raw word for each actual team equals the precise trace-bit
sequence used by the ordinary dispatcher and its native packet/singleton roles. -/
theorem Scatter.nativeWordsEquiv_teamRows [DecidableEq Team] (code : Team ↪ ℕ)
    (f : Assignment.Choices b s select i owner) (team : Team) (l : TeamRowPrepare.Layout)
    (dimension : l.d = d) (id : l.teamID = code team) (packetBase singleBase : ℕ) :
    (((nativeWordsEquiv b s select i owner) f).2 team).val =
      TeamRows.choices l (TeamRows.wordOwner (code ∘ owner))
        ((Assignment.bankData f packetBase singleBase).privateTapeAt l) := by
  rw [nativeWordsEquiv_private,teamPrivateKeys,List.map_flatMap,TeamRows.choices,dimension,range_val,List.flatMap_map]
  apply List.flatMap_congr
  intro q _
  let v := finProdFinEquiv.symm q
  have hw : TeamRows.wordOwner (code ∘ owner) (q.val/d) = code (owner v.1) := by
    have h : q.val/d < d := v.1.isLt
    rw [TeamRows.wordOwner,dite_eq_left h]
    rfl
  have ht : (Assignment.bankData f packetBase singleBase).privateTapeAt l q.val =
      (rowPrivateKeys select i b s v).map (Assignment.lookup f) := by
    rw [Padding.Banks.Data.privateTapeAt,dite_eq_left q.isLt]
    exact Assignment.privateRowBits_eq f ..
  change (teamBlock b s select i owner team q).map (Assignment.lookup f) =
    if TeamRows.wordOwner (code ∘ owner) (q.val/d) = l.teamID then _ else []
  simp only [hw,id,code.injective.eq_iff]
  by_cases ho : owner v.1 = team
  · rw [ite_eq_left ho,ht]
    exact congrArg (List.map (Assignment.lookup f)) (ite_eq_left ho)
  · rw [ite_eq_right ho]
    change (if owner v.1 = team then _ else []).map _ = []
    rw [ite_eq_right ho,List.map_nil]

end Cube

end BorderVNP
end Computability
end OAI
