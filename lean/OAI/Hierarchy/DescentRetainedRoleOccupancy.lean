import OAI.Hierarchy.DescentRetainedHomePrefix
import OAI.Hierarchy.DescentPaddedNodeCells

namespace OAI
/-! # Counting every original node of a donor from the issued role page -/
namespace Hierarchy.DescentSixParty.Reached.NodeCells
open DescentKernelHistory DescentLocalArchiveOrder DescentColonies DescentCompiler DescentSIMDLookup
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist : ℕ}
    (cap : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W) (ord : Local B)
    {H b : ℕ} (name : cap.V↪Fin H) (faithful : ∀u,(name u).val=(cap.vertex u).val)
    (x : Block k) (h : Fin H) (g : Fin (S.groupCount age))
local notation "home" => DescentPaidResidentCount.occupies cap.placement (Equiv.refl _) name h g x

include faithful in
/-- The full one-based primitive row identifies both unpaid nodes and vacant lanes.
The sum is over the real prior site at this donor coordinate, independently of its funding. -/
theorem original_count (L : DescentResetRetainedSetup.Layout) (word : Cell L.siteWord) (d₀ : Fin L.donors)
    (enough : ∀v,Fintype.card (B.recipe v).Node≤L.previousNodes)
    (role : NodeOrder.All B→Cell b) (positive : ∀v,(role v).val≠0)
    (resident : ∀j : Fin L.previousNodes,
      (L.entry word d₀ j L.occupiedField).val≠0 ↔
       ((atPhysical cap B ord x j h g).elim 0 role).val≠0) :
    L.originalCount word d₀=∑v,if home v then Fintype.card (B.recipe v).Node else 0 :=by
  have unique {u v : W.graph.Site} (left : home u) (right : home v) : u=v :=by
    exact cap.valid.coordinates (Prod.ext (Prod.ext (left.2.1.trans right.2.1.symm)
      (name.injective (left.1.trans right.1.symm))) (left.2.2.trans right.2.2.symm))
  have marker (j : Fin L.previousNodes) : (L.entry word d₀ j L.occupiedField).val≠0 ↔
      ∃v,home v ∧ j.val<Fintype.card (B.recipe v).Node :=by
    rw [resident,←atPhysical_live cap B ord x j h g name faithful]
    cases at_ : atPhysical cap B ord x j h g with
    | none=>simp
    | some v=>simp [positive v]
  by_cases live : ∃v,home v
  · obtain ⟨v,hv⟩:=live
    have costs : (∑u,if home u then Fintype.card (B.recipe u).Node else 0)=Fintype.card (B.recipe v).Node:=by
      rw [Finset.sum_eq_single v,ite_eq_left hv]
      · intro u _ diff
        exact ite_eq_right (fun hu=>diff (unique hu hv))
      · simp
    rw [costs]
    apply DescentPaidResidentCount.Reset.count_occupied L word d₀ _ (enough v)
    intro j
    rw [marker]
    exact ⟨fun ⟨u,hu,index⟩=>(unique hu hv) ▸ index,fun index=>⟨v,hv,index⟩⟩
  · have absent (v : W.graph.Site) : ¬home v:=fun hv=>live ⟨v,hv⟩
    simp only [ite_eq_right (absent _),Finset.sum_const_zero]
    apply DescentPaidResidentCount.Reset.count_occupied L word d₀ 0 (Nat.zero_le _)
    intro j
    simp [marker,absent]

end
end Hierarchy.DescentSixParty.Reached.NodeCells

end OAI
