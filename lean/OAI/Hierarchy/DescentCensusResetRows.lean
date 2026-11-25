import OAI.Hierarchy.DescentCensusBlankRows
import OAI.Hierarchy.DescentOrderedReentry

namespace OAI
/-! # The one potentially empty trunk per fallback terminal in a reentry -/

namespace Hierarchy.DescentResetTrunks
open Computability.BorderVNP.Crossing DescentSixParty DescentRouterBank
open scoped Classical
noncomputable section
variable {F P H Q : Type} [Field F] [Fintype H] [Fintype Q] {d n : ℕ} {bits : P→ℕ}
variable (A : MarkedWorld F n P bits) (home : A.graph.Site→H) (group : Bool→A.graph.Edge→Q) (hub : H→Bool)

omit [Fintype Q] in
theorem blank_trunks {w : A.graph.Edge→ℕ} (same : w=A.graph.width)
    (R : Network d (Bool×Q) (publicWidth group w)) (S : R.Tables F) (live : ∀e,0<w e) :
    (install A home group hub same R S).blank.card ≤ Fintype.card (install A home group hub same R S).graph.Site := by
  subst w
  let M:=world A home group R S hub
  let trunks : H ↪ M.graph.Edge := Function.Embedding.inl.trans Function.Embedding.inr
  have incl : M.blank⊆Finset.univ.map trunks := by
    rintro (⟨s,e⟩|z|e) mem
    · obtain ⟨_,zero⟩:=(M.mem_blank _).1 mem
      exact ((live e).ne' zero).elim
    · exact Finset.mem_map.mpr ⟨z,Finset.mem_univ _,rfl⟩
    · have out:=((M.mem_blank _).1 mem).1
      let mark := marked A home group R hub
      have select := @Finset.mem_filter M.graph.Edge (fun a => mark a = true)
        (fun a => instDecidableEqBool (mark a) true) (@Finset.univ _ M.graph.finiteEdge)
        (Sum.inr (Sum.inr e))
      exact (out (select.mpr ⟨Finset.mem_univ _, rfl⟩)).elim
  have cnt : M.blank.card≤Fintype.card H := by simpa only [Finset.card_map,Finset.card_univ] using Finset.card_le_card incl
  let names : H↪M.graph.Site := ⟨fun v=>Sum.inl (false,v),fun _ _ h=>congrArg Prod.snd (Sum.inl.inj h)⟩
  exact cnt.trans (Fintype.card_le_of_embedding names)

end
end Hierarchy.DescentResetTrunks

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d L : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {q ε : ℝ} {h C Ht : ℕ} (Z : ResetInput W q ε h C Ht) (T : Z.Terminals) (key : W.graph.Edge↪Fin L)

theorem ordered_blank (pos : 0<Z.unit) : (Z.orderedOrdinary T key).blank.card ≤
    Fintype.card (Z.orderedOrdinary T key).graph.Site := by
  have fewer := (Z.orderedReentry T key).blank_pieces Z.unit _ (counts_fit Z T)
  have trunks : (Z.orderedReentry T key).blank.card≤Fintype.card (Z.orderedReentry T key).graph.Site :=
    blank_trunks W T.home Z.placement.input T.hub (funext (fun e=>(Z.allWidths e).symm)) Z.bank Z.tables (fun _=>pos)
  exact fewer.trans trunks

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
