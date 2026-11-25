import OAI.Hierarchy.DescentFallbackRelayBounds
import OAI.Hierarchy.DescentPublicTapQueryBound

namespace OAI
/-! # Bound the public fallback-tree query before the signed lookup -/
namespace Hierarchy.DescentFallbackOperandBranch.Config
open DescentFallbackItemSelect DescentFallbackOperandQuery DescentPrivateTreeTemplate
open DescentResetLocalRoster DescentHostDirectory DescentPacking.PackedMatch.Local
noncomputable section
variable {n d : ℕ} (board : NonlinearExpanders.Graph n d) (C : Config)

theorem make_query_bound (side : Bool) (cap height : ℕ) (path : List Bool)
    (root : code C.residual×Option (Fin (2^n))) (items : Fin C.count→Item) (node arg : ℕ)
    (sectors : C.sectors=2^n) (depth : height≤C.maxDepth)
    (positive : 0<C.privateSlots) (tree : Fintype.card (Edge height)≤C.privateSlots)
    (stems : ∀j,C.stemAt side cap (items j)≤2*total C.toShape cap)
    {out : ℕ×ℕ×ℕ×Bool} (got : C.make side cap height path root items node arg=some out) :
    out.1≤2*total C.toShape cap :=by
  unfold make at got
  obtain ⟨j,_,row⟩:=Option.bind_eq_some_iff.mp got
  obtain ⟨leaf,_,output⟩:=Option.bind_eq_some_iff.mp row
  dsimp only at output
  split at output
  · split at output
    · obtain ⟨i,_,item⟩:=Option.bind_eq_some_iff.mp output
      cases item
      exact stems i
    · cases output
      exact C.tree_bound side true cap height _ leaf root sectors positive tree
  · by_cases terminal : path.length=height
    · simp only [terminal, ↓reduceIte] at output
      split at output
      · cases output
      · cases output
        exact C.contact_bound side cap height leaf root sectors depth
    · simp only [terminal, ↓reduceIte] at output
      split at output
      · cases output
      · cases output
        exact C.tree_bound side false cap height _ leaf root sectors positive tree

theorem mixed_query_bound (node arg : ℕ) (x : C.Data n)
    (sectors : C.sectors=2^n) (donors : C.donors≤2^C.residual) (capRoom : C.oldCap≤(C.header x 1).val)
    (positive : 0<C.privateSlots) (slots : ∀t≤C.maxDepth,Fintype.card (Edge t)≤C.privateSlots)
    {out : ℕ×ℕ×ℕ×Bool} (got : C.mixed board node arg x=some out) :
    out.1≤2*total C.toShape (C.header x 1).val :=by
  unfold mixed at got
  dsimp only at got
  repeat' first
    | contradiction
    | exact C.relay_query x _ node arg donors capRoom got
    | (apply C.make_query_bound _ _ _ _ _ _ _ _ sectors (Nat.min_le_left _ _) positive
          (slots _ (Nat.min_le_left _ _)) _ got
       intro j
       apply C.stem_bound
       · exact (finProdFinEquiv.symm j : Fin C.donors×Fin (2*C.oldCap)).1.isLt.trans_le donors
       · exact (finProdFinEquiv.symm j : Fin C.donors×Fin (2*C.oldCap)).2.isLt.trans_le
           (Nat.mul_le_mul_left _ capRoom))
    | split at got

end
end Hierarchy.DescentFallbackOperandBranch.Config
namespace Hierarchy.DescentResetPublicOperandBook.Config
open DescentPrivateTreeTemplate DescentResetLocalRoster DescentFallbackOperandQuery DescentSIMDLookup DescentPackedZip
open scoped Classical Fin.CommRing
noncomputable section
variable {n d : ℕ} (board : NonlinearExpanders.Graph n d) (C : Config)
local notation "F₀" => C.oldConfig

/-- Both public branches select among the same native candidate ranks, using the actual cap word. -/
theorem column_query_bound (width : ℕ) (j : Fin (F₀).mouths) (x : C.Data n)
    (sectors : C.sectors=2^n) (donors : C.donors≤2^C.residual) (capRoom : C.oldCap≤((C.reg x) 0).val)
    (positive : 0<C.privateSlots) (slots : ∀t≤C.maxDepth,Fintype.card (Edge t)≤C.privateSlots)
    :
    (C.column board width none j x).val≤2*total (F₀).toShape ((C.reg x) 0).val :=by
  let pair:=finProdFinEquiv.symm j
  change (match C.mixed board pair.2.val pair.1.val x with
      | none=>0 | some (q,_,_,_)=>(q:Cell width)).val≤_
  cases found : C.mixed board pair.2.val pair.1.val x with
  | none => exact Nat.zero_le _
  | some answer =>
    have bound : answer.1≤2*total (F₀).toShape ((C.reg x) 0).val:=by
      by_cases inactive : ((F₀).header (C.basic x) 0).val = 0
      · simp [mixed,inactive] at found
      · cases port : C.rotor.public_selector board C.multiplicity C.grain pair.2.val pair.1.val (C.reg x) with
        | none =>
          simp only [mixed, ite_eq_right inactive, port] at found
          exact (F₀).mixed_query_bound board pair.2.val pair.1.val (C.basic x) sectors donors capRoom
            positive slots found
        | some selected =>
          obtain ⟨side,root,req⟩ := selected
          simp only [mixed, ite_eq_right inactive, port] at found
          exact C.tap_query_bound x side root req donors sectors capRoom found
    exact (Nat.mod_le _ _).trans bound

end
end Hierarchy.DescentResetPublicOperandBook.Config

end OAI
