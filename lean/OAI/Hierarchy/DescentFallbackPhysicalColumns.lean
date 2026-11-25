import OAI.Hierarchy.DescentResetPublicOperandBook
import OAI.Hierarchy.DescentFallbackOperandShape
import OAI.Hierarchy.DescentFallbackFlatRead

namespace OAI
/-! # The joint operand menu dispatches its measured tree and public tap rows -/
namespace Hierarchy.DescentResetPublicOperandBook.Config
open DescentSIMDLookup DescentDenseHostOrder DescentResetLocalRoster DescentFallbackItemSelect
open scoped Classical Fin.CommRing
noncomputable section
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h) (C : DescentResetPublicOperandBook.Config)
local notation "F" => C.oldConfig

theorem tree_dispatch (node arg : ℕ) (x : C.Data n) (s : Bool)
    (root : code C.residual×Option (Fin (2^n))) (ds : List Bool) (shape : ↥(roster board C.residual C.maxDepth))
    (active : ((F).header (C.basic x) 0).val≠0)
    (located : ((F).header (C.basic x) 2).val=(localRank board C.residual C.maxDepth shape).val)
    (tag : shape.val=.fall s ((),(root.1.val,root.2)) ds)
    (room : DescentFallbackPeriod.rootCell C.residual n root<DescentFallbackShapeTable.rows C.residual (2^n)) :
    let id:=(⟨_,room⟩ : Fin (DescentFallbackShapeTable.rows C.residual (2^n)))
    let amount:=DescentFallbackPeriod.score ((F).packet (C.basic x)) (id,0,id)
    C.mixed board node arg x=(F).make s ((F).header (C.basic x) 1).val (min C.maxDepth (Nat.clog 2 amount)) ds root
      ((F).rowsAt (C.basic x) s root id amount) node arg := by
  have seen : ((C.reg x) 3).val=(localRank board C.residual C.maxDepth shape).val := located
  have ok : ((C.reg x) 3).val<(roster board C.residual C.maxDepth).card :=
    seen ▸ (localRank board C.residual C.maxDepth shape).isLt
  have ordinal : (⟨_,ok⟩ : Fin (roster board C.residual C.maxDepth).card)=
      DescentResetTrunkPalette.order board C.residual C.maxDepth shape := Fin.ext seen
  have decoded : ((DescentResetTrunkPalette.order board C.rotor.residual C.rotor.depth).symm
      ⟨_,ok⟩).val = .fall s ((),(root.1.val,root.2)) ds := by
    let ord := DescentResetTrunkPalette.order board C.residual C.maxDepth
    have recovered : ord.symm ⟨_,ok⟩=shape :=
      (congrArg ord.symm ordinal).trans (ord.symm_apply_apply shape)
    exact (congrArg Subtype.val recovered).trans tag
  have noTap : C.rotor.public_selector board C.multiplicity C.grain node arg (C.reg x)=none := by
    simp [DescentRotorOperandQueryROM.Shape.public_selector,decoded]
  rw [mixed,ite_eq_right active,noTap]
  exact DescentFallbackOperandBranch.Config.mixed_fallback board F node arg (C.basic x) s root ds shape active located tag room

theorem public_dispatch (node arg : ℕ) (x : C.Data n) (s : Bool) (root : code C.residual)
    (req : DescentRotorOperandQueryROM.Shape.Mouth n) (active : ((F).header (C.basic x) 0).val≠0)
    (port : C.rotor.public_selector board C.multiplicity C.grain node arg (C.reg x)=some (s,root,req)) :
    C.mixed board node arg x=C.tap x s root req :=by rw [mixed,ite_eq_right active,port]

/-- All seven dedicated field pages use the same cable, chunk, and cover, as does the query page. -/
theorem column_at (b : ℕ) (x : C.Data n) (arg : Fin (F).args) (node : Fin (F).nodes)
    (q word count : ℕ) (mark : Bool) (actual : C.mixed board node.val arg.val x=some (q,word,count,mark)) :
    let slot:=(finProdFinEquiv (arg,node))
    C.column board b none slot x=(q:ℕ) ∧ ∀i : Fin 7,
      C.column board b (some i) slot x=
        ((![0,0,if mark then word/C.split else 0,if mark then word%C.split else word,0,1,count] i : ℕ) : Cell b) :=by
  dsimp only
  constructor
  · simp only [column,Equiv.symm_apply_apply,actual]
  · intro i
    simp only [column,Equiv.symm_apply_apply,actual]

theorem column_empty (b : ℕ) (x : C.Data n) (arg : Fin (F).args) (node : Fin (F).nodes)
    (empty : C.mixed board node.val arg.val x=none) (field : Option (Fin 7)) :
    C.column board b field (finProdFinEquiv (arg,node)) x=0 := by
  simp only [column,Equiv.symm_apply_apply,empty]

end
end Hierarchy.DescentResetPublicOperandBook.Config

end OAI
