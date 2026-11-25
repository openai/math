import OAI.Hierarchy.DescentResetPrimaryRange
import OAI.Hierarchy.DescentFallbackRelayBounds

namespace OAI
/-! # The public operand lookup executed at the original relay shape -/
namespace Hierarchy.DescentResetPublicOperandBook.Config
open DescentSIMDLookup DescentDenseHostOrder DescentResetLocalRoster DescentHostDirectory DescentPackedZip
open DescentFallbackOperandQuery DescentFallbackItemSelect DescentPacking.PackedMatch.Local
noncomputable section
variable {n d : ℕ} (board : NonlinearExpanders.Graph n d) (C : Config)
local notation "F₀" => C.oldConfig

theorem mixed_relay (x : C.Data n) (shape : ↥(roster board C.residual C.maxDepth))
    (live : ((F₀).header (C.basic x) 0).val≠0)
    (seen : ((F₀).header (C.basic x) 2).val=(localRank board C.residual C.maxDepth shape).val)
    {first target} (relayAt : shape.val=.trunk true (first,target)) (node arg : ℕ) :
    C.mixed board node arg x=(F₀).relay (C.basic x) target node arg := by
  have bound : ((F₀).header (C.basic x) 2).val<(roster board C.residual C.maxDepth).card:=
    seen ▸ (localRank _ _ _ shape).isLt
  have ix : (⟨((F₀).header (C.basic x) 2).val,bound⟩:Fin (roster board C.residual C.maxDepth).card)=
      DescentResetTrunkPalette.order board C.residual C.maxDepth shape:=Fin.ext seen
  have selector : C.rotor.public_selector board C.multiplicity C.grain node arg (C.reg x)=none :=by
    have decoded : ((DescentResetTrunkPalette.order board C.rotor.residual C.rotor.depth).symm
        ⟨((C.reg x) 3).val,bound⟩).val = .trunk true (first,target) := by
      let ord := DescentResetTrunkPalette.order board C.residual C.maxDepth
      have recovered : ord.symm ⟨_,bound⟩=shape :=
        (congrArg ord.symm ix).trans (ord.symm_apply_apply shape)
      exact (congrArg Subtype.val recovered).trans relayAt
    simp [DescentRotorOperandQueryROM.Shape.public_selector,decoded]
  simp only [mixed,ite_eq_right live,selector,DescentFallbackOperandBranch.Config.mixed,dite_eq_left bound,ix,
    Equiv.symm_apply_apply,relayAt]

theorem relay_request (x : C.Data n) (shape : ↥(roster board C.residual C.maxDepth))
    (live : ((F₀).header (C.basic x) 0).val≠0)
    (seen : ((F₀).header (C.basic x) 2).val=(localRank board C.residual C.maxDepth shape).val)
    {first target} (relayAt : shape.val=.trunk true (first,target)) (node arg : ℕ) (j : Fin (F₀).count)
    (hit : select ((F₀).relayItems (C.basic x)) ((F₀).relayRows (C.basic x) target) node=some j)
    (valid : arg<2*C.batches) :
    let cap:=((F₀).header (C.basic x) 1).val
    let all:=total (F₀).toShape cap
    C.mixed board node arg x=some (if arg<C.batches then
      (directed all true (stemSlots (F₀).toShape cap),node*C.batches+arg,1,target.2.isSome)
    else (directed all false (2^C.residual*(2*cap)+j.val),arg-C.batches,1,false)) :=by
  rw [C.mixed_relay board x shape live seen relayAt]
  by_cases firstRow : arg<C.batches <;>
    simp [DescentFallbackOperandBranch.Config.relay,hit,valid,firstRow]
end
end Hierarchy.DescentResetPublicOperandBook.Config

end OAI
