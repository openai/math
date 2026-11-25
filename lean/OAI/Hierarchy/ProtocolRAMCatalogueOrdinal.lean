import OAI.Hierarchy.ProtocolRAMCatalogueRowFields
import OAI.Hierarchy.ProtocolRAMBoughtOrdinal
import OAI.Hierarchy.ProbeReportedGeometry

namespace OAI
/-! # Original ordinals of the physical core and purchased rows -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open AdaptiveProbe ProbeStage ReportSockets CoreBoard
open PurchaseFrozen
open scoped BigOperators Classical
variable {h W k attempts : ℕ}

def originalBought (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : Marks h W k attempts) : Bought S π depth marked ↪
      Fin (attempts*(ProtocolRAM.PurchaseFrozen.count h (2^W) k*ProtocolRAM.PurchaseFrozen.paths h S.degree depth)) where
  toFun chain := finProdFinEquiv (chain.1,BoughtLocation.relative chain.2)
  inj' := by
    rintro ⟨a,x⟩ ⟨b,y⟩ same
    have eq := finProdFinEquiv.injective same
    have ab := congrArg Prod.fst eq
    dsimp at ab
    subst b
    exact congrArg (Sigma.mk a) (BoughtLocation.relative_injective (congrArg Prod.snd eq))

def Board.ordinal (b : Board) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : Marks h W k attempts) (order : Fin b.coreRows≃Edges S h (2^W) k)
    (size : attempts*(ProtocolRAM.PurchaseFrozen.count h (2^W) k*ProtocolRAM.PurchaseFrozen.paths h S.degree depth)=b.boughtRows) :
    Catalogue S π depth marked ↪Fin b.rows where
  toFun := Sum.elim (fun e=>b.coreIndex (order.symm e))
    (fun e=>b.boughtIndex (Fin.cast size (originalBought S π depth marked e)))
  inj' := by
    rintro (a|a) (c|c) eq
    · have slots : (order.symm a).val=(order.symm c).val :=
        congrArg (fun i : Fin b.rows=>i.val) eq
      exact congrArg Sum.inl (order.symm.injective (Fin.ext slots))
    · have h:=congrArg Fin.val eq
      change (order.symm a).val=b.coreRows+_ at h
      have := (order.symm a).isLt
      omega
    · have h:=congrArg Fin.val eq
      change b.coreRows+_=(order.symm c).val at h
      have := (order.symm c).isLt
      omega
    · apply congrArg Sum.inr
      apply (originalBought S π depth marked).injective
      apply Fin.ext
      have h:=congrArg Fin.val eq
      change b.coreRows+(originalBought S π depth marked a).val=b.coreRows+(originalBought S π depth marked c).val at h
      omega

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
