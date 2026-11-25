import OAI.ThreeFlat.RAM.HistoryPhysicalFamilies

namespace OAI
/-! # Work charged by the installed family guards -/
namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section

theorem enabled_work (u v : ℕ) (f g : Family) : (enabled u f).work=(enabled v g).work := rfl

/-- All tested family guards have a fixed arithmetic charge. -/
def guardFee (fs : List Family) := (fs.map fun f=>2*(enabled 0 f).work+4).sum

theorem bodyCost_le_guardFee {w : ℕ} (u : ℕ) (entry : Memory w) (localTime : ℕ) (fs : List Family) :
    bodyCost u entry localTime (fun _=>localTime) fs≤localTime+guardFee fs := by
  induction fs with
  | nil=>simp [bodyCost,guardFee]
  | cons f fs ih=>
    simp only [bodyCost,guardFee,List.map_cons,List.sum_cons] at *
    rw [enabled_work u 0 f f]
    split <;> omega

def blockGuardFee {F : Type} [Field F] [Fintype F] (B : Diagonal.PhysicalStage.Block F) :=
  (B.levels+1)*(2*(enabled 0 ((refreshGrid B).family 0)).work+4)

theorem guardFee_families {F : Type} [Field F] [Fintype F] (B : Diagonal.PhysicalStage.Block F)
    (start height : ℕ) : guardFee (families B start height)=blockGuardFee B := by
  have all (gs : List (Grid F)) (base : ℕ) :
      guardFee (familiesFrom base gs)=gs.length*(2*(enabled 0 ((refreshGrid B).family 0)).work+4) := by
    induction gs generalizing base with
    | nil=>rfl
    | cons g tail ih=>
      change (2*(enabled 0 (g.family base)).work+4)+guardFee (familiesFrom (base+g.size) tail)=_
      rw [ih,enabled_work 0 0 (g.family base) ((refreshGrid B).family 0),List.length_cons,
        Nat.succ_mul tail.length (2*(enabled 0 ((refreshGrid B).family 0)).work+4)]
      exact Nat.add_comm ..
  unfold families
  rw [all]
  simp [grids,blockGuardFee]


end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
