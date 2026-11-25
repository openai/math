import OAI.Hierarchy.DescentResetRetainedPriorBanks

namespace OAI
/-! # Address room for all original seven operand fields and two node fields -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentDatedPriorOperand DescentDatedNodeMetadata ProtocolRAM
noncomputable section
variable (v : Layout)

/-- Exclusive limit of the previously published rectangular field archive, including the
one rounded lookup tail that can cross the end of its last logical row. -/
def priorOperandLimit (base : ℕ) :=
  base+(7*v.previousArgs)*(v.blocks*v.previousLayout.rows)+2^Nat.clog 2 (v.previousLayout.rows+1)

def priorMetaLimit (seed : Bool) (base : ℕ) :=
  if seed then v.previousChart.seedEnd base else v.previousChart.endAddress base

private theorem rounded_fit (base n last limit w : ℕ) (place : base+2^n≤last)
    (before : last≤limit) (room : limit<2^w) : (⟨base,n⟩ : Bank).Fits w limit :=
  ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt ((place.trans before).trans_lt room),place.trans before⟩

theorem prior_registers (seed : Bool) (metadataBase args limit w : ℕ)
    (metaRoom : v.priorMetaLimit seed metadataBase≤limit) (argRoom : v.priorOperandLimit args≤limit)
    (room : limit<2^w) (j : Fin v.sources) :
    ((if seed then v.seedPrior metadataBase args else v.laterPrior metadataBase args) j).Fits w limit :=by
  let l:=v.previousLayout
  let c:=v.previousChart
  have argFit (p : DescentOperandStateBanks.Pages v.previousArgs) (x : Fin v.blocks) :
      (previousBank l args x p).Fits w limit:=by
    have low : p.val*(v.blocks*l.rows)+x.val*l.rows≤(7*v.previousArgs)*(v.blocks*l.rows):=calc
      _ ≤ p.val*(v.blocks*l.rows)+v.blocks*l.rows :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_lt x.isLt)) _
      _ = (p.val+1)*(v.blocks*l.rows) :=(Nat.succ_mul ..).symm
      _ ≤ _ := Nat.mul_le_mul_right _ p.isLt
    apply rounded_fit _ _ (v.priorOperandLimit args) _ _ _ argRoom room
    change args+p.val*(l.blocks*l.rows)+x.val*l.rows+2^Nat.clog 2 (l.rows+1) ≤
      args+(7*v.previousArgs)*(v.blocks*l.rows)+2^Nat.clog 2 (l.rows+1)
    rw [show l.blocks=v.blocks from rfl,Nat.add_assoc args (p.val * _) (x.val * _)]
    exact Nat.add_le_add_right (Nat.add_le_add_left low args) _
  have metaFit (f : Fin 2) (x : Fin v.blocks) :
      ((if seed then c.seedBank metadataBase else c.bank metadataBase) f x).Fits w limit:=by
    have idx := Nat.mul_le_mul_right c.rows (Nat.le_of_lt (c.slot f x).isLt)
    cases seed
    · apply rounded_fit _ _ (c.endAddress metadataBase) _ _ _ metaRoom room
      exact Nat.add_le_add_right (Nat.add_le_add_left idx (c.output metadataBase)) _
    · apply rounded_fit _ _ (c.seedEnd metadataBase) _ _ _ metaRoom room
      exact Nat.add_le_add_right (Nat.add_le_add_left idx metadataBase) _
  cases seed
  · change (v.laterPrior metadataBase args j).Fits w limit
    change ∀ f x, (c.bank metadataBase f x).Fits w limit at metaFit
    dsimp only [laterPrior,priorBanks,directory]
    split <;> first | exact metaFit _ _ | exact argFit _ _
  · change (v.seedPrior metadataBase args j).Fits w limit
    change ∀ f x, (c.seedBank metadataBase f x).Fits w limit at metaFit
    dsimp only [seedPrior,priorBanks,directory]
    split <;> first | exact metaFit _ _ | exact argFit _ _

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
