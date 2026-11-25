import OAI.Hierarchy.ProbeRepairHistogramAccount

namespace OAI
/-! # Transporting actual paid repair rows from word addresses to commodity labels -/
noncomputable section
namespace Hierarchy.AdaptiveProbe.OuterBank
open scoped Classical BigOperators
variable {I J X : Type*} [Fintype I] [Fintype J]

def coordinates (B : OuterBank I X) (e : I ≃ J) : OuterBank J X where
  stock := fun x j=>B.stock x (e.symm j)
  cash := B.cash
  payload := fun j=>B.payload (e.symm j)
  box := fun j=>B.box (e.symm j)
  coefficient := fun j=>B.coefficient (e.symm j)
  a := B.a
  M := B.M

/-- Recover the original typed commodity, keeping each selected native row,
all its word counts and charges, and the state at both ends unchanged. -/
def FailedRows.ofCoordinates {B : OuterBank I X} (e : I ≃ J) {n w K cap : ℕ} {ρ γ s : ℝ} {x y : X}
    (R : (B.coordinates e).FailedRows n w K cap ρ γ s x y) :
    B.FailedRows n w K cap ρ γ s x y := by
  let tag := fun u=>(R.kind u).map e.symm
  let raw := fun i=>R.raw (e i)
  have some_iff (u) (i : I) : tag u=some i ↔ R.kind u=some (e i) := by
    cases h : R.kind u with
    | none => simp [tag,h]
    | some a => simp [tag,h,Equiv.symm_apply_eq]
  have bits (f) (i : I) : resourceBits tag f i=resourceBits R.kind f (e i) := by
    unfold resourceBits
    simp_rw [some_iff]
  have unit (f) (i : I) : stockChange tag f i=stockChange R.kind f (e i) := by
    unfold stockChange
    simp_rw [some_iff]
  have cost (f b) : cashChange tag f R.weight b=cashChange R.kind f R.weight b := by
    unfold cashChange
    simp [tag]
  have spill : pairing (bitStock w (spillBits cap w raw)) B.box=
      pairing (bitStock w (spillBits cap w R.raw)) (B.coordinates e).box := by
    let f := fun j=>bitStock w (spillBits cap w R.raw) j*(B.coordinates e).box j
    have relabelled:=e.sum_comp f
    simpa only [pairing,f,coordinates,bitStock,spillBits,clipBits,raw,Equiv.symm_apply_apply] using relabelled
  have prices (u) : activePrice tag R.weight (maximizer B.a B.M s B.coefficient B.box (B.units w x)) u=
    activePrice R.kind R.weight (maximizer (B.coordinates e).a (B.coordinates e).M s
      (B.coordinates e).coefficient (B.coordinates e).box ((B.coordinates e).units w x)) u := by
    cases h : R.kind u <;> simp [tag,h,activePrice,coordinates,maximizer,units]
  refine {
    rows:=R.rows,ports:=R.ports,kind:=tag,installed:=R.installed,consumed:=R.consumed,
    weight:=R.weight,broadcast:=R.broadcast,width:=R.width,raw:=raw,
    stock:=?_,retained:=?_,paid:=?_,density:=R.density,width_pos:=R.width_pos,
    width_fits:=R.width_fits,quotes:=?_,curvature:=?_ }
  · intro i
    simpa only [bits,coordinates,raw,Equiv.symm_apply_apply] using R.stock (e i)
  · intro i
    simpa only [coordinates,raw,Equiv.symm_apply_apply] using R.retained (e i)
  · rw [cost,spill]
    exact R.paid
  · dsimp only
    intro r
    simpa only [prices] using R.quotes r
  · simp_rw [unit]
    exact (e.sum_comp _).le.trans R.curvature

end Hierarchy.AdaptiveProbe.OuterBank
end

end OAI
