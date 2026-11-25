import OAI.Hierarchy.DescentPhysicalOrdinaryReturn
import OAI.Hierarchy.DescentStageVenueWireRoom
import OAI.Hierarchy.DescentDatedOrdinaryVenueModel

namespace OAI
/-! # Address bounds for the ordinary result at the attained receiver -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentDatedPriorOperand DescentOperandStateBanks ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

private theorem later {b : Bank} {w lo hi : ℕ} (h : b.Fits w lo) (le_ : lo≤hi) : b.Fits w hi :=
  ⟨h.1,h.2.1,h.2.2.trans le_⟩

theorem result_room {w : ℕ} (floor : ℕ) (src : StageVenueTail.Sources)
    (shape : v.VectorShape) (chart : v.metadata.chart=v.nodeChart)
    (digits : v.metadata.spanBits=v.resolver.size+2) (final : v.operandBook=v.finalChart)
    (venue : v.venue.Space src (v.rasterEnd floor) w) (top : v.operandEnd floor<2^w) :
    v.ResultRoom floor src w := by
  have h₄ : v.metaEnd floor≤v.operandEnd floor:=by
    rw [operandEnd,v.operandBook.affine];exact Nat.le_add_right ..
  have h₃ : v.metaStart floor≤v.metaEnd floor:=by
    rw [metaEnd,v.metadata.ordinary_translate];exact Nat.le_add_right ..
  have h₂ : v.rasterEnd floor≤v.metaStart floor:=by
    rw [metaStart,venueEnd,v.venue.translates];exact Nat.le_add_right ..
  have h₁ : v.endAddress floor≤v.rasterEnd floor:=by
    rw [rasterEnd,StageVenueTail.OrdinaryRaster.translated];exact Nat.le_add_right ..
  have hk := h₁.trans h₂
  have hv := (v.routed_le floor).trans ((v.resolver.floor_le _).trans hk)
  have lim:=h₄.trans_lt top
  have prev (x : Fin v.resolver.blocks) (p : Pages v.resolver.operands) :=
    from_previous_placed v.resolver v.vector (v.vectorStart floor) shape.operands shape.blocks shape.hosts
      shape.groups shape.lanes (hv.trans_lt (h₃.trans_lt lim)) x p
  refine ⟨chart,digits,final,venue,?_,?_,?_,top⟩
  · intro x
    let j : Fin (2^v.venue.k):=⟨if x.val<2^v.venue.k then x.val else 0,by
      split <;> first | assumption | exact Nat.two_pow_pos _⟩
    exact ⟨later (venue.paid j).1 h₂,trivial⟩
  · intro x j
    exact later (prev x (page 6 j)).1 hv
  · intro p x i
    unfold DescentOrdinaryFinal.Chart.sourceBank
    cases h : v.finalChart.columns.symm i with
    | inl f =>
      let source : Bank := if small : f.val < 2 then
        (v.finalSources floor).meta ⟨f.val,small⟩ x
        else previousBank v.finalChart.layout (v.finalSources floor).spanFloor x p
      change source.Fits w (v.metaEnd floor) ∧ v.finalChart.rows ≤ source.size
      by_cases small : f.val < 2
      · simp only [source, dite_eq_left small]
        have stop := v.nodeEnd floor chart digits
        have h := v.nodeChart.valid (v.nodeBankBase floor) (by
          change v.nodeChart.ordinaryEnd (v.metaStart floor) v.metadata.paidBits (v.resolver.size+2)<2^w
          exact (le_of_eq stop).trans_lt lim) (⟨f.val,by assumption⟩ : Fin 2) x
        exact ⟨later h.1 (le_of_eq stop),h.2⟩
      · simp only [source, dite_eq_right small]
        exact ⟨later (prev x p).1 (hv.trans h₃),(prev x p).2⟩
    | inr k =>
      let j:=v.resolver.index (x,v.finalChart.slots.symm k)
      have fit_ := (v.resolver.within (v.normalizedEnd floor) j).2.trans (hk.trans h₃)
      exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (fit_.trans_lt lim),fit_⟩,
        (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
