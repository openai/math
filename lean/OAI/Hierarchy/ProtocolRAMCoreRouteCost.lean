import OAI.Hierarchy.ProtocolRAMRowText
import OAI.Hierarchy.ProtocolRAMCoreRouteDirectory
import OAI.Hierarchy.ProtocolRAMCoreRouteBounds
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueCost
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueFits
import OAI.Hierarchy.ProtocolRAMCalendarHardware

namespace OAI
/-! # Address, native clock and text bounds for the two route-directory scans -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe CoreBoard
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical
variable {z W k attempts w out : ℕ} {S : PurchaseSampler}
local notation "N" => Stages z (2^W)
local notation "A" => Actions N k
local notation "r" => Fintype.card (Slots z (2^W) k)

theorem operator_work (x : Source) (a : A) :
    (operator x S z W k attempts a).work≤63+8*ReportSockets.copies k attempts := by
  rcases a with e|t|⟨t,l⟩|l
  · exact x.payload_work e
  · rw [show (operator x S z W k attempts (.inr (.inl t))).work=7 from x.tile_work t];omega
  · exact (x.quote_work t l).trans (by omega)
  · rw [show (operator x S z W k attempts (.inr (.inr (.inr l)))).work=7 from x.center_work l];omega

def operationBound (n k attempts : ℕ) :=
  17+Fintype.card (Actions n k)*(9+8*(63+8*ReportSockets.copies k attempts))

theorem index_work (p : Recipes) (x : Source) :
    (indexWord p x S z W k attempts).work≤operationBound N k attempts := by
  let ord := Fintype.equivFin A
  let rowExpr := Expr.lookup p.operand .row
  have select := BoughtSockets.choose_work_bound (Fintype.card A) 0
    (8*(63+8*ReportSockets.copies k attempts)) (fun i=>(operator x S z W k attempts (ord.symm i)).atRow rowExpr)
    (.lookup p.mode .row) (by
      intro i
      exact (CatalogueRows.substitute_work _ _).trans (by
        rw [show rowExpr.work+1=8 from rfl,Nat.mul_comm];exact Nat.mul_le_mul_left _ (operator_work x _)))
  change 7+1+_+7+1≤_
  dsimp only [ord,rowExpr] at select
  simp only [Expr.work,operationBound] at select ⊢
  have coeff (t : ℕ) : 2+5+t+2=9+t := by omega
  rw [coeff] at select
  omega

theorem index_fits (p : Recipes) (x : Source) (s : Safe x S z W k attempts w out)
    (banks : p.kind.Fits w out ∧ p.mode.Fits w out ∧ p.operand.Fits w out) : (indexWord p x S z W k attempts).Fits w out := by
  have ops (a : A) : (operator x S z W k attempts a).Fits w out := by
    rcases a with e|t|⟨t,l⟩|l
    · exact s.payload e
    · exact s.tile t
    · exact s.quote t l
    · exact s.center l
  exact ⟨⟨banks.1,trivial⟩,trivial,
    BoughtSockets.choose_fits_bound _ _ _ _ (fun i=>CatalogueRows.fits_atRow _ _ (ops _) ⟨banks.2.2,trivial⟩)
      ⟨banks.2.1,trivial⟩,⟨banks.2.2,trivial⟩⟩

theorem pass_fits (p : Recipes) (x : Source) (b : RouteSettlement.Banks)
    (s : Safe x S z W k attempts w b.kind.base)
    (banks : p.kind.Fits w b.kind.base ∧ p.mode.Fits w b.kind.base ∧ p.operand.Fits w b.kind.base)
    (order : b.kind.base+2*r≤b.index.base) (room : b.index.base+2*r<2^w) :
    ∀t∈stages b p x S z W k attempts,t.Fits w := by
  intro t h
  simp only [stages,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl
  · exact ⟨⟨banks.1,trivial⟩,order.trans_lt ((Nat.le_add_right ..).trans_lt room)⟩
  · have base : b.kind.base ≤ b.index.base := (Nat.le_add_right ..).trans order
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ base (index_fits p x s banks),room⟩

theorem clock_bound (p : Recipes) (x : Source) (b : RouteSettlement.Banks) :
    clock (stages b p x S z W k attempts)≤12+(2*r)*(22+2*operationBound N k attempts) := by
  have bound : 2*r*(2*(indexWord p x S z W k attempts).work+4)≤2*r*(2*operationBound N k attempts+4) :=
    Nat.mul_le_mul_left _ (by have := index_work (S:=S) (z:=z) (W:=W) (k:=k) (attempts:=attempts) p x; omega)
  simp only [stages,clock,Pass.clock,Expr.work]
  nlinarith

theorem text_bound (p : Recipes) (x : Source) (b : RouteSettlement.Banks) :
    Native.text (program w (stages b p x S z W k attempts))≤65+4*operationBound N k attempts := by
  have small := index_work (S:=S) (z:=z) (W:=W) (k:=k) (attempts:=attempts) p x
  rw [text_passes]
  simp only [listText,stages,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,rowText,Expr.work]
  omega

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
