import OAI.Hierarchy.DescentPhysicalResetPrime
import OAI.Hierarchy.DescentEstimatorFrame

namespace OAI
/-! # The exact exterior memory frame of the fixed reset prefix -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSIMDLookup DescentPackedWalsh DescentSixParty.PackedFlow.Canvas
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentStaticWordColumn
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (a : PhysicalReset) (floor : ℕ)

local notation "P" => a.chart floor
local notation "C" => flow a floor
local notation "E" => estimator a floor
local notation "N" => a.hosts*(a.high+a.low+1)+a.hosts*a.ports

theorem prime_any_framed (src count : Bank) (R δ w : ℕ) (mem : Memory w) (ok : PrimeRoom a floor src count R δ w) :
    ∃prior,(prime a floor src count R δ w).Exec mem ((E).image ((E).literal prior)) (primeTicks a floor R δ w) ∧
      ∀i,i<floor ∨ (E).endAddress≤ i→(E).image ((E).literal prior) i=mem i := by
  have header:(P).endAddress≤(E).start:=((P).estimator_prefix a.payload a.gain a.positive).trans (Nat.le_add_right ..)
  have rows : N=(E).hosts:=by change _=a.hosts*((a.high+a.low)+1+a.ports);ring
  have span:(E).start+(E).hosts*2^(E).high≤(E).inputEnd:=Nat.add_le_add (E).areas.2.2.2.2.2.1 (rows_le (E).hosts (E).high)
  have limit:(E).start+N*2^a.high<2^w:=by
    rw [rows];exact (span.trans ((E).calendar.pre ((E).dim+1))).trans_lt ok.fit.bounded
  have prefixRoom:(P).endAddress<2^w:=header.trans_lt ((Nat.le_add_right ..).trans_lt limit)
  obtain ⟨mid,one,copied⟩:=Setup.setup_any_framed a.previousToken a.previousRoster src a.hosts a.ports R a.high a.low a.bits a.short
    a.lanes floor a.depthCut a.fullBudget a.classBound a.grain w mem ok.batch ok.source prefixRoom
  obtain ⟨prior,two,prepared⟩:=Setup.prepare_any_framed a.previousToken a.previousRoster count a.hosts a.ports R a.high a.low a.bits a.short
    a.lanes floor a.depthCut a.fullBudget a.classBound a.grain δ w (E).start mid ok.batch ok.oldTokens ok.oldRoster
    ok.slots ok.countLow ok.smooth ok.dimensions header limit
  have headerRoom:(E).staticEnd<2^w:=(Nat.le_add_right (E).staticEnd (E).dataGap).trans_lt ((Nat.le_add_right ..).trans_lt limit)
  have low:= (a.occupied floor).1
  have H : floor≤(E).origin:=low
  have starts:(E).start≤(E).endAddress:=by rw [(E).endAddress_eq];omega
  have addr : (E).inputEnd≤(E).endAddress:=by
    have solve:(E).inputEnd≤(E).solveAt:=Nat.le_add_right ..
    have final_:(E).solveAt≤(E).endAddress:=by
      exact ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
    exact solve.trans final_
  refine ⟨prior,?_,?_⟩
  · refine Procedure.Exec.then (Procedure.Exec.then one two) ?_
    exact (E).any prior ok.fit headerRoom ((E).room_of_end ok.bounded) ok.payload (Nat.succ_le_of_lt ok.dimensions)
  · intro i hi
    apply ((E).any_frame ok.fit prior i (by omega)).trans
    have before : (E).start + N*2^a.high ≤ (E).endAddress := by
      rw [rows]
      exact span.trans addr
    apply (prepared i (hi.imp_right (fun high => before.trans high))).trans
    exact copied i (hi.imp_right (fun high => (header.trans starts).trans high))


end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
