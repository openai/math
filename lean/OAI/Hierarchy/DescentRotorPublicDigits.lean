import OAI.Hierarchy.DescentRotorActualAperture
import OAI.Hierarchy.DescentRotorPublicRanges
import OAI.Hierarchy.DescentFallbackRepeatedFields

namespace OAI
/-! # Printed range fields of the true public operand at a rotor tap -/
namespace Hierarchy.DescentResetPublicOperandBook.Config
open DescentSIMDLookup DescentFallbackItemSelect DescentFallbackOperandQuery DescentResetLocalRoster
open DescentRotor DescentBaseProfile DescentRotorOperandQueryROM.Shape DescentRotorOperandRanks
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F E : Type} [Field F] [Fintype E] {n h u N : ℕ} (board : NonlinearExpanders.Graph n h)
    (C : DescentResetPublicOperandBook.Config) {hp : 0<C.packetWidth} {src dst : E→Fin (2^n)} {pay : ℝ}
    (P : BaseCircuit F board C.multiplicity C.packetWidth u hp src dst pay) (key : E↪Fin N)
    (x : C.Data n) (side : Bool) (root : code C.residual) (req : Mouth n)
    (slot : E↪Fin C.oldConfig.count)
    (read : ∀e,C.endpoints side root x (slot e)=some (src e,dst e))
    (miss : ∀j,(¬∃e,slot e=j)→C.endpoints side root x j=none)
    (order : ∀a b,before (C.oldItem x side) (slot a) (slot b) ↔ key a<key b)
    (mass : C.traffic x side root=matrixOfBundles src dst)
    (depth : DescentRecordedRotorLayers.layers n C.packetWidth C.gain ((C.reg x) 0).val=P.layers)
local notation "ids" => C.oldItem x side
local notation "ports" => C.portRows x side root req
local notation "ord" => Ordered.orderedAddress key src dst hp
local notation "attached" e => ((if req.pin then dst e else src e)=req.vertex ∧
  (P.choose (ord e).1).val=req.layer ∧ (ord e).2.val=req.digit)
local notation "fiber" => DescentRotorOperandRanks.At src dst (fun p=>(if req.pin then p.2 else p.1)=req.vertex)



open DescentBundleHistory DescentLaneGates DescentRetainedRangeDigits
open DescentFallbackOperandBranch.Config
local notation "under" e:arg => earlierCount src dst key req e
local notation "capacity" => Fintype.card fiber*C.batches

include read miss order mass depth in
/-- The decoder uses the three actual digits of the phased public operand. A
covered second word repeats the same range, and an overrun prints three zeros. -/
theorem tap_range_digits (e : E) (selected : attached e) (bpos : 0<C.batches) (f : Fin 3) :
    rangeDigit (C.tap x side root req) f=
      if req.within< min 2 (capacity-(under e*C.batches+req.batch)) then
        DescentRetainedRangeDigits.value ⟨0,1,min 2 (capacity-(under e*C.batches+req.batch))⟩ f else 0 :=by
  have printed:=public_word board C P key x side root req slot read miss order mass depth e selected bpos
  by_cases yes : req.within < min 2 (capacity - ((under e)*C.batches+req.batch))
  · rw [dite_eq_left yes] at printed
    obtain ⟨_,_,_,hit⟩:=printed
    simp only [hit,rangeDigit,Option.elim_some,ite_eq_left yes]
  · rw [dite_eq_right yes] at printed
    simp only [printed,rangeDigit,Option.elim_none,ite_eq_right yes]

include read miss order mass depth in
/-- At every queried flattened slot of a public rotor mouth, including the
right-hand padding, the dated range words are exactly those of the genuine
two-operand recipe. The earliest slot is positioned after the private spine. -/
theorem public_span {Q : Type} {w : Q→ℕ} {p : ℕ} (hp : 0<p) (multiple : ∀j,w j=w j/p*p)
    (prog : Program (2^n) p w) (z : prog.Node) (back leg : Lane p w)
    (op : prog.op z=equalOp (.wire back) (.wire leg)) (e : E) (selected : attached e) (bpos : 0<C.batches)
    (origin : leg.start=(under e*C.batches+req.batch)*p) (step : leg.stride=1)
    (span : w leg.port/p=capacity)
    (node : Fin C.nodes) (arg : Fin C.args) (f : Fin 3) (outBits : ℕ) (room : 2<2^outBits)
    (aperture : arg.val=back.count (fun j=>w j/p)+req.within)
    (active : (C.oldConfig.header (C.basic x) 0).val≠0)
    (chosen : C.rotor.public_selector board C.multiplicity C.grain node.val arg.val (C.reg x)=some (side,root,req)) :
    (C.column board outBits (some (page f)) (finProdFinEquiv (arg,node)) x).val=
      atSlot (ofProgram (fun j=>w j/p) multiple hp prog) z arg.val f :=by
  have residue : leg.start%p=0:=by rw [origin,Nat.mul_mod_left]
  have c : leg.count (fun j=>w j/p)=min 2 (capacity-(under e*C.batches+req.batch)):=by
    change min (leg.stride+1) (w leg.port/p-leg.start/p)=_
    rw [step,span,origin,Nat.mul_div_cancel _ hp]
  have trueRange:=DescentResetLaneIssue.second_range hp multiple prog z back leg op residue step req.within f
  have actual:=tap_range_digits board C P key x side root req slot read miss order mass depth e selected bpos f
  have written : rangeDigit (C.mixed board node.val arg.val x) f=atSlot (ofProgram (fun j=>w j/p) multiple hp prog) z arg.val f:=by
    rw [public_dispatch board C node.val arg.val x side root req active chosen,actual,aperture,trueRange,c]
    rfl
  have small : rangeDigit (C.mixed board node.val arg.val x) f≤2:=by
    rw [public_dispatch board C node.val arg.val x side root req active chosen,actual]
    by_cases yes : req.within < min 2 (capacity - ((under e)*C.batches+req.batch))
    · rw [ite_eq_left yes]
      fin_cases f
      · exact Nat.zero_le _
      · exact (by decide : (1:ℕ) ≤ 2)
      · exact min_le_left _ _
    · rw [ite_eq_right yes]
      exact Nat.zero_le _
  exact C.column_nat board x arg node f _ outBits small room (fun b=>by
    rw [column_range board C,written])

end
end Hierarchy.DescentResetPublicOperandBook.Config

end OAI
