import OAI.Hierarchy.DescentRotorFlatPhysical
import OAI.Hierarchy.DescentEqualityRangeDigits

namespace OAI
/-! # The affine fields of the actual flattened private rotor prefix, including padding -/
namespace Hierarchy.DescentRotorOperandQueryROM.Shape
open DescentSIMDLookup DescentPhysicalSplit DescentBatchedNodeOrder DescentRotor DescentLaneGates DescentCommonHost
open DescentBatchedRotor DescentResetGates DescentRouterSlots DescentKernelHistory DescentBundleHistory
open DescentRetainedRangeDigits DescentTerminalSliceRuns DescentDenseHostOrder DescentHostDirectory
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {n h : ℕ} (G : NonlinearExpanders.Graph n h) (C : Shape)
local notation "Q" => DescentCommonPalette.rotor G

def PrivateLane.code (mult levels p : ℕ) (l : PrivateLane G) : SliceCode :=
  ⟨l.start%p,l.stride,l.count G C mult levels p⟩
theorem PrivateLane.range_field (mult layers p split j : ℕ) (l : PrivateLane G) (f : Fin 3) :
    l.kept G C mult layers p split j (page f)=DescentRetainedRangeDigits.value (l.code G C mult layers p) f:=by fin_cases f <;>rfl

private theorem copies (mult levels p : ℕ) (l : PrivateLane G) :
    (l.names G C mult levels p).map (fun a=>(a.1 : PrivateLane G).code G C mult levels p)=
      List.replicate (l.count G C mult levels p) (l.code G C mult levels p):=by
  simp [PrivateLane.names,List.map_ofFn,Function.comp_def]

theorem private_occurrences (mult layers p node : ℕ) (site : (Q).Site) :
    repeatFields ((C.privateRows G mult layers p node site).map (PrivateLane.code G C mult layers p))=
      (C.flattened G mult layers p node site).map (fun a=>a.1.code G C mult layers p):=by
  simp only [repeatFields,flattened,List.map_flatMap,List.flatMap_map]
  apply congrArg (fun fn => List.flatMap fn (C.privateRows G mult layers p node site))
  funext l
  exact (copies G C mult layers p l).symm

section Fields
set_option quotPrecheck false
variable {A : Type} {width : A→ℕ} {Y p : ℕ} (units : A→ℕ) (multiple : ∀a,width a=units a*p)
  (hp : 0<p) (prg : Program Y p width) (z : prg.Node)
variable (mult layers node : ℕ) (site : (DescentCommonPalette.rotor G).Site)
local notation "stored" => C.flattened G mult layers p node site
local notation "declared" => (C.privateRows G mult layers p node site).map (PrivateLane.code G C mult layers p)
local notation "recipe" => DescentBundleHistory.ofProgram (Y:=Y) (p:=p) (w:=width) units multiple hp prg

theorem private_prefix (remaining : List SliceCode)
    (formal : (operandCodes units (prg.op z)).flatten=declared++remaining) :
    DescentRetainedRangeDigits.occurrences (r:=prg.recipe) recipe z=(stored).map (fun a=>a.1.code G C mult layers p)++repeatFields remaining:=by
  rw [←DescentRetainedRangeDigits.layout (r:=prg.recipe) recipe z,lane_codes units multiple hp prg z,formal]
  rw [show repeatFields (declared++remaining)=repeatFields declared++repeatFields remaining by simp [repeatFields]]
  rw [private_occurrences]

theorem private_at_slot (remaining : List SliceCode) (formal : (operandCodes units (prg.op z)).flatten=declared++remaining)
    (arg within split : ℕ) (l : PrivateLane G) (hit : (stored)[arg]?=some (l,within)) (f : Fin 3) :
    l.kept G C mult layers p split within (page f)=DescentRetainedRangeDigits.atSlot (r:=prg.recipe) recipe z arg f:=by
  have inside:arg<(stored).length:=(List.getElem?_eq_some_iff.mp hit).choose
  unfold DescentRetainedRangeDigits.atSlot
  rw [private_prefix G C units multiple hp prg z mult layers node site remaining formal,
    List.getElem?_append_left (by simpa using inside),List.getElem?_map,hit]
  exact PrivateLane.range_field G C mult layers p split within l f

theorem private_outside (remaining : List SliceCode) (formal : (operandCodes units (prg.op z)).flatten=declared++remaining)
    (arg : ℕ) (outside : ((recipe).recipe hp).arity z≤arg) : (stored)[arg]?=none:=by
  have s:=DescentRetainedRangeDigits.length (r:=prg.recipe) recipe z hp
  rw [private_prefix G C units multiple hp prg z mult layers node site remaining formal,List.length_append,List.length_map] at s
  exact List.getElem?_eq_none (by omega)

end Fields

private theorem packet_lt {layers batches : ℕ} (r : Fin layers) (b : Fin batches) :
    r.val*batches+b.val<layers*batches:=by
  have row:=Nat.mul_le_mul_right batches (Nat.succ_le_of_lt r.isLt)
  rw [Nat.succ_mul] at row
  omega

theorem private_address (mult layers p node arg : ℕ) (site : (Q).Site) (l : PrivateLane G) (within : ℕ)
    (hit : (C.flattened G mult layers p node site)[arg]?=some (l,within)) : l.address<layers*C.batches:=by
  obtain ⟨i,eqn⟩:=List.getElem?_eq_some_iff.mp hit
  have member:(l,within)∈C.flattened G mult layers p node site:=by rw [←eqn];exact List.getElem_mem i
  obtain ⟨q,hq,pair⟩:=List.mem_flatMap.mp member
  obtain ⟨j,hj⟩:=List.mem_ofFn.mp (show (l,within)∈q.names G C mult layers p from pair)
  change (q,j.val)=(l,within) at hj
  have e:q=l:=congrArg Prod.fst hj
  subst q
  rcases site with ⟨v,b|i⟩
  · cases b
    · simp only [privateRows] at hq
      split at hq
      next yes =>
        obtain ⟨a,rfl⟩:=List.mem_ofFn.mp hq
        exact packet_lt _ _
      next =>simp at hq
    · simp [privateRows] at hq
  · simp only [privateRows] at hq
    split at hq
    next live =>
      split at hq
      next t =>
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
        rcases hq with rfl|rfl <;>exact packet_lt _ _
      next t =>
        split at hq
        next x =>
          simp only [List.mem_singleton] at hq
          subst l
          exact packet_lt _ _
        next x =>
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
          rcases hq with rfl|rfl <;>exact packet_lt _ _
    next =>simp at hq


theorem flat_table_present (mult p split node arg : ℕ) (x : Fin 4→Cell C.fieldBits)
    (active : (x 1).val>0 ∧ (x 2).val%2=0 ∧ (x 3).val<(roster G C.residual C.depth).card)
    (side : Bool) (label : Unit×ℕ) (site : (Q).Site)
    (shape : ((DescentResetTrunkPalette.order G C.residual C.depth).symm ⟨(x 3).val,active.2.2⟩).val=.good side label site)
    (root : ((x 1).val-1,label.2)∈DescentHostDirectory.codes C.residual)
    (levels : ℕ) (measured : DescentRecordedRotorLayers.layers n C.packet C.gain (x 0).val=levels)
    (enough : levels*C.batches≤C.addresses) (l : PrivateLane G) (within : ℕ)
    (hit : (C.flattened G mult levels p node site)[arg]?=some (l,within)) (f : Fin 3) :
    C.flatReg G mult p split node arg (page f).succ x=DescentRetainedRangeDigits.value (l.code G C mult levels p) f:=by
  have bound: l.address<C.addresses:=(C.private_address G mult levels p node arg site l within hit).trans_le enough
  simpa [flatReg,active,shape,root,measured,hit,bound] using PrivateLane.range_field G C mult levels p split within l f

theorem flat_table_outside (mult p split node arg : ℕ) (x : Fin 4→Cell C.fieldBits)
    (active : (x 1).val>0 ∧ (x 2).val%2=0 ∧ (x 3).val<(roster G C.residual C.depth).card)
    (side : Bool) (label : Unit×ℕ) (site : (Q).Site)
    (shape : ((DescentResetTrunkPalette.order G C.residual C.depth).symm ⟨(x 3).val,active.2.2⟩).val=.good side label site)
    (past : (C.flattened G mult (DescentRecordedRotorLayers.layers n C.packet C.gain (x 0).val) p node site)[arg]?=none)
    (f : Fin 8) : C.flatReg G mult p split node arg f x=0:=by
  simp [flatReg,active,shape,past]

end
end Hierarchy.DescentRotorOperandQueryROM.Shape

end OAI
