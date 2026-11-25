import OAI.Hierarchy.DescentResetPublicOperandBook

namespace OAI
/-! # The actual old carrier of each public argument of a rotor tap -/
namespace Hierarchy.DescentResetPublicOperandBook.Config
open DescentSIMDLookup DescentFallbackItemSelect DescentDenseHostOrder DescentResetHostSize
open DescentResetLocalRoster DescentRotor DescentBaseProfile DescentRotorOperandQueryROM.Shape
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F E : Type} [Field F] [Fintype E] {n h u N : ℕ} (board : NonlinearExpanders.Graph n h)
    (C : Config) {hp : 0<C.packetWidth} {src dst : E→Fin (2^n)} {pay : ℝ}
    (P : BaseCircuit F board C.multiplicity C.packetWidth u hp src dst pay) (key : E↪Fin N)
    (x : C.Data n) (side : Bool) (root : code C.residual) (req : Mouth n)
    (slot : E↪Fin C.oldConfig.count)
    (read : ∀e,C.endpoints side root x (slot e)=some (src e,dst e))
    (miss : ∀j,(¬∃e,slot e=j)→C.endpoints side root x j=none)
    (order : ∀a b,before (C.oldItem x side) (slot a) (slot b) ↔ key a<key b)
    (mass : C.traffic x side root=matrixOfBundles src dst)
    (depth : DescentRecordedRotorLayers.layers n C.packetWidth C.gain ((C.reg x) 0).val=P.layers)
local notation "ord" => Ordered.orderedAddress key src dst hp
local notation "rank₀" e:arg => (Ordered.ordinal key src dst (src e,dst e) ((Ordered.cells src dst e).2)).val
local notation "attached" e:arg => ((if req.pin then dst e else src e)=req.vertex ∧
  (P.choose (ord e).1).val=req.layer ∧ (ord e).2.val=req.digit)

include read miss order mass depth in
theorem accepts_old (e : E) : C.accepts x side root req (slot e)=true ↔ attached e := by
  have serial:=DescentRotorOperandRanks.serial slot key (C.oldItem x side) src dst
    (C.endpoints side root x) read miss order e
  unfold accepts
  simp only [read e,Option.any,decide_eq_true_eq]
  rw [depth,mass,serial]
  exact matches_iff board P key req e

include read miss order mass depth in
theorem carrier_old (e : E) (atTap : attached e) : C.carrier x side root req=some (slot e) := by
  have eqn:=accepts_old board C P key x side root req slot read miss order mass depth
  have existsSlot : ∃j,C.accepts x side root req j=true:=⟨slot e,(eqn e).mpr atTap⟩
  rw [carrier,dite_eq_left existsSlot]
  apply congrArg some
  have picked:=existsSlot.choose_spec
  by_cases actual : ∃t,slot t=existsSlot.choose
  · obtain ⟨t,ht⟩:=actual
    rw [←ht] at picked ⊢
    exact congrArg slot (matches_unique board P key req t e
      ((matches_iff board P key req t).mpr ((eqn t).mp picked)) ((matches_iff board P key req e).mpr atTap))
  · have reject (j : Fin C.oldConfig.count) (absent : C.endpoints side root x j=none) :
        C.accepts x side root req j=false := by
      simp only [accepts,absent,Option.any_none]
    exact False.elim (Bool.false_ne_true ((reject _ (miss _ actual)).symm.trans picked))

include read miss order mass depth in
theorem carrier_empty (padding : ∀e,¬attached e) : C.carrier x side root req=none := by
  apply dite_eq_right
  rintro ⟨j,yes⟩
  by_cases hit : ∃e,slot e=j
  · obtain ⟨e,rfl⟩:=hit
    exact padding e ((accepts_old board C P key x side root req slot read miss order mass depth e).mp yes)
  · simp [accepts,miss j hit] at yes

end
end Hierarchy.DescentResetPublicOperandBook.Config

end OAI
