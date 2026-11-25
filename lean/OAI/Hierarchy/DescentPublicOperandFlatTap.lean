import OAI.Hierarchy.DescentPublicOperandCarrier
import OAI.Hierarchy.DescentOperandApertureOrder
import OAI.Hierarchy.DescentFallbackPhysicalColumns

namespace OAI
/-! # The public rotor lookup addresses the actual chronological socket p-word -/
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

def rotorContactAt (side : Bool) (cap : ℕ) (root : code C.residual) (v : Fin (2^n)) : ℕ :=
  let sh:=C.oldConfig.toShape
  directed (total sh cap) side (stemSlots sh cap+1+
    ((finTwoEquiv.symm side).val*(rootSlots C.residual (2^n)*sockets sh)+
      (rootId C.residual (2^n) (.inl root)).val*sockets sh+v.val))

include read miss order in
theorem physical_port (e : fiber) :
    rank ids ports (slot e.val)=(Finset.univ.filter (fun i : fiber=>key i.val<key e.val)).card ∧
    (ports).card=Fintype.card fiber :=
  ⟨rank_exact slot key ids src dst _ read miss order _ e,count_exact slot src dst _ read miss _⟩

include read miss order mass depth in
theorem printed_tap (e : E) (selected : attached e) (bpos : 0<C.batches) :
    let first:=rank ids ports (slot e)*C.batches+req.batch
    let count:=min 2 ((ports).card*C.batches-first)
    if allowed : req.within<count then
      let word:=first+req.within
      let donor:=(rankOrder ids ports).symm
        ⟨word/C.batches,(Nat.div_lt_iff_lt_mul bpos).2 (fits_aperture allowed)⟩
      if req.pin then C.tap x side root req=some
        (C.rotorContactAt side ((C.reg x) 0).val root req.vertex,word,count,true)
      else C.tap x side root req=some
        (C.oldConfig.stemAt side ((C.reg x) 0).val (ids donor.val),word%C.batches,count,false)
    else C.tap x side root req=none :=by
  let first:=rank ids ports (slot e)*C.batches+req.batch
  let count:=min 2 ((ports).card*C.batches-first)
  have carrier:=carrier_old board C P key x side root req slot read miss order mass depth e selected
  dsimp only
  by_cases allowed:req.within<count
  · rw [dite_eq_left allowed]
    have ins : first+req.within<(ports).card*C.batches := fits_aperture allowed
    have picked:=(selected_word ids ports bpos ins).1
    have ok : req.within ≤ 1 ∧ req.within + first < (ports).card * C.batches := by
      simp [count] at allowed
      omega
    cases pin:req.pin
    · simp [tap,carrier,first,pin,picked]
      exact ok
    · simp [tap,carrier,pin,rotorContactAt]
      exact ok
  · rw [dite_eq_right allowed]
    simp [tap,carrier]
    intro within available
    exact False.elim (allowed (by simp [count,first]; exact ⟨within,by omega⟩))

include read miss order mass depth in
theorem missing_tap (padding : ∀e,¬attached e) : C.tap x side root req=none :=by
  simp [tap,carrier_empty board C P key x side root req slot read miss order mass depth padding]

end
end Hierarchy.DescentResetPublicOperandBook.Config

end OAI
