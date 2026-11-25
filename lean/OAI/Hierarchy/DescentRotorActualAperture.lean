import OAI.Hierarchy.DescentPublicOperandFlatTap

namespace OAI
/-! # The actual donor and physical query of a covered public rotor word -/
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


def earlierCount (src dst : E→Fin (2^n)) (key : E↪Fin N) (req : Mouth n) (e : E) :=
  (Finset.univ.filter (fun j : DescentRotorOperandRanks.At src dst (fun a=>(if req.pin then a.2 else a.1)=req.vertex)=>key j.val<key e)).card

include read miss order mass depth in
/-- Even when the second word crosses an old item, the reported donor is the
unique old item whose chronological interval contains the covered word. -/
theorem public_word (e : E) (selected : attached e) (bpos : 0<C.batches) :
    let first:=earlierCount src dst key req e*C.batches+req.batch
    let amount:=min 2 (Fintype.card fiber*C.batches-first)
    let word:=first+req.within
    if _covered : req.within<amount then
      ∃ donor : fiber,
        earlierCount src dst key req donor.val=word/C.batches ∧
        (∀other : fiber,earlierCount src dst key req other.val=word/C.batches→ other=donor) ∧
        C.tap x side root req=some
          (if req.pin then C.rotorContactAt side ((C.reg x) 0).val root req.vertex
           else C.oldConfig.stemAt side ((C.reg x) 0).val (ids (slot donor.val)),
           if req.pin then word else word%C.batches,amount,req.pin)
    else C.tap x side root req=none :=by
  let first:=earlierCount src dst key req e*C.batches+req.batch
  let amount:=min 2 (Fintype.card fiber*C.batches-first)
  let word:=first+req.within
  let property:=fun p : Fin (2^n)×Fin (2^n)=>(if req.pin then p.2 else p.1)=req.vertex
  let chart:=coords slot src dst (C.endpoints side root x) read miss property
  let carrier : fiber:=⟨e,selected.1⟩
  have atPort (i : fiber) : rank ids ports (slot i.val)=earlierCount src dst key req i.val :=
    (C.physical_port (key:=key) (x:=x) (side:=side) (root:=root) (req:=req) (slot:=slot) read miss order i).1
  have size : (ports).card=Fintype.card fiber:=(C.physical_port (key:=key) (x:=x) (side:=side)
    (root:=root) (req:=req) (slot:=slot) read miss order carrier).2
  have begins : rank ids ports (slot e)*C.batches+req.batch=first :=by rw [atPort carrier]
  have picked:=C.carrier_old board P key x side root req slot read miss order mass depth e selected
  dsimp only
  by_cases yes : req.within<amount
  · rw [dite_eq_left yes]
    have accessible : word<(ports).card*C.batches :=by rw [size];exact fits_aperture yes
    let serial : Fin (ports).card:=⟨word/C.batches,(Nat.div_lt_iff_lt_mul bpos).2 accessible⟩
    let hit:=(rankOrder ids ports).symm serial
    let donor : fiber:=chart.symm hit
    have site:slot donor.val=hit.val:=congrArg Subtype.val (chart.apply_symm_apply hit)
    have correct : rank ids ports hit.val=word/C.batches:=congrArg Fin.val ((rankOrder ids ports).apply_symm_apply serial)
    have payload : select ids ports (word/C.batches)=some (slot donor.val) := by
      rw [site,←correct];exact select_read ids ports hit.property
    have donorValue : earlierCount src dst key req donor.val=word/C.batches:=by rw [←atPort donor,site,correct]
    refine ⟨donor,donorValue,?_,?_⟩
    · intro other same
      apply Subtype.ext
      apply slot.injective
      apply rank_inj ids (chart other).property (chart donor).property
      change rank ids ports (slot other.val) = rank ids ports (slot donor.val)
      rw [atPort other,atPort donor,same,donorValue]
    · have valid : ¬req.within≥min 2 (Fintype.card fiber*C.batches-first) :=not_le.mpr yes
      have sought : select ids ports ((first+req.within)/C.batches)=some (slot donor.val):=payload
      by_cases pin : req.pin = true
      · simp [tap,picked,begins,size,pin,rotorContactAt]
        exact ⟨by simp [amount,pin] at yes; omega, rfl, rfl⟩
      · have negative : req.pin = false := Bool.eq_false_iff.mpr pin
        simp [tap,picked,begins,size,negative,sought]
        exact ⟨by simp [amount,negative] at yes; omega, rfl, rfl⟩
  · rw [dite_eq_right yes]
    have past : min 2 (Fintype.card fiber*C.batches-first)≤req.within:=le_of_not_gt yes
    simp [tap,picked,begins,size]
    intro within available
    exact False.elim (yes (by simp [amount]; exact ⟨within,by omega⟩))

end
end Hierarchy.DescentResetPublicOperandBook.Config

end OAI
