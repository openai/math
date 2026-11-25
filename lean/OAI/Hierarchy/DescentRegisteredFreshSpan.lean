import OAI.Hierarchy.DescentFreshOperandSpan
import OAI.Hierarchy.DescentRegisteredBirthChip

namespace OAI
/-! Source coordinates of the three newborn span columns in the registered W book. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentOrdinaryBorn DescentSIMDLookup DescentRawCablePanel
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (A : v.ArgumentEntry)
    (S : A.InputShape v) (floor : ℕ) (mat : A.Match v floor)
local notation "B₀" => v.bornBook
local notation "fmt₀" => A.clip.venue.socket

/-- The source data here come from the actual depot operand, before the chart's
packing casts. At the selected old edge its fields are produced by
`Stage.issued_birth_donor` at the original source host, block and outgoing ordinal. -/
theorem born_input_span
    (blocks : (B₀).blocks=(fmt₀).blocks) (seats : (B₀).cap=(fmt₀).cap)
    (names : (B₀).names=(fmt₀).names) (units : (B₀).widths=(fmt₀).widths)
    (wide : 0 < (B₀).bits) (demand : (B₀).demand=v.gadget.b)
    (parts : Fin A.clip.venue.hosts→Fin A.clip.venue.groups→DepotRAM.Parts fmt₀)
    (arg : Fin v.vector.operands) (b : Fin (2^v.reference.k)) (s : Fin v.reference.capacity)
    (party : Fin 6) (h : Fin A.clip.venue.hosts) (g : Fin A.clip.venue.groups)
    (a : Profile v.gadget.C) :
    let raw:=DepotRAM.chip fmt₀ (fmt₀).cap A.clip.venue.profile v.gadget.b A.clip.venue.slots (parts h g)
    let source:=chipDonor fmt₀ raw (finProdFinEquiv ((b.cast mat.newBlocks.symm).cast blocks,
      (s.cast mat.newCap.symm).cast seats))
    source.first=true → (∀e,(source.supplyUnits e).val=(a.val e).val+v.gadget.k) →
    ∀f : Fin 3,(A.bornInput v S floor mat parts
      (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) arg) b s party h g).val=
      if arg.val<DescentFreshRoleFields.arity v.gadget (B₀).grain (B₀).scale a party
      then (if f.val=0 then 0 else 1) else 0 := by
  intro raw source first counts f
  let donor:=chipDonor (B₀).format
    (A.nativeChips v S.toBirthShape parts (h.cast S.hosts.symm) (g.cast S.groups.symm))
    (finProdFinEquiv (b.cast mat.newBlocks.symm,s.cast mat.newCap.symm))
  have acquired:=A.native_chip_fields v S.toBirthShape blocks seats names units parts
    (h.cast S.hosts.symm) (g.cast S.groups.symm) (b.cast mat.newBlocks.symm) (s.cast mat.newCap.symm)
  have read : donor.first=source.first ∧ ∀e,(donor.supplyUnits e).val=(source.supplyUnits e).val :=by
    simp [source,raw,donor] at acquired ⊢
    exact acquired
  have result:=selected_span v.gadget (B₀).grain (B₀).scale arg.val (B₀).bits wide a party f donor
    (read.1.trans first) (fun e=>(read.2 e).trans (counts e))
  simp only [bornInput,rowsAt,DescentOperandStateBanks.page,Equiv.symm_apply_apply,Fin.val_cast,demand]
  exact result


/-- Present the native topology window using the registered directory's integer
axes. The cast changes only the finite index and carries the same six subwords. -/
def partsOn {src dst : DepotRAM.Shape} (fmt : src=dst) {H J H' J' : ℕ}
    (own : H'=H) (groups : J'=J) (parts : Fin H→Fin J→DepotRAM.Parts src)
    (h : Fin H') (g : Fin J') : DepotRAM.Parts dst :=
  cast (congrArg DepotRAM.Parts fmt) (parts (h.cast own) (g.cast groups))

theorem donor_on {src dst : DepotRAM.Shape} (fmt : src=dst) {H J H' J' : ℕ}
    (own : H'=H) (groups : J'=J) (parts : Fin H→Fin J→DepotRAM.Parts src)
    (h : Fin H) (g : Fin J) (b : Fin src.blocks) (seat : Fin src.cap)
    (profile demand slots : ℕ) :
    let old:=chipDonor src (DepotRAM.chip src src.cap profile demand slots (parts h g)) (finProdFinEquiv (b,seat))
    let data:=partsOn fmt own groups parts (h.cast own.symm) (g.cast groups.symm)
    let printed:=chipDonor dst (DepotRAM.chip dst dst.cap profile demand slots data)
      (finProdFinEquiv (b.cast (congrArg DepotRAM.Shape.blocks fmt),seat.cast (congrArg DepotRAM.Shape.cap fmt)))
    printed.first=old.first ∧ ∀e,(printed.supplyUnits e).val=(old.supplyUnits e).val := by
  subst dst; subst H'; subst J'
  exact ⟨rfl,fun _=>rfl⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
