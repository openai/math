import OAI.Hierarchy.DescentOrdinaryMountedBirth

namespace OAI
/-! # Material source words at every reference in the dated ordinary directory -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony DescentPackedZip DescentOrdinaryBorn
open DescentSIMDLookup DescentOrdinaryReferenceInputs DescentRawCablePanel
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (A : ArgumentEntry v)

/-- The two source directories specify the same host and group enumerations
and the same bit widths. Each equality concerns only public integer fields. -/
structure InputShape extends A.BirthShape v where
  prevGroups : A.clip.venue.groups=A.previous.groups
  previousBits : DescentOrdinaryPriorRetile.digits A.previous=v.reference.bits*v.reference.oldNodes
  birthBits : v.bornBook.bits=v.reference.bits

variable (S : A.InputShape v) (floor : ℕ) («matching» : A.Match v floor)
local notation "H₀" => A.clip.venue.hosts
local notation "G₀" => A.clip.venue.groups
local notation "D₀" => A.directory v floor «matching»
local notation "old₀" => (fun (b : Fin (2^v.reference.k))=>Fin.cast «matching».oldBlocks.symm b)
local notation "new₀" => (fun (b : Fin (2^v.reference.k))=>Fin.cast «matching».newBlocks.symm b)
local notation "fa₀" => ((finProdFinEquiv : Fin 7×Fin v.vector.operands ≃ Fin v.vector.pageCount).symm)

def oldField (p : Fin v.vector.pageCount) (valid : (fa₀ p).2.val<A.previous.operands) :=
  page (fa₀ p).1 (⟨(fa₀ p).2.val,valid⟩ : Fin A.previous.operands)

def oldInput
    (old : Pages A.previous.operands→Fin A.previous.blocks→Fin A.previous.hosts→Fin A.previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits A.previous))
    (p : Fin v.vector.pageCount) (b : Fin (2^v.reference.k)) :=
  rowsAt (H:=H₀) rfl S.prevGroups S.previousBits
    (if valid : (fa₀ p).2.val<A.previous.operands then
      DescentOrdinaryPriorPad.extend H₀ (old (A.oldField v p valid) (old₀ b))
     else fun _ _=>0)

def bornInput (parts : Fin H₀→Fin G₀→DepotRAM.Parts A.clip.venue.socket) (p : Fin v.vector.pageCount)
    (b : Fin (2^v.reference.k)) (t : Fin v.reference.capacity) (j : Fin 6) :=
  rowsAt S.hosts.symm S.groups.symm S.birthBits (fun h g=>
    component v.bornBook.bits (pointerAt v.bornBook.demand v.bornBook.grain v.bornBook.scale
      (chipDonor v.bornBook.format (A.nativeChips v S.toBirthShape parts h g)
        (finProdFinEquiv (new₀ b,Fin.cast «matching».newCap.symm t))) j (fa₀ p).2.val) (fa₀ p).1)

include «matching» in
private theorem working : v.vector.lanes*v.vector.radix=A.clip.working:=by
  rw [«matching».post,«matching».radix]
  rfl

theorem old_bank (p : Fin v.vector.pageCount) (q : Fin v.vector.lows) (b : Fin (2^v.reference.k)) :
    ((D₀).refs p q).previous b =
      if valid : (fa₀ p).2.val<A.previous.operands then
        DescentOrdinaryPriorPad.bank A.previous H₀ A.clip.working (A.priorStart v floor)
          (old₀ b) (A.oldField v p valid)
      else DescentOrdinaryPriorPad.zero A.previous H₀ A.clip.working (A.priorStart v floor) :=by
  change (if valid : (fa₀ p).2.val<A.previous.operands then
    DescentOrdinaryPriorPad.bank A.previous H₀ (v.vector.lanes*v.vector.radix) (A.priorStart v floor)
      (old₀ b) (A.oldField v p valid)
    else DescentOrdinaryPriorPad.zero A.previous H₀ (v.vector.lanes*v.vector.radix) (A.priorStart v floor))=_
  rw [A.working v floor «matching»]

theorem selected_operands {w} (m : Memory w) (safe : A.Room v floor w) (space : v.vectorStart floor<2^w)
    (old : Pages A.previous.operands→Fin A.previous.blocks→Fin A.previous.hosts→Fin A.previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits A.previous))
    (parts : Fin H₀→Fin G₀→DepotRAM.Parts A.clip.venue.socket)
    (previousPitch : 0<A.previous.lanes) (panelPitch : 0<A.clip.panelPitch)
    (lower : ∀x p,(previousBank A.previous A.previousBase x p).Fits w (v.signedEnd floor))
    (previous : ∀x p,Reads (previousBank A.previous A.previousBase x p) (old p x) A.previous.lanes m)
    (panel : Reads A.venue.panel (fun h g=>DepotRAM.combine A.clip.venue.socket (parts h g)) A.clip.panelPitch m)
    (p : Fin v.vector.pageCount) (q : Fin v.vector.lows) :
    let dst:=A.mountedTape v floor m
    (∀x,Reads (((D₀).refs p q).previous x) (A.oldInput v S floor «matching» old p x) v.reference.lanes dst) ∧
    (∀x t j,Reads (((D₀).refs p q).birth x t j) (A.bornInput v S floor «matching» parts p x t j) v.reference.lanes dst) :=by
  intro dst
  constructor
  · intro x
    rw [A.old_bank v floor «matching» p q x]
    unfold oldInput
    apply reads_at rfl S.prevGroups S.previousBits «matching».refPitch
    by_cases valid : (fa₀ p).2.val<A.previous.operands
    · simp only [dite_eq_left valid]
      exact A.mounted_old v floor m safe «matching» space (old₀ x) (A.oldField v p valid) _
        previousPitch (lower _ _) (previous _ _)
    · simp only [dite_eq_right valid]
      exact A.mounted_zero v floor m safe «matching» space _
  · intro x t j
    apply reads_at S.hosts.symm S.groups.symm S.birthBits («matching».refPitch.trans «matching».bornPitch.symm)
    exact A.mounted_birth v S.toBirthShape floor m safe «matching» space panelPitch parts panel
      (new₀ x) (Fin.cast «matching».newCap.symm t) j (Fin.cast «matching».newArgs.symm (fa₀ p).2) (fa₀ p).1

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
