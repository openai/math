import OAI.Hierarchy.DescentDatedPrimitiveUpdate

namespace OAI
/-! The primitive update is a function of the public dated shape and earlier physical bank addresses. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentOrdinaryPrimitiveCheckpoint ProtocolRAM DescentKernelHistory
open ThreeFlat.Routing
noncomputable section
variable {F P Q : Type} [Field F]

@[ext] structure PrimitiveDevice (F : Type) [Field F] where
  gadget : PoweredGadget F
  config : DescentOrdinaryPalette.Configuration
  shape : Layout
  births : DescentOrdinaryBorn.Chart
  floor : ℕ
  chip : Bank
  past : ℕ→Bank
  origins : ℕ→Bank
  halo : Bank

namespace PrimitiveDevice
variable (D : PrimitiveDevice F)
def input : D.shape.Inputs where
  previous x:=D.past x.val
  newborn t:=if hi:t.val<DescentOrdinaryPaletteBirth.fields D.births then
    DescentOrdinaryPaletteBirth.bank D.births D.floor ⟨t.val,hi⟩ else ⟨0,0⟩
  origin x:=D.origins x.val
  halo:=D.halo
def phase (w : ℕ) :=
  (DescentOrdinaryPaletteBirth.phase D.gadget D.config.seedWidth D.config.grainLimit D.config.rotor D.births D.chip D.floor w).seq
    (D.shape.phase (DescentOrdinaryPaletteBirth.roof D.births D.floor) D.input w)
end PrimitiveDevice

namespace PhysicalOrdinary
variable (v : PhysicalOrdinary F P) (floor : ℕ) (A : ArgumentEntry v)

def primitiveDevice : PrimitiveDevice F where
  gadget:=v.gadget
  config:=v.palette
  shape:=v.paletteShape
  births:=v.bornBook
  floor:=v.operandEnd floor
  chip:=A.chipBank v floor
  past n:=if h:n<A.previous.blocks then A.labels v floor ⟨n,h⟩ else ⟨0,0⟩
  origins n:=if h:n<v.vector.radix then v.originBank floor ⟨n,h⟩ else ⟨0,0⟩
  halo:=(A.ports v floor).roster

theorem primitive_device (match_ : A.Match v floor) (radix : v.vector.radix=2^v.reference.k) (w : ℕ) :
    v.primitiveUpdate floor A match_ radix w=(v.primitiveDevice floor A).phase w:=by
  have addr : (v.primitiveDevice floor A).input=v.primitiveSources floor A match_ radix:=by
    change Layout.Inputs.mk _ _ _ _=Layout.Inputs.mk _ _ _ _
    congr 1
    · funext x
      have hx : x.val<A.previous.blocks:=by rw [match_.oldBlocks];exact x.isLt
      simp only [primitiveDevice, dite_eq_left hx]
      exact congrArg (A.labels v floor) (Fin.ext (Fin.val_cast match_.oldBlocks.symm x).symm)
    · funext x
      have hx : x.val < DescentOrdinaryPaletteBirth.fields v.bornBook := by
        change x.val < v.bornBook.blocks * v.bornBook.cap * 6
        rw [match_.newBlocks, match_.newCap]
        exact x.isLt
      change (if hi : x.val < DescentOrdinaryPaletteBirth.fields v.bornBook then _ else _) = _
      rw [dite_eq_left hx]
      have count : (v.primitiveDevice floor A).shape.fields = DescentOrdinaryPaletteBirth.fields v.bornBook := by
        change 2^v.reference.k * v.reference.capacity * 6 = v.bornBook.blocks * v.bornBook.cap * 6
        rw [match_.newBlocks, match_.newCap]
      exact congrArg (DescentOrdinaryPaletteBirth.bank v.bornBook (v.operandEnd floor))
        (Fin.ext (Fin.val_cast count x).symm)
    · funext x
      have hx : x.val<v.vector.radix:=by rw [radix];exact x.isLt
      simp only [primitiveDevice, dite_eq_left hx]
      exact congrArg (v.originBank floor) (Fin.ext (Fin.val_cast radix.symm x).symm)
  unfold primitiveUpdate PrimitiveDevice.phase
  rw [addr]
  rfl

theorem primitive_equal (v' : PhysicalOrdinary F Q) (floor' : ℕ) (A' : ArgumentEntry v')
    (match_ : A.Match v floor) (other : A'.Match v' floor')
    (radix : v.vector.radix=2^v.reference.k) (radix' : v'.vector.radix=2^v'.reference.k)
    (sameG : v.gadget=v'.gadget) (sameC : v.palette=v'.palette) (sameShape : v.paletteShape=v'.paletteShape)
    (sameBirth : v.bornBook=v'.bornBook) (start : v.operandEnd floor=v'.operandEnd floor')
    (chip : A.chipBank v floor=A'.chipBank v' floor')
    (oldBlocks : A.previous.blocks=A'.previous.blocks) (old : ∀i,A.labels v floor i=A'.labels v' floor' (i.cast oldBlocks))
    (nBlocks : v.vector.radix=v'.vector.radix) (stamps : ∀i,v.originBank floor i=v'.originBank floor' (i.cast nBlocks))
    (ports : (A.ports v floor).roster=(A'.ports v' floor').roster) (w : ℕ) :
    v.primitiveUpdate floor A match_ radix w=v'.primitiveUpdate floor' A' other radix' w:=by
  rw [primitive_device,primitive_device]
  apply congrArg (fun (d:PrimitiveDevice F)=>d.phase w)
  apply PrimitiveDevice.ext sameG sameC sameShape sameBirth start chip
  · funext n
    by_cases h:n<A.previous.blocks
    · simp only [primitiveDevice, dite_eq_left h, dite_eq_left (oldBlocks ▸ h)]
      exact (old ⟨n,h⟩).trans (congrArg (A'.labels v' floor') (by apply Fin.ext; simp only [Fin.val_cast]))
    · simp only [primitiveDevice,dite_eq_right h,dite_eq_right (oldBlocks ▸ h)]
  · funext n
    by_cases h:n<v.vector.radix
    · simp only [primitiveDevice, dite_eq_left h, dite_eq_left (nBlocks ▸ h)]
      exact (stamps ⟨n,h⟩).trans (congrArg (v'.originBank floor') (by apply Fin.ext; simp only [Fin.val_cast]))
    · simp only [primitiveDevice,dite_eq_right h,dite_eq_right (nBlocks ▸ h)]
  · exact ports

end PhysicalOrdinary
end
end Hierarchy.DescentSixParty.Chronology

end OAI
