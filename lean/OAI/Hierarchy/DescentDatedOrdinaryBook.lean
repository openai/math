import OAI.Hierarchy.DescentDatedOrdinaryBirthArea
import OAI.Hierarchy.DescentPrivateWholeDonorEnd

namespace OAI
/-! # The complete ordinary date from the physical chooser to the private fee meter -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentRawCablePanel.DepotRAM
open ProtocolRAM Computability.VPVNP.BurstRAM
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k i z D wire hist : ℕ} {W : MarkedWorld F d P bits}
variable {prior : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
variable {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} (ticket : OrdinaryLink prior he T c n target)

def ordinaryArea (ℓ b payload unit profile seats : ℕ) : Stage.Dated.Ordinary :=
  let _ := ticket
  ⟨2^ℓ,S.groupCount i,k,b,prior.placement.degree,prior.placement.cap,payload,unit,profile,seats⟩

/-- End of the four-hop owner workspace and deposited fee register. Both its setup and dynamic
subregions follow the actually selected rotation word and all paid matching output banks. -/
def endAddress (old : Bank) (floor ℓ b short payload unit profile seats : ℕ) :=
  let a:=ticket.ordinaryArea ℓ b payload unit profile seats
  ticket.wholeDonorEnd short profile (2^ℓ) payload (a.rotationEnd old floor)

theorem end_relocate (old : Bank) (floor ℓ b short payload unit profile seats : ℕ) :
    ticket.endAddress old floor ℓ b short payload unit profile seats=
      floor+ticket.endAddress old 0 ℓ b short payload unit profile seats := by
  let a:=ticket.ordinaryArea ℓ b payload unit profile seats
  have lift:=a.rotation_add old 0 floor
  simp only [Nat.add_zero] at lift
  unfold endAddress
  rw [ticket.wholeDonorEnd_translate short profile (2^ℓ) payload]
  change a.rotationEnd old floor+_=floor+ticket.wholeDonorEnd short profile (2^ℓ) payload (a.rotationEnd old 0)
  rw [ticket.wholeDonorEnd_translate short profile (2^ℓ) payload (a.rotationEnd old 0),lift,Nat.add_assoc]

theorem floor_le_end (old : Bank) (floor ℓ b short payload unit profile seats : ℕ) :
    floor≤ticket.endAddress old floor ℓ b short payload unit profile seats := by
  rw [end_relocate];exact Nat.le_add_right ..

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
