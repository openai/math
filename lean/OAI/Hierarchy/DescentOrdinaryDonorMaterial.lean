import OAI.Hierarchy.DescentOrdinaryRawRankFields
import OAI.Hierarchy.DescentOrdinarySignedPaths
import OAI.Hierarchy.DescentOrdinaryDonorTrims
import OAI.Hierarchy.DescentOrdinaryRawMass
import OAI.Hierarchy.DescentOrdinaryIssuedTicket

namespace OAI
/-! Local endpoint and multiplicity digits read before the signed-source rendezvous. -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Material
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentSharedCableNames DescentHaloWalkRAM
open DescentSixParty.Chronology DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (s : Shape) {w H J M : ℕ}

variable (u : Setup)
def roles := s.blocks*(s.cap*11)
abbrev Field := Fin 8
def seatIndex : Seat s ≃ Fin (roles s) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv
def page (f : Field) (seat : Seat s) : Fin (8*roles s) :=finProdFinEquiv (f,seatIndex s seat)

/-- The eighth column is the within-donor ticket, before attaching the reverse rank. -/
def observations (v : Parts s) (seat : Seat s) : Field→ℕ :=
  let x:=seat.1
  let t:=seat.2.1
  let role:=seat.2.2
  let d:=seatDonor s u.profile u.motifWidth u.slots v x t
  let mass:=liveMass (report u.oldBits u.gain u.slots d role)
  let left:=atSeat s u.profile u.motifWidth u.slots false v x t role
  let right:=atSeat s u.profile u.motifWidth u.slots true v x t role
  let lo:=(roleLow u.oldBits u.gain u.slots false d role).val
  let hi:=(roleLow u.oldBits u.gain u.slots true d role).val
  let upper:=decide (ranked s v.chart right*u.hostPitch+hi<ranked s v.chart left*u.hostPitch+lo)
  if mass=0 ∨ left.val=0 ∨ right.val=0 then fun _=>0 else
    ![left.val,right.val,lo,hi,upper.toNat,mass,1,(x.val*s.cap+t.val)*11+role.val]

def law (i : ℕ) (v : Cell (totalBits s)) : Cell u.fieldBits :=
  if h : i<8*roles s then
    let j : Field × Fin (roles s):=finProdFinEquiv.symm ⟨i,h⟩
    (observations s u (separate s v) ((seatIndex s).symm j.2) j.1:ℕ)
  else 0

theorem decoded (f : Field) (seat : Seat s) (v : Parts s) :
    law s u (page s f seat).val (combine s v)=(observations s u v seat f:ℕ) :=by
  rw [law, dite_eq_left (page s f seat).isLt]
  simp only [page, Fin.eta, Equiv.symm_apply_apply, separate_combine]

def cells (H J M base : ℕ) (f : Field) (seat : Seat s) : Bank :=
  ⟨RoleScans.home (totalBits s) H J M (8*roles s) base+(page s f seat).val*(H*chunks J M),
    Nat.clog 2 (H*chunks J M)⟩

def phase (H J M w base : ℕ) (old : Bank) : NativePhase w :=
  let n:=8*roles s
  ⟨RoleScans.cpu (law s u) H J M w base n old,RoleScans.ticks (totalBits s) H J M n,
    RoleScans.image (law s u) H J M base n old,
    cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@ProtocolRAM.program_cheap _ _)⟩

variable (base : ℕ) (old : Bank) (m : Memory w) (lower : old.base+old.size≤base)
    (capacity : H*chunks J M≤old.size) (pay : M*max (totalBits s) u.fieldBits≤w/2)
    (room : RoleScans.limit (totalBits s) H J M base (8*roles s)<2^w)

include lower capacity pay room in
theorem any :
    let stage:=phase s u H J M w base old
    stage.Runs m ∧ (∀x,x<base ∨ RoleScans.limit (totalBits s) H J M base (8*roles s)≤x→stage.image m x=m x) :=by
  intro stage
  have ok:=RoleScans.any_run (law s u) base (8*roles s) old m lower capacity pay room
  exact ⟨ok.1,ok.2.1⟩

include lower capacity pay room in
theorem emitted (prior : Fin H→Fin J→Parts s) (earlier : Reads old (fun h g=>combine s (prior h g)) M m)
    (f : Field) (seat : Seat s) :
    Reads (cells s H J M base f seat)
      (fun h g=>(observations s u (prior h g) seat f:Cell u.fieldBits)) M ((phase s u H J M w base old).image m) :=by
  intro p
  have rd := RoleScans.read (law s u) base (8*roles s) old m lower capacity pay room _ earlier (page s f seat) p
  simp only [decoded] at rd
  exact rd

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Material

end OAI
