import OAI.Hierarchy.DescentDatedOrdinaryBook

namespace OAI
/-! # Address rate for the selected ordinary rotation and original donor-meter suffix -/
namespace Hierarchy
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentRawCablePanel.DepotRAM DescentDatedAddressBook
open ProtocolRAM Filter
noncomputable section
namespace DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary

def donorWords (a : Ordinary) :=
  let P:=(a.D+1)^4
  let B:=5+(2^a.k*(2*a.cap)+(a.D+1+1))
  18*(a.H*P)+26*(a.H*(a.G+a.payload))+2*P*((a.payload+1)*(P+1))+
    (2*(2*B+3+2^(a.k+1))+3)*2^(a.payload/2)+32

theorem donor_width_rate {ι : ℕ→Type*} (a : ∀h,ι h→Ordinary) (b : ScalarRoom a) :
    DescentDatedAddressBook.Bounded (fun h i=>(a h i).donorWords) := by
  have H:=b.hosts;have G:=b.groups;have D:=b.degree;have r:=b.radix;have cap:=b.wires
  obtain ⟨C,hw⟩:=b.payload
  have pages:=DescentDatedAddressBook.Bounded.pow_of_linear (K:=C) hw
  have pay : DescentDatedAddressBook.Bounded (fun h i=>(a h i).payload) := pages.of_le fun _ _=>Nat.lt_two_pow_self.le
  have half : DescentDatedAddressBook.Bounded (fun h i=>2^((a h i).payload/2)) := pages.of_le fun _ _=>Nat.pow_le_pow_right (by decide) (Nat.div_le_self ..)
  have rad : DescentDatedAddressBook.Bounded (fun h i=>2^((a h i).k+1)) := by simpa only [Nat.pow_succ] using r.mul (DescentDatedAddressBook.Bounded.const 2)
  dsimp only [donorWords]
  repeat' first | assumption | apply DescentDatedAddressBook.Bounded.add | apply DescentDatedAddressBook.Bounded.mul | apply DescentDatedAddressBook.Bounded.pow | apply DescentDatedAddressBook.Bounded.const

end DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary

namespace DescentSixParty.Chronology.OrdinaryLink
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k i z D wire hist : ℕ} {W : MarkedWorld F d P bits}
variable {prior : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
variable {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} (ticket : OrdinaryLink prior he T c n target)

theorem concrete_extent (old : Bank) (floor ℓ b short payload unit profile seats : ℕ) :
    let a:=ticket.ordinaryArea ℓ b payload unit profile seats
    ticket.endAddress old floor ℓ b short payload unit profile seats ≤
      floor+a.rotationEnd old 0+a.donorWords := by
  intro a
  let M:=lanes payload (ticket.installedDonorWidth short profile)
  let P₀:=(prior.placement.degree+1)^4
  have lanes : M≤payload := Nat.div_le_self ..
  have chunks' : chunks (S.groupCount i) M≤S.groupCount i+payload :=
    ((Nat.div_le_self ..).trans (Nat.sub_le ..)).trans (Nat.add_le_add_left lanes _)
  have first:=a.rotation_add old 0 floor
  simp only [Nat.add_zero] at first
  have physical:=ticket.wholeDonorEnd_bound short profile (2^ℓ) payload (a.rotationEnd old floor)
  change ticket.endAddress old floor ℓ b short payload unit profile seats≤
    a.rotationEnd old floor+18*(2^ℓ*P₀)+26*(2^ℓ*chunks (S.groupCount i) M)+
    2*P₀*((M+1)*(P₀+1))+
    (2*(2*(5+(2^k*(2*prior.placement.cap)+(prior.placement.degree+1+1)))+3+2^(k+1))+3)*2^(payload/2)+32 at physical
  change _≤floor+a.rotationEnd old 0+(18*(2^ℓ*P₀)+26*(2^ℓ*(S.groupCount i+payload))+
    2*P₀*((payload+1)*(P₀+1))+
    (2*(2*(5+(2^k*(2*prior.placement.cap)+(prior.placement.degree+1+1)))+3+2^(k+1))+3)*2^(payload/2)+32)
  rw [first] at physical
  have more:=Nat.mul_le_mul_left 26 (Nat.mul_le_mul_left (2^ℓ) chunks')
  have many:=Nat.mul_le_mul_left (2*P₀) (Nat.mul_le_mul_right (P₀+1) (Nat.add_le_add_right lanes 1))
  omega

end DescentSixParty.Chronology.OrdinaryLink
end
end Hierarchy

end OAI
