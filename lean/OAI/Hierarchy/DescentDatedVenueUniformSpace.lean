import OAI.Hierarchy.DescentDatedVenueBookRate

namespace OAI
/-! # One exponent for the native three-channel venue and its public directory -/
namespace Hierarchy.DescentSixParty.StageVenueTail.Date
open DescentDatedAddressBook Filter
noncomputable section

structure NativeCaps (d : Date) (h : ℕ) : Prop where
  blocks : 2^d.k≤2^h
  hosts : d.hosts≤2^(4*h)
  groups : d.groups≤2^h
  degree : d.degree≤2^h
  cap : d.cap≤2^h
  issued : d.lanes≤h
  signed : d.signedLanes≤h
  alive : d.aliveLanes≤h
  paid : d.paidLanes≤h
  signedWidth : DescentSignedCableCodec.width d.degree d.cap*d.signedLanes≤h
  paidWidth : d.paidBits*d.paidLanes≤h

theorem uniform_space : ∃C : ℕ,∀ᶠ h : ℕ in atTop,∀d : Date,NativeCaps d h→d.endAddress 0≤(2^h)^C :=by
  let ι (h : ℕ):={d : Date // NativeCaps d h}
  let a (h) (i : ι h):=i.val
  have exp {f : ∀h,ι h→ℕ} (b : ∀h i,f h i≤2^h) : Bounded f :=
    ⟨1,Eventually.of_forall (fun h i=>by simpa only [Nat.one_mul] using b h i)⟩
  have small {f : ∀h,ι h→ℕ} (b : ∀h i,f h i≤h) : Bounded f :=exp (fun h i=>(b h i).trans Nat.lt_two_pow_self.le)
  have width {f : ∀h,ι h→ℕ} (b : ∀h i,f h i≤h) : ∃K : ℕ,∀ᶠ h : ℕ in atTop,∀i,f h i≤K*h :=
    ⟨1,Eventually.of_forall (fun h i=>by simpa only [Nat.one_mul] using b h i)⟩
  have room : ScalarRoom a:=⟨exp (fun _ i=>i.property.blocks),⟨4,Eventually.of_forall (fun _ i=>i.property.hosts)⟩,
    exp (fun _ i=>i.property.groups),exp (fun _ i=>i.property.degree),exp (fun _ i=>i.property.cap),
    small (fun _ i=>i.property.issued),small (fun _ i=>i.property.signed),small (fun _ i=>i.property.alive),
    small (fun _ i=>i.property.paid),width (fun _ i=>i.property.signedWidth),width (fun _ i=>i.property.paidWidth),
    width (fun _ i=>i.property.alive),width (fun _ i=>i.property.issued)⟩
  obtain ⟨C,next⟩:=extent_rate a room
  refine ⟨C,?_⟩
  filter_upwards [next] with h bound
  intro d caps
  exact (bound (⟨d,caps⟩ : ι h)).trans_eq (by rw [←pow_mul,Nat.mul_comm])

end
end Hierarchy.DescentSixParty.StageVenueTail.Date

end OAI
