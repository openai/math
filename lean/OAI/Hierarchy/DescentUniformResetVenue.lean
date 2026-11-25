import OAI.Hierarchy.DescentOriginalPeerRegions
import OAI.Hierarchy.DescentDatedResetVenue

namespace OAI
/-! # Workspace bounds for recorded reset venues over varying schedules -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (t f g reset D drift : ℕ) {ι : ℕ→Type*}
    (index : ℕ→ℕ) (tailCost chosenJ sites age size degree root previous nextM base : ∀h,ι h→ℕ)
    (old : ∀h,ι h→Prior)
local notation "sample" h:arg i:arg => originalSample G op t f g reset (tailCost h i) D drift (chosenJ h i)
  (sites h i) (age h i) (size h i) (degree h i) h (root h i) (previous h i) (2^(root h i)) (nextM h i)
  (base h i) (old h i)
local notation "z" => fun h i=>sample h i
set_option quotPrecheck false in
local notation "p" => fun h i=>(sample h i).output G board D f g op.C op.w

/-- The host, group and packing bounds belong to the same physical reset sample. -/
theorem uniform_venue_room (r : CalendarInputs G board D f g op.C op.w index z)
    (level : ∀ᶠ h:ℕ in atTop,index h≤h)
    (oldH : Bounded fun h i=>(sample h i).sched.hostSize (age h i))
    (newH : Bounded fun h i=>(sample h i).sched.hostSize (age h i+1))
    (oldG : Bounded fun h i=>let a:=sample h i;2^a.sched.groupWidth a.k a.tail a.age)
    (newG : Bounded fun h i=>(sample h i).sched.groupCount (age h i+1))
    (M : Bounded fun h i=>2^(root h i))
    (oldHosts : ∀h i,(old h i).venue.hosts=(sample h i).sched.hostSize (age h i))
    (oldK : ∀h i,(old h i).venue.k=(sample h i).k)
    (priced : Installed p)
    (mask : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,nextM h i≤C*h):
    ResetVenue.ScalarRoom (fun h i=>(p h i).venue):=by
  have previousH:Bounded (fun h i=>(old h i).venue.hosts):=oldH.of_le fun h i=>(oldHosts h i).le
  have blocks:=r.sheets.block.bounded level
  have roster:=r.sheets.shapes.bounded level
  have cap:=((Bounded.const (ι:=ι) (2^g)).mul (r.previousCap.bounded level))
  obtain ⟨C,maskCost⟩:=mask
  have newPitch:Bounded nextM:=(Bounded.pow_of_linear maskCost).of_le fun h i=>Nat.lt_two_pow_self.le
  have cents:∀ᶠ h:ℕ in atTop,∀i,(p h i).venue.census.broadcast*(p h i).receiver.lanes≤1*h:=by
    filter_upwards [priced] with h hit
    intro i
    exact (hit i _ (.inl (by simp [rootUnits]))).trans (by simpa only [Nat.one_mul] using Nat.div_le_self h 2)
  have widths:∀ᶠ h:ℕ in atTop,∀i,
      let v:=p h i
      let L:=v.venue.dense.blocks
      let b:=v.venue.census.bits
      let M₀:=v.receiver.lanes
      b*M₀≤1*h ∧ (b*L)*M₀≤1*h ∧ L*M₀≤1*h ∧ M₀≤1*h ∧
        DescentSignedCableCodec.width v.venue.next.degree v.venue.next.cap*M₀≤1*h:=by
    filter_upwards [priced] with h all_
    intro i
    let v:=p h i
    let L:=2^v.middle.rootDepth
    let M₀:=v.receiver.lanes
    let b:=v.funded.precision
    have use (d:ℕ)(found:d∈v.rootUnits):d*M₀≤1*h:=(all_ i d (.inl found)).trans (by simpa only [Nat.one_mul] using Nat.div_le_self h 2)
    have single:=use (b*L+b) (by simp [rootUnits,b,L])
    have folded:=use ((b+b)*L) (by simp [rootUnits,b,L])
    have scan:=use (L*Nat.clog 2 (L+1)) (by simp [rootUnits,L])
    have nonzero:0<L:=Nat.two_pow_pos _
    have pos:0<Nat.clog 2 (L+1):=Nat.clog_pos (by decide) (by omega)
    have booked:L*M₀≤1*h:=(Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right L pos)).trans scan
    have one:M₀≤1*h:=(Nat.le_mul_of_pos_left M₀ nonzero).trans booked
    exact ⟨(Nat.mul_le_mul_right _ (Nat.le_add_left ..)).trans single,
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right L (Nat.le_add_right ..))).trans folded,
      booked,one,use (DescentSignedCableCodec.width v.venue.next.degree v.venue.next.cap)
        (by simp [rootUnits])⟩
  have paidKey:=widths.mono fun _ h i=>(h i).1
  have paidBlocks:=widths.mono fun _ h i=>(h i).2.1
  have bitBlocks:=widths.mono fun _ h i=>(h i).2.2.1
  have tiny:=widths.mono fun _ h i=>(h i).2.2.2.1
  have signedKey:=widths.mono fun _ h i=>(h i).2.2.2.2
  have originalBlocks:Bounded (fun h i=>2^(old h i).venue.k):=
    blocks.of_le fun h i=>by rw [oldK];exact le_rfl
  have census:DescentFundedCensus.Shape.ScalarRoom (fun h i=>(p h i).venue.census):=
    ⟨roster,previousH,oldG,M,1,cents⟩
  have dense:DescentVenueQuantityPlanes.State.ScalarRoom (fun h i=>(p h i).venue.dense):=
    ⟨roster,previousH,newH,newG,blocks,M,M,⟨1,paidKey⟩,⟨1,paidBlocks⟩⟩
  have actors:DescentVenueQuantityPlanes.State.ScalarRoom (fun h i=>(p h i).venue.actorDims):=
    ⟨roster,previousH,newH,newG,blocks,M,M,
      ⟨1,tiny.mono (fun h w i => by
        change 1 * (p h i).receiver.lanes ≤ 1*h
        simpa only [Nat.one_mul] using w i)⟩,
      ⟨1,bitBlocks.mono (fun h w i => by
        change (1 * (p h i).venue.dense.blocks) * (p h i).receiver.lanes ≤ 1*h
        simpa only [Nat.one_mul] using w i)⟩⟩
  exact ⟨census,dense,actors,originalBlocks,newH,newG,Bounded.const 3,cap,newPitch,M,M,M,
    ⟨1,signedKey⟩,⟨1,paidKey⟩,⟨1,tiny⟩,⟨C,maskCost⟩⟩

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
