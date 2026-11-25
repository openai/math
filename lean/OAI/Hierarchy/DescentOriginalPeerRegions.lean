import OAI.Hierarchy.DescentNamedSheetRoom
import OAI.Hierarchy.DescentNamedFrontDimensions
import OAI.Hierarchy.DescentScheduledContactRoom

namespace OAI
/-! # The original public schedules pay the full contact, peer and private-mask address ranges -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
variable {F : Type} [Field F] (G:PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
variable (op : RotorSpec) (t f g reset τ D drift B : ℕ) {ι : ℕ→Type*}
variable (sites age size degree root previous nextM base : ∀h,ι h→ℕ) (old : ∀h,ι h→Prior)
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg i:arg => stageNumbers G t (J_ h) f g reset (sites h i) (tail τ (J_ h))
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "a_" h:arg i:arg => originalSample G op t f g reset τ D drift (J_ h) (sites h i) (age h i)
  (size h i) (degree h i) h (root h i) (previous h i) (2^(root h i)) (nextM h i) (base h i) (old h i)
set_option quotPrecheck false in
local notation "out_" => fun h i=>(a_ h i).output G board D f g op.C op.w

theorem original_inputs (positive : 0<B) (branch : G.b≤2^(capRate G t g)) (bound : ℕ)
    (short : ∀h i,size h i≤h) (degrees : ∀h i,degree h i≤bound) :
    CalendarInputs G board D f g op.C op.w (fun h=>J_ h) (fun h i=>a_ h i) :=by
  let E:=localExponent G board op t f g reset D
  have specs:=original_fields G board op t f g reset τ D drift B positive branch bound
  have width : ∀ᶠ h:ℕ in atTop,∀i,(a_ h i).LocalAt G board D f g op.C op.w (J_ h) E :=
    specs.mono fun h area i=>area (sites h i) (age h i) (size h i) (degree h i) (root h i)
      (previous h i) (2^(root h i)) (nextM h i) (base h i) (old h i) (short h i) (degrees h i)
  refine {
    sheets := CandidateSheets.scale_at board D f g G t reset τ B sites age (fun h i=>2^(root h i))
    previousCap := ⟨E,width.mono fun h w i=>(w i).cap⟩
    dimension := ⟨E,width.mono fun h w i=>(w i).dim⟩
    controls := ⟨E,width.mono fun h w i=>(w i).root⟩
    rootOutput := ⟨E,width.mono fun h w i=>(w i).primaries⟩
    funded := ⟨E,width.mono fun h w i=>(w i).quantities⟩
    paid := ⟨E,width.mono fun h w i=>(w i).paid⟩
    coefficient := ⟨E,width.mono fun h w i=>(w i).coefficient⟩
    primitive := ⟨E,width.mono fun h w i=>(w i).token⟩
    «arguments» := ⟨E,width.mono fun h w i=>(w i).arguments⟩
    nodes := ⟨E,width.mono fun h w i=>(w i).nodes⟩
    fibres := ?_ }
  intro h i
  let S:=S_ h i
  let k:=k_ h
  let c:=S.groupWidth k (tail τ (J_ h)) (age h i)
  let shift:=S.retainedExponent G k (tail τ (J_ h)) drift (degree h i) (size h i) (age h i) h
  have cut:shift≤c:=Nat.min_le_left ..
  change 2^(c-shift+(shift+k)-c)=2^k
  congr 1;omega

theorem original_region_rooms (positive : 0<B) (branch : G.b≤2^(capRate G t g)) (bound : ℕ)
    (short : ∀h i,size h i≤h) (degrees : ∀h i,degree h i≤bound)
    (seed : Bounded sites) (earlier : ∀h i,age h i≤(S_ h i).length)
    (next : ∀h i,root h i≤(S_ h i).groupWidth (k_ h) (tail τ (J_ h)) (age h i+1))
    (priced : Installed (out_)) :
    CandidateFront.ScalarRoom (fun h i=>(out_ h i).front) ∧
    DescentContactOutputShape.Shape.ScalarRoom (fun h i=>(out_ h i).contactShape) ∧
    DescentPrivateMaskDeck.Shape.ScalarRoom (fun h i=>(out_ h i).privateShape) ∧
    CandidateSheets.ScalarRoom (fun h i=>(out_ h i).sheets) ∧ ActorSetup.ScalarRoom (fun h i=>(out_ h i).actor) :=by
  let p:=out_
  let z:=fun h i=>a_ h i
  have r:=original_inputs G board op t f g reset τ D drift B sites age size degree root previous nextM base
    old positive branch bound short degrees
  have axes:=schedule_space G t f g reset τ B sites age seed earlier
  have level : ∀ᶠ h:ℕ in atTop,J_ h≤h :=
    Eventually.of_forall fun h=>(Nat.div_le_self ..).trans (Nat.log_le_self 2 h)
  have M : Bounded (fun h i=>2^(root h i)) :=axes.newGroup.of_le fun h i=>
    (Nat.pow_le_pow_right (by decide) (next h i)).trans ((S_ h i).group_power (k:=k_ h) rfl rfl _).le
  have oldG : Bounded (fun h i=>2^(S_ h i).groupWidth (k_ h) (tail τ (J_ h)) (age h i)) :=
    axes.oldGroup.of_le fun h i=>((S_ h i).group_power (k:=k_ h) rfl rfl _).le
  obtain ⟨numbers,keyCount⟩:=front_counts G board D f g op.C op.w (fun h=>J_ h) z r level
    axes.oldHost axes.newHost oldG axes.newGroup M
  have c : ContactDimensions p:=⟨axes.oldHost,oldG,axes.newGroup,M,Bounded.const D,
    r.sheets.block.bounded level,r.previousCap.bounded level,r.sheets.shapes.bounded level,r.sheets.contact.bounded level⟩
  have aligned : ∀h i,(p h i).ContactAligned :=fun h i=>fromBoard_contact_aligned ..
  have axes' : ∀h i,(p h i).PeerAxes:=by intro h i;constructor <;> first | rfl | exact Nat.two_pow_pos _
  obtain ⟨donors,contacts,products⟩:=scheduled_contact_rooms p c aligned priced
  obtain ⟨C,matrix⟩:=axes.matrices
  have sizeGL : ∀ᶠ h:ℕ in atTop,∀i,(p h i).sheets.stemDimension*(p h i).sheets.stemDimension≤C*h :=by
    filter_upwards [matrix] with h each
    intro i
    have lim:=each i
    change 2^((p h i).sheets.stemDimension*(p h i).sheets.stemDimension)≤2^(C*h) at lim
    by_contra! higher
    exact (not_lt_of_ge lim) (Nat.pow_lt_pow_right (by decide) higher)
  have sheets:=CandidateSheets.room_from_schedule p r.sheets level axes.newHost axes.newGroup M
    (fun _ _=>rfl) (fun _ _=>Nat.two_pow_pos _) (fun _ _=>rfl) (fun _ _=>rfl) ⟨C,sizeGL⟩
    (axes.oldHost.mul c.shapes) (c.lows.mul ((Bounded.const 2).mul c.cap)) priced
  let const (a:ℕ):=Bounded.const (ι:=ι) a
  have L:=r.sheets.block.bounded level
  have k : Bounded (fun h (_:ι h)=>k_ h):=L.of_le fun _ _=>Nat.lt_two_pow_self.le
  have rows:=((k.add (const 1)).mul L).mul (const (2^n+1))
  have actorKey : ∀ᶠ h:ℕ in atTop,∀i,(p h i).actor.unitBits*(p h i).actor.lanes≤1*h :=
    priced.mono fun h w i=>(w i _ (.inl (by
      change (p h i).actor.unitBits ∈ (p h i).rootUnits
      simp [rootUnits]))).trans
      (by simpa only [Nat.one_mul] using Nat.div_le_self h 2)
  have tag : ∀ᶠ h:ℕ in atTop,∀i,(p h i).actor.headerBits≤1*h :=by
    filter_upwards [actorKey] with h fit
    intro i
    have m : 0<(p h i).actor.lanes:=Nat.two_pow_pos _
    exact (Nat.le_add_left ..).trans ((Nat.le_mul_of_pos_right _ m).trans (fit i))
  have actor : ActorSetup.ScalarRoom (fun h i=>(p h i).actor) :=
    ⟨axes.oldHost,rows.mul ((const (D+1)).mul rows),oldG,M,c.shapes,r.dimension.bounded level,
      const (D*2^(GroupStage.depthBound D n f g)),⟨1,tag⟩,⟨1,actorKey⟩⟩
  exact ⟨projected_words p axes' numbers priced donors contacts,products,
    private_words p axes' numbers priced (fun _ _=>rfl) keyCount,sheets,actor⟩

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
