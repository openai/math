import OAI.Hierarchy.DescentNamedSheetRoom
import OAI.Hierarchy.DescentNamedFrontDimensions
import OAI.Hierarchy.DescentScheduledContactRoom

namespace OAI
/-! # Reset workspace bounds over a common family of recorded schedules -/
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

/-- Only the native numerical envelope is shared between members of the family.
The epoch exponent, frozen depth and initial cardinal may all vary with the index. -/
theorem uniform_region_rooms (r : CalendarInputs G board D f g op.C op.w index z)
    (level : ∀ᶠ h:ℕ in atTop,index h≤h)
    (oldH : Bounded fun h i=>(sample h i).sched.hostSize (age h i))
    (newH : Bounded fun h i=>(sample h i).sched.hostSize (age h i+1))
    (oldG : Bounded fun h i=>let a:=sample h i;2^a.sched.groupWidth a.k a.tail a.age)
    (newG : Bounded fun h i=>(sample h i).sched.groupCount (age h i+1))
    (M : Bounded fun h i=>2^(root h i))
    (matrices : Bounded fun h i=>let a:=sample h i;let dim:=a.sched.groupWidth a.k a.tail a.age+a.k;2^(dim*dim))
    (priced : Installed p) :
    CandidateFront.ScalarRoom (fun h i=>(p h i).front) ∧
    DescentContactOutputShape.Shape.ScalarRoom (fun h i=>(p h i).contactShape) ∧
    DescentPrivateMaskDeck.Shape.ScalarRoom (fun h i=>(p h i).privateShape) ∧
    CandidateSheets.ScalarRoom (fun h i=>(p h i).sheets) ∧ ActorSetup.ScalarRoom (fun h i=>(p h i).actor) :=by
  obtain ⟨numbers,keyCount⟩:=front_counts G board D f g op.C op.w index z r level
    oldH newH oldG newG M
  have c : ContactDimensions p:=⟨oldH,oldG,newG,M,Bounded.const D,
    r.sheets.block.bounded level,r.previousCap.bounded level,r.sheets.shapes.bounded level,r.sheets.contact.bounded level⟩
  have aligned : ∀h i,(p h i).ContactAligned :=fun h i=>fromBoard_contact_aligned ..
  have axes' : ∀h i,(p h i).PeerAxes:=by intro h i;constructor <;> first | rfl | exact Nat.two_pow_pos _
  obtain ⟨donors,contacts,products⟩:=scheduled_contact_rooms p c aligned priced
  obtain ⟨C,matrix⟩:=matrices
  have sizeGL : ∀ᶠ h:ℕ in atTop,∀i,(p h i).sheets.stemDimension*(p h i).sheets.stemDimension≤C*h :=by
    filter_upwards [matrix] with h each
    intro i
    have lim:=each i
    change 2^((p h i).sheets.stemDimension*(p h i).sheets.stemDimension)≤2^(C*h) at lim
    by_contra! higher
    exact (not_lt_of_ge lim) (Nat.pow_lt_pow_right (by decide) higher)
  have sheets:=CandidateSheets.room_from_schedule p r.sheets level newH newG M
    (fun _ _=>rfl) (fun _ _=>Nat.two_pow_pos _) (fun _ _=>rfl) (fun _ _=>rfl) ⟨C,sizeGL⟩
    (oldH.mul c.shapes) (c.lows.mul ((Bounded.const 2).mul c.cap)) priced
  let const (a:ℕ):=Bounded.const (ι:=ι) a
  have L:=r.sheets.block.bounded level
  have k : Bounded (fun h (i:ι h)=>(z h i).k):=L.of_le fun _ _=>Nat.lt_two_pow_self.le
  have rows:=((k.add (const 1)).mul L).mul (const (2^n+1))
  have actorKey : ∀ᶠ h:ℕ in atTop,∀i,(p h i).actor.unitBits*(p h i).actor.lanes≤1*h :=
    priced.mono fun h w i=>(w i _ (.inl (by simp [rootUnits]))).trans
      (by simpa only [Nat.one_mul] using Nat.div_le_self h 2)
  have tag : ∀ᶠ h:ℕ in atTop,∀i,(p h i).actor.headerBits≤1*h :=by
    filter_upwards [actorKey] with h fit
    intro i
    have m : 0<(p h i).actor.lanes:=Nat.two_pow_pos _
    exact (Nat.le_add_left ..).trans ((Nat.le_mul_of_pos_right _ m).trans (fit i))
  have actor : ActorSetup.ScalarRoom (fun h i=>(p h i).actor) :=
    ⟨oldH,rows.mul ((const (D+1)).mul rows),oldG,M,c.shapes,r.dimension.bounded level,
      const (D*2^(GroupStage.depthBound D n f g)),⟨1,tag⟩,⟨1,actorKey⟩⟩
  exact ⟨projected_words p axes' numbers priced donors contacts,products,
    private_words p axes' numbers priced (fun _ _=>rfl) keyCount,sheets,actor⟩


end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
