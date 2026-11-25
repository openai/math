import OAI.Hierarchy.DescentDatedOrdinaryCountRoof
import OAI.Hierarchy.DescentDatedPhysicalOrdinary
import OAI.Hierarchy.DescentDatedResetScalarRoom
import OAI.Hierarchy.DescentDatedTerminalRate
import OAI.Hierarchy.DescentDatedInitialArea
import OAI.Hierarchy.DescentDatedRetainedExceptions

namespace OAI
/-! # One native calendar uses the actual compiled branch at each legitimate date -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSixParty.Chronology DescentTerminalCompiledPrefix Filter
noncomputable section

inductive NativeDate (F P : Type) [Field F] where
  | ordinary (v : PhysicalOrdinary F P)
  | reset (v : PhysicalReset)

namespace NativeDate
variable {F P : Type} [Field F]
def stop (d : NativeDate F P) (base : ℕ) := match d with
  | .ordinary v=>v.fullEnd base
  | .reset v=>v.fullEnd base
theorem contains (d : NativeDate F P) (base : ℕ) : base≤d.stop base := by
  cases d with
  | ordinary v=>exact (v.full_spent base).1
  | reset v=>
    have h:=v.occupied (v.stageStart base)
    exact (v.ingress.after base).trans ((h.1.trans h.2.1).trans h.2.2)

variable {A : Type} (image : ℕ→InitialArea A) (dates : ℕ→ℕ) (calendar : ∀h,Fin (dates h)→NativeDate F P)
def bump (h t base : ℕ) :=if valid:t<dates h then (calendar h ⟨t,valid⟩).stop base else base
def atDate (h j : ℕ) :=cursor (image h).floor (bump dates calendar h) j

theorem bump_grows (h j base : ℕ) : base≤bump dates calendar h j base := by
  unfold bump
  split
  · apply contains
  · rfl

/-- A prior word the chronological executors preserve below their native stage floor stays
identical at any subsequent date, including empty or repeated physical apertures. -/
theorem keeps_prior {h w s t addr : ℕ} (states : ℕ → Computability.VPVNP.BurstRAM.Memory w)
    (inside : addr<atDate image dates calendar h s) (later : s≤t)
    (frame : ∀j,s≤j→j<t→∀a<atDate image dates calendar h j,states (j+1) a=states j a) :
    states t addr=states s addr :=
  cursor_retains (bump dates calendar h) (bump_grows dates calendar h) states inside later frame

/-- The paid ordinary accumulator may update the old private-counter word on every visit. -/
theorem keeps_prior_except {h w s t addr counter : ℕ} (states : ℕ → Computability.VPVNP.BurstRAM.Memory w)
    (inside : addr<atDate image dates calendar h s) (later : s≤t) (different : addr≠counter)
    (frame : ∀j,s≤j→j<t→∀a<atDate image dates calendar h j,a≠counter→states (j+1) a=states j a) :
    states t addr=states s addr := by
  let steps:=bump dates calendar h
  let spans:=fun j=>steps j (atDate image dates calendar h j)-atDate image dates calendar h j
  have same (k : ℕ) : atDate image dates calendar h k=floor (image h).floor spans k :=
    cursor_eq _ steps (bump_grows dates calendar h) k
  apply retained_outside_counter spans states (inside.trans_eq (same s)) later different
  intro j lo hi a pre ne
  exact frame j lo hi a (pre.trans_eq (same j).symm) ne

abbrev OrdinaryAt (h : ℕ) :={p : Fin (dates h)×PhysicalOrdinary F P // calendar h p.1=.ordinary p.2}
abbrev ResetAt (h : ℕ) := {p : Fin (dates h)×PhysicalReset // calendar h p.1=.reset p.2}

theorem increment_rate
    (ordinary : Bounded (ι:=OrdinaryAt dates calendar) (fun _ p=>p.val.2.fullCeiling))
    (reset : Bounded (ι:=ResetAt dates calendar) (fun h p=>
      p.val.2.fullEnd (atDate image dates calendar h p.val.1)-atDate image dates calendar h p.val.1)) :
    Bounded (ι:=fun h=>Fin (dates h)) (fun h t=>
      bump dates calendar h t (atDate image dates calendar h t)-atDate image dates calendar h t) := by
  obtain ⟨E,e⟩:=ordinary
  obtain ⟨R,r⟩:=reset
  refine ⟨max E R,?_⟩
  filter_upwards [e,r] with h oh rh
  intro t
  rw [bump,dite_eq_left t.isLt]
  cases hv:calendar h t with
  | ordinary v=>
    have cap:=oh (⟨(t,v),hv⟩:OrdinaryAt dates calendar h)
    have paid:=(v.full_spent (atDate image dates calendar h t)).2.1
    change v.fullCeiling≤2^(E*h) at cap
    change v.fullEnd _-_≤_
    exact (show v.fullEnd (atDate image dates calendar h t)-atDate image dates calendar h t≤v.fullCeiling by omega).trans
      (cap.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_left E R))))
  | reset v=>
    have cost:=rh (⟨(t,v),hv⟩:ResetAt dates calendar h)
    exact cost.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_right E R)))

/-- The same exponent covers initial real data, both actual native branch types, terminal
private masking and the final five-pass scalar output, for all sufficiently large input sizes. -/
theorem full_word_room (S : ℕ→Shape) (I : ℕ→AddressPlan.Input) (terminal : AddressPlan.Rates S I)
    (initial : Bounded (ι:=fun _=>Unit) (fun h _=>(image h).floor))
    (length : Bounded (ι:=fun _=>Unit) (fun h _=>dates h))
    (ordinary : Bounded (ι:=OrdinaryAt dates calendar) (fun _ p=>p.val.2.fullCeiling))
    (reset : Bounded (ι:=ResetAt dates calendar) (fun h p=>
      p.val.2.fullEnd (atDate image dates calendar h p.val.1)-atDate image dates calendar h p.val.1))
    (maskedAt : ℕ→ℕ) (mask : Bounded (ι:=fun _=>Unit)
      (fun h _=>maskedAt h-atDate image dates calendar h (dates h))) :
    ∃K : ℕ,∀ᶠ h:ℕ in atTop,AddressPlan.endAddress (S h) (I h) (maskedAt h)<2^(K*h) :=
  AddressPlan.realized_calendar_room S I terminal (fun h=>(image h).floor) dates (bump dates calendar)
    (bump_grows dates calendar) initial length (increment_rate image dates calendar ordinary reset) maskedAt mask

theorem monotone_dates (h : ℕ) : Monotone (atDate image dates calendar h) :=
  monotone_nat_of_le_succ (fun j=>bump_grows dates calendar h j _)

/-- One hardware register width simultaneously addresses every attained intermediate stage floor,
the terminal pooled keys and therefore each address strictly inside their published slabs. -/
theorem every_word_room (S : ℕ→Shape) (I : ℕ→AddressPlan.Input) (terminal : AddressPlan.Rates S I)
    (initial : Bounded (ι:=fun _=>Unit) (fun h _=>(image h).floor))
    (length : Bounded (ι:=fun _=>Unit) (fun h _=>dates h))
    (ordinary : Bounded (ι:=OrdinaryAt dates calendar) (fun _ p=>p.val.2.fullCeiling))
    (reset : Bounded (ι:=ResetAt dates calendar) (fun h p=>
      p.val.2.fullEnd (atDate image dates calendar h p.val.1)-atDate image dates calendar h p.val.1))
    (maskedAt : ℕ→ℕ) (mask : Bounded (ι:=fun _=>Unit)
      (fun h _=>maskedAt h-atDate image dates calendar h (dates h))) :
    ∃K : ℕ,∀ᶠ h:ℕ in atTop,
      (∀j≤dates h,atDate image dates calendar h j<2^(K*h)) ∧ AddressPlan.endAddress (S h) (I h) (maskedAt h)<2^(K*h) := by
  obtain ⟨C,stages⟩:=eventual_calendar_room (start:=fun h=>(image h).floor) (dates:=dates)
    (bump dates calendar) (bump_grows dates calendar) initial length
    (increment_rate image dates calendar ordinary reset)
  obtain ⟨E,last⟩:=full_word_room image dates calendar S I terminal initial length ordinary reset maskedAt mask
  refine ⟨max C E,?_⟩
  filter_upwards [stages,last] with h paid done_
  constructor
  · intro j inside
    have roof : atDate image dates calendar h (dates h)<2^(C*h) :=paid
    exact ((monotone_dates image dates calendar h inside).trans_lt roof).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_left C E)))
  · exact done_.trans_le (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_right C E)))

/-- The per-date hypotheses are bounded scalar fields of the actual selected machine,
including bits of the finite ROM keys. No per-date upper bound on the output address is needed. -/
theorem every_word_from_scalars (S : ℕ→Shape) (I : ℕ→AddressPlan.Input) (term : AddressPlan.Rates S I)
    (initial : Bounded (ι:=fun _=>Unit) (fun h _=>(image h).floor))
    (length : Bounded (ι:=fun _=>Unit) (fun h _=>dates h))
    (ordinary : DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary.ScalarRoom
      (fun h (p:OrdinaryAt dates calendar h)=>p.val.2.area))
    (six : ∀h (p:OrdinaryAt dates calendar h),
      DescentPacking.PackedMatch.SixBirths.unit p.val.2.area.shapeAt≤p.val.2.unit)
    (vector : DescentOperandVectorArena.Layout.ScalarRoom (fun h (p:OrdinaryAt dates calendar h)=>p.val.2.vector))
    (resolve : DescentDatedPriorOperand.Layout.ScalarRoom (fun h (p:OrdinaryAt dates calendar h)=>p.val.2.resolver))
    (profile : ProfileRepack.ScalarRoom (fun h (p:OrdinaryAt dates calendar h)=>p.val.2.profileRepack))
    (metadata : MetadataReturn.ScalarRoom (fun h (p:OrdinaryAt dates calendar h)=>p.val.2.metadata))
    (digits : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀p:OrdinaryAt dates calendar h,let m:=p.val.2.metadata;(m.spanBits*m.chart.nodes)*m.chart.lanes≤K*h)
    (book : DescentOrdinaryFinal.Chart.ScalarRoom (fun h (p:OrdinaryAt dates calendar h)=>p.val.2.operandBook))
    (extra : Bounded (fun h (p:OrdinaryAt dates calendar h)=>p.val.2.referenceWords))
    (reverse : Bounded (fun h (p:OrdinaryAt dates calendar h)=>p.val.2.reverseWords))
    (routing : MaterialExtent.ScalarRoom (fun h (p:OrdinaryAt dates calendar h)=>p.val.2.material))
    (marks : DescentOrdinaryMarkProject.Shape.ScalarRoom (fun h (p:OrdinaryAt dates calendar h)=>p.val.2.markShape))
    (signed : SignedExtent.ScalarRoom (fun h (p:OrdinaryAt dates calendar h)=>p.val.2.signed))
    (raw : DescentSixParty.StageVenueTail.OrdinaryRaster.ScalarRoom (fun h (p:OrdinaryAt dates calendar h)=>p.val.2.area) (fun h (p:OrdinaryAt dates calendar h)=>p.val.2.venue) (fun h (p:OrdinaryAt dates calendar h)=>p.val.2.rasterLanes))
    (venue : DescentSixParty.StageVenueTail.Date.ScalarRoom (fun h (p:OrdinaryAt dates calendar h)=>p.val.2.venue))
    (primitive : PhysicalOrdinary.PrimitiveScalarRoom (fun h (p:OrdinaryAt dates calendar h)=>p.val.2))
    (reset : PhysicalReset.ScalarRoom (fun h (p:ResetAt dates calendar h)=>p.val.2)
       (fun h (p:ResetAt dates calendar h)=>p.val.2.stageStart (atDate image dates calendar h p.val.1)))
    (ingress : DescentResetCanvasIngress.Layout.ScalarRoom (fun h (p:ResetAt dates calendar h)=>p.val.2.ingress))
    (maskedAt : ℕ→ℕ) (mask : Bounded (ι:=fun _=>Unit)
      (fun h _=>maskedAt h-atDate image dates calendar h (dates h))) :
    ∃K : ℕ,∀ᶠ h:ℕ in atTop,
      (∀j≤dates h,atDate image dates calendar h j<2^(K*h)) ∧ AddressPlan.endAddress (S h) (I h) (maskedAt h)<2^(K*h) := by
  apply every_word_room image dates calendar S I term initial length
    (PhysicalOrdinary.cover_rate (fun h (p:OrdinaryAt dates calendar h)=>p.val.2) ordinary six vector resolve profile metadata digits book extra reverse routing marks signed raw venue primitive)
    (PhysicalReset.complete_increment _ _ reset ingress) maskedAt mask

end NativeDate
end
end Hierarchy.DescentDatedAddressBook

end OAI
