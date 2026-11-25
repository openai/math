import OAI.Hierarchy.GridChosenReceiverPrefix
import OAI.Hierarchy.GridReceiverIntervalSchedule
import OAI.Hierarchy.GridReceiverBanks
import OAI.Hierarchy.GridPinResourceFiber

namespace OAI
/-! # The four interval-scan tables after the receiver's native root election -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.GridReceiverIntervalInputs
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM NodePublication TraceAdmission TraceDistribution GridRegisteredSetting
open Computability.VPVNP.BurstRAM PrivateRAM GridReceiverDirectory GridReceiverTickDirectory GridPinArena
open GridThrough FactorPinIntervals
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {w pc regs slots S base fuel axes : ℕ}
variable (D : RunData F (64*w) pc regs slots S base fuel axes (w/2)) (l : GridNativeImage.Layout)
local notation "W" => (64*w)
local notation "J" => (GridDescription.sector w)
local notation "g" => (slab w)
local notation "age" => (receiverAge w)
local notation "m" => l.dimension
local notation "n" => l.sideMinusOne
local notation "q" => l.copies
local notation "k" => (m+1)
local notation "T" => ((n+1)^k*q)
local notation "P" => (GridReceiverBanks.pinPlan D l)
local notation "dir" => (GridReceiverDirectory.native D l)
local notation "stages" => (dir).stages.length
local notation "full" => (2^(axes+1) : ℕ)
local notation "span" => (2^(w/2) : ℕ)
local notation "unit" => (D.issuedUnit w l.degree l.stageRate l.rootRate)
local notation "cost" => (D.costs (GridNativeImage.resources D l))

private theorem controls_low (large : 64^10≤w) : TickWorkspace.base age 18+5≤14*J := by
  have positive : 1≤w := le_trans (by decide : 1≤64^10) large
  have top := (receiverAge_chart w large).2
  have bound : TickWorkspace.stride age ≤ 2^(20*w) := by
    change (2^(age^10))^4 ≤ 2^(20*w)
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have space : 32*2^(20*w) ≤ J := by
    change 2^5*2^(20*w) ≤ 2^(32*w)
    rw [←pow_add];exact Nat.pow_le_pow_right (by decide) (by omega)
  have pos := (Nat.two_pow_pos (20*w))
  change 19*TickWorkspace.stride age+5 ≤ 14*J
  omega

/-- On a real selected occurrence, the compiler has already executed the
registration, the assignment passes and the tick-specific root filter. -/
theorem from_prefix (geom : ElectionRoom D l) (large : 64^10≤w) (z : D.trace)
    (sel : Fin (l.selectorCap+1) → Bool) (safe : GridNativeDispatch.WordRoom D)
    {input origin entry classified out : Memory W}
    (history : Histories D l z sel safe input origin entry)
    (t : Fin T)
    (assigned : GridSimulation.Assigned geom.teams_pos (cost z.1 m n l.bank D.issuedCharges unit) entry classified)
    (ticked : Ticked (banks w age)
      (FactorAllocation.factors w (cost z.1 m n l.bank D.issuedCharges unit) (List.finRange (D.roots z.1)) t)
      (t.val : Word W) classified out)
    (Q : Layout (Cell k n × Fin q) S (D.roots z.1) l.pinWidth)
    (owners : ∀ i, Q.origin i=D.origin z.1 i) :
    GridPinPublisher.CountInputs P Q geom.teams_pos w (cost z.1 m n l.bank D.issuedCharges unit) (D.dest z.1) out := by
  obtain ⟨_,_,_,_,_,N,_,_,_,_,registered,_⟩ := history
  let amount := cost z.1 m n l.bank D.issuedCharges unit
  let ids := FactorAllocation.factors w amount (List.finRange (D.roots z.1)) t
  let K := (20*(w+1)+2)^(k+2)
  have limit : 32*g≤J := (scales w geom.pos).1
  have nonzero : 0<g := Nat.two_pow_pos _
  have count : (D.roots z.1)*(k+2)≤g := by rw [N];exact geom.rows
  have nBound : D.roots z.1≤g := by rw [N];exact geom.items
  have classes : K≤g := geom.groups
  have thresh : GridReceiverHeader.count w≤g := geom.thresholds
  have len : ids.length ≤ K*(D.roots z.1) := by
    dsimp only [ids]
    rw [←GridReceiverDirectoryOrder.rows geom.teams_pos w amount t]
    exact (List.length_filterMap_le ..).trans_eq List.length_range
  have separate : TickWorkspace.base age 17+K*(D.roots z.1)≤TickWorkspace.base age 18 := by
    rw [N]; exact geom.room.separate
  have lower := controls_low (w:=w) large
  have stable (a : ℕ) (after : 14*J≤a) (gap : a<15*J+20*g ∨ 16*J≤a) : out a=classified a := by
    apply ticked.frame a
    · right; change TickWorkspace.base age 17+ids.length≤a; omega
    · right; change TickWorkspace.base age 18+5≤a;omega
    · change a<15*J+20*g ∨ 15*J+20*g+2≤a;omega
  have resource (a : ℕ) (lo : 14*J≤a) (hi : a<14*J+g) : GridSimulation.protectedAddress w (D.roots z.1) (k+2) a := by
    unfold GridSimulation.protectedAddress FactorBucketRAM.untouched FactorBucketRAM.Outside
    dsimp [assignmentBanks];omega
  have old (a : ℕ) (high : 16*J≤a) : GridSimulation.protectedAddress w (D.roots z.1) (k+2) a := by
    change FactorBucketRAM.Outside a (14*J+g) (GridReceiverHeader.count w) ∧
      FactorBucketRAM.Outside a (15*J) ((D.roots z.1)*(k+2)) ∧ FactorBucketRAM.Outside a (15*J+g) (D.roots z.1) ∧
      FactorBucketRAM.Outside a (15*J+2*g) K ∧ FactorBucketRAM.Outside a (15*J+3*g) (D.roots z.1)
    unfold FactorBucketRAM.Outside;omega
  have rows := GridRegisteredOrder.registered D (GridReceiverDirectory.parameters D l) z.1 D.issuedCharges unit
    m n l.bank N registered
  constructor
  · intro f
    change out (15*J+g+f.val)=_
    have := f.isLt
    rw [stable _ (by omega) (.inl (by omega))];exact assigned.key f
  · intro f
    change out (15*J+3*g+f.val)=_
    have := f.isLt
    rw [stable _ (by omega) (.inl (by omega))];exact assigned.owner f
  · intro f
    let i := 14*J+f.val*(k+2)+1
    have bound := Nat.mul_le_mul_right (k+2) f.isLt
    rw [Nat.succ_mul] at bound
    have lo : 14*J ≤ i := by dsimp [i];omega
    have hi : i<14*J+g := by dsimp [i];omega
    have bits : entry i=(TraceAdmission.inputCount (D.dest z.1) f S span : Word W) :=
      (Fin.cast_val_eq_self (entry i)).symm.trans (congrArg (fun a : ℕ => (a : Word W)) (rows.inputs f))
    change out i=_
    rw [stable i lo (.inl (by omega)),assigned.frame _ (resource i lo hi),bits]
    rw [GridPinPublisher.inputLength_from_resource (D.dest z.1) Q.origin D.bucket (Nat.two_pow_pos _)
      D.input_extent (TraceDistribution.native_interval_index D.machine D.fit D.field D.state)
      (fun j => (D.owns z.1 j).trans (owners j).symm)]
  · intro j
    let i := 16*J+g+stages*full+j.val
    have high : 16*J ≤ i := by dsimp only [i];omega
    change out i=_
    rw [stable i (by omega) (.inr high),assigned.frame i (old _ high)]
    exact rows.owners j

/-- Later low-workspace phases may transport all four inputs together by
preserving the physical resource, class, owner and ancestor window. -/
theorem keep_window (geom : ElectionRoom D l) (z : D.trace)
    (Q : Layout (Cell k n × Fin q) S (D.roots z.1) l.pinWidth) {before after : Memory W}
    (src : GridPinPublisher.CountInputs P Q geom.teams_pos w (cost z.1 m n l.bank D.issuedCharges unit) (D.dest z.1) before)
    (keep : ∀ i, 14*J ≤ i → i<16*J+g+stages*full+full → after i=before i) :
    GridPinPublisher.CountInputs P Q geom.teams_pos w (cost z.1 m n l.bank D.issuedCharges unit) (D.dest z.1) after := by
  have high := (scales w geom.pos).1
  have N := GridReceiverDirectory.roots D l z.1
  have bound : D.roots z.1≤g := by rw [N];exact geom.items
  have rows : D.roots z.1*(k+2)≤g := by rw [N];exact geom.rows
  have windowEnd : 16*J+g ≤ 16*J+g+stages*full+full :=
    (Nat.le_add_right (16*J+g) (stages*full)).trans (Nat.le_add_right _ full)
  apply GridPinPublisher.CountInputs.keep src
  · intro f
    have := f.isLt
    apply keep (15*J+g+f.val) (by omega)
    exact lt_of_lt_of_le (by omega : 15*J+g+f.val < 16*J+g) windowEnd
  · intro f
    have := f.isLt
    apply keep (15*J+3*g+f.val) (by omega)
    exact lt_of_lt_of_le (by omega : 15*J+3*g+f.val < 16*J+g) windowEnd
  · intro f; have h := Nat.mul_le_mul_right (k+2) f.isLt;rw [Nat.succ_mul] at h
    apply keep (14*J+f.val*(k+2)+1) (by omega)
    exact lt_of_lt_of_le (by omega : 14*J+f.val*(k+2)+1 < 16*J+g) windowEnd
  · intro j; have := j.isLt;change after (16*J+g+stages*full+j.val)=_;apply keep <;> omega

end Hierarchy.GridReceiverIntervalInputs
end

end OAI
