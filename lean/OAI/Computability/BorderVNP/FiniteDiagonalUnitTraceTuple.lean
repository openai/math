import OAI.Computability.BorderVNP.FiniteDiagonalNativeBranches
import OAI.Computability.BorderVNP.FiniteDiagonalUnitTracePacket

/-! # The unit tag indexes exactly the accepted physical unit tuple

The unit summand has no private guesses. The product of the local trace indices
therefore tests the all-zero exterior assignment and the true reference column,
and every such tuple carries field weight one.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM TeamContraction RoutingISA RoutingISA.Pins RoutingISA.Evaluator ProcessorSlots
open scoped BigOperators Classical

variable {F : Type*} [Field F] {R r d w link : ℕ}

/-- Assemble local trace bijections before summing. Only the reference column on
team zero matters, even if the other teams' literal packets have different reference columns. -/
theorem unitTuple_decode {ι S : Type*} (M : Fin (R+1) → MachineInput w S)
    (bnd : ∀ u, Bounds r (M u).inputSize)
    (weight : ∀ u, NativePath (M u) (bnd u).ticks (bnd u).burst (bnd u).privateClock → F)
    (pin : Fin d → Bool) (ref : Fin (R+1) → Fin d → Bool) (ext : Exterior R r link → Bool)
    (localData : ∀ u, Nonempty (NativePath (M u) (bnd u).ticks (bnd u).burst
      (bnd u).privateClock ≃ PLift (LocalUnit u pin (ref u) ext)) ∧ ∀ p, weight u p = 1) :
    ∃ E : {p : NativeTuple M bnd // tuplePathWeight (M := M) (b := bnd) weight p ≠ 0} ≃
      {tag : Option ι // tag = none ∧ ext = (fun _ => false) ∧ pin = ref 0},
      ∀ p, (E p).val = none ∧ tuplePathWeight (M := M) (b := bnd) weight p.val = 1 := by
  have equiv (u) := Classical.choice (localData u).1
  have unitValue (p : NativeTuple M bnd) : tuplePathWeight (M := M) (b := bnd) weight p = 1 := by
    simp [tuplePathWeight, fun u => (localData u).2 (p u)]
  have common : (∀ u, LocalUnit u pin (ref u) ext) ↔ ext = (fun _ => false) ∧ pin = ref 0 := by
    rw [← forall_localUnit pin (ref 0) ext]
    constructor <;> intro h u <;> exact ⟨(h u).1,fun hu => by subst u; exact (h 0).2 rfl⟩
  let encode (p : {p : NativeTuple M bnd // tuplePathWeight (M := M) (b := bnd) weight p ≠ 0}) :
      {tag : Option ι // tag = none ∧ ext = (fun _ => false) ∧ pin = ref 0} :=
    ⟨none,rfl,common.mp fun u => (equiv u (p.val u)).down⟩
  refine ⟨Equiv.ofBijective encode ⟨?_,?_⟩, fun p => ⟨rfl,unitValue p.val⟩⟩
  · intro x y _
    apply Subtype.ext
    funext u
    exact (equiv u).injective (Subsingleton.elim ..)
  · rintro ⟨tag,htag,hOK⟩
    subst tag
    let p : NativeTuple M bnd := fun u => (equiv u).symm ⟨common.mpr hOK u⟩
    exact ⟨⟨p,(unitValue p).trans_ne one_ne_zero⟩,Subtype.ext rfl⟩

/-- Numeric and address placement conditions for a single actual zero-tag packet.
All local trace bijections are derived from these physical frame checks. -/
structure UnitPacketPlacement (pkt : ReferencePacket w d) (f : BroadcastFrame) (L : Layout)
    (fields : ProcessorFields L) (pub : Arg → Word w) (A : AdviceLayout) (offset ticks : ℕ) : Prop where
  /-- The true public operands encode the fixed boot layout. -/
  scalar : PacketFrame L f A pkt.entry.length w (fun _ => 0) (operand pub)
  /-- The broadcast region is in word-address range. -/
  broadcast : f.Fits w (pub 0).val
  /-- The literal-advice region and its source are disjoint and in range. -/
  advice : A.Fits f w (pub 0).val
  /-- The extended boot frame fits the allocated words. -/
  extension : ExtendedFrame.Fits w (pub 0).val A.dst pkt.entry.length
  /-- The advised data start at the actual compiled site offset. -/
  location : A.offset = offset
  /-- All packet bits fit in the literal-advice region. -/
  capacity : pkt.bits.length ≤ A.count
  /-- The reference column is read from the decoded packet. -/
  reference : L.starbase = A.dst+pkt.offset
  /-- The physical reference branch bit is zero. -/
  zeroTag : readings (processorMemory fields w) (f.addr f.partner 0) = 0
  /-- Stride and count fit the architectural register width. -/
  stride : L.stride < 2^w
  /-- The flattened pin slots fit a single register. -/
  count : L.count < 2^w
  /-- The live column fits the flattened processor slots. -/
  room : L.width ≤ L.count
  /-- The broadcast preserves the advised column. -/
  separate : L.starbase+d ≤ f.dst ∨ f.dst+f.header ≤ L.starbase
  /-- The owner can address every bit of both columns. -/
  pins : L.team = 0 → IdentityFits L w
  /-- All three boot phases and the zero-tag check fit the charged clock. -/
  time : packetUnitBudget A.count w f L ≤ ticks

variable {pc reg k routines m g a n e m' g' : ℕ} {Q Γ Q' Γ' : Type} [Fintype Q]

/-- Direct unit summand of the finite diagonal: the accepted bounded native tuples
of the actual assembled processors on a zero tag are indexed by the single unit tag
exactly on the zero exterior and matching column. -/
theorem jointPacket_unitTuple {ι : Type*} (P : TeamOpcode.Program pc reg k routines)
    (lib : Fin routines → TeamSite.Macro Q Γ m g) (S : SiteData R r reg k w a)
    (pack : Fin (R+1) → ReferencePacket w d) (fit : Fits P lib r w a R link n e)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (header dst ibase hbase starbase : Fin (R+1) → ℕ)
    (pub : Fin (R+1) → Arg → Word w) (bank : Fin (R+1) → Bank w)
    (A : Fin (R+1) → AdviceLayout) (eval : Code) (fallsThrough : eval.withoutAccept = true)
    (nativeLib : Fin 8 → TeamSite.Macro Q' Γ' m' g') (ret : FieldProcessor.Returns Q' Γ' F m' 8)
    (fuel : ℕ) :
    let G := wiring P lib (S.withPacket pack) d link n e fit
    let L (u) := G.pinLayout u (ibase u) (hbase u) (starbase u)
    let f (u) := G.transferFrame u (header u) (dst u)
    let fields (u) := G.processorFields u pin ext (ibase u) (hbase u) (starbase u)
    let mac := TeamSiteEvents.macros nativeLib fuel
    let M (u) := processorMachine (withStartup eval) (pub u) mac (bank u) (fields u)
    ∀ bnd : ∀ u, Bounds r (M u).inputSize,
      (∀ u, UnitPacketPlacement (pack u) (f u) (L u) (fields u) (pub u) (A u)
        (adviceOffset P lib r w n) (bnd u).ticks) →
      let weight (u) (p : NativePath (M u) (bnd u).ticks (bnd u).burst (bnd u).privateClock) :=
        FieldProcessor.pathProduct (withStartup eval).program (pub u) nativeLib ret fuel ⟨0,bank u⟩ p.val
      ∃ E : {p : NativeTuple M bnd // tuplePathWeight (M := M) (b := bnd) weight p ≠ 0} ≃
        {tag : Option ι // tag = none ∧ ext = (fun _ => false) ∧ pin = (pack 0).reference},
        ∀ p, (E p).val = none ∧ tuplePathWeight (M := M) (b := bnd) weight p.val = 1 := by
  intro G L f fields mac M bnd place weight
  apply unitTuple_decode M bnd weight pin (fun u => (pack u).reference) ext
  intro u
  let h := place u
  exact jointPacket_unit_trace P lib S pack link n e fit u pin ext (header u) (dst u) (ibase u)
    (hbase u) (starbase u) (pub u) nativeLib ret fuel (bank u) (A u) eval fallsThrough
    (bnd u).ticks (bnd u).burst (bnd u).privateClock h.scalar h.broadcast h.advice h.extension
    h.location h.capacity h.reference h.zeroTag h.stride h.count h.room h.separate
    (fun eq => h.pins (congrArg Fin.val eq)) h.time

/-- Identify the decoded unit fiber with the `none` summand in the finite
branch count. The selected data pin equals the reference on its owner. -/
def unitTagsEquiv {ι : Type*} {Edge : Type} {t inner : ℕ} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} (ref : Fin d → Bool) (same : pin = ref)
    (layout : ι → Routing.WireLayout (R+1) r link)
    (banks : ∀ i ext, WireSnapshots G pin ext (layout i) w)
    (fixed : ι → Routing.Block (R+1)) (header : ∀ i, Fin (layout i).header → Bool)
    (high payload : ι → Fin (R+1) → Fin (R+1) → ℕ → Bool) (value : ι → F)
    (ext : Exterior R r link → Bool) :
    {tag : Option ι // tag = none ∧ ext = (fun _ => false) ∧ pin = ref} ≃
    {tag : Option ι // tag = none ∧ branchPasses layout banks fixed header high payload ext tag ∧
      branchWeight value tag ≠ 0} :=
  Equiv.subtypeEquivRight fun tag => by
    cases tag with
    | none =>
      change (_ ∧ ext = _ ∧ pin = ref) ↔ (_ ∧ (∀ u, LocalUnit u pin pin ext) ∧ (1:F) ≠ 0)
      simp [forall_localUnit, same]
    | some => simp

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
