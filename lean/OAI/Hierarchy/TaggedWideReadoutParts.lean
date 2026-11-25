import OAI.Hierarchy.TaggedWideGuardedBoard
import OAI.Hierarchy.TaggedWideGuardedBill

namespace OAI
/-! # One parent format built from two original RAM gates and physical routed records -/
noncomputable section
namespace Hierarchy.Tagged.WideControlJoin
open ThreeFlat Routing TaggedPrune Computability.VPVNP.BurstRAM
open scoped Classical BigOperators

/-- The finite inputs to the wide constructor before the quantified parent
bound. The two native programs and the original-site tensors are actual
objects on their common pins; all shorter sockets are the two compactors. -/
structure Frame (F : Type*) [Field F] (k h w M : ℕ) where
  routing : NativeRouting F k h w M
  data : Type
  [finiteData : Fintype data]
  first : Gate
  paid : Gate
  prefixPins : first.Head→(OpenPins h w routing.catalyst ⊕ Fin routing.selectors)⊕Bool
  paidPins : paid.Head→(OpenPins h w routing.catalyst ⊕ Fin routing.selectors)⊕Bool
  flag : Fin first.u
  site : BitNetwork F (Fintype.card (SitePins (OpenPins h w routing.catalyst) (Fin routing.selectors) data paid))
attribute [instance] Frame.finiteData

structure Parts (F : Type*) [Field F] (k h w M n : ℕ) extends Frame F k h w M where
  cut : Fin n→CutFormat F (SitePins (OpenPins h w routing.catalyst) (Fin routing.selectors) data paid)
  cap : Fin n→ℕ

namespace Parts
variable {F : Type*} [Field F] {k h w M n : ℕ} (a : Parts F k h w M n)
local notation "E" => OpenPins h w a.routing.catalyst
local notation "Q" => Fin a.routing.selectors

def charges := nativeCharges a.routing a.first a.paid a.cut a.site

/-- The semantic hypotheses are elementary observations of the real native
execution and the signed finite sum of physically wired local data. -/
structure Run where
  prefixHeader : (E→Bool)→(Q→Bool)→ℕ→Word a.first.W
  paidHeader : (E→Bool)→(Q→Bool)→ℕ→Word a.paid.W
  prefixRead : ∀ e s,headerRead a.prefixPins e s=a.first.headBits (prefixHeader e s)
  paidRead : ∀ e s,headerRead a.paidPins e s=a.paid.headBits (paidHeader e s)
  admitted : (E→Bool)→(Q→Bool)→Prop
  accept : ∀ e s,authentic (parentTag a.routing) e s→
    a.first.observed (prefixHeader e s) (a.first.zeroFlag a.flag)=if admitted e s then (1:F) else 0
  tape : ∀ e s,authentic (parentTag a.routing) e s→(admitted e s ↔ ∃j,reads a.routing.encoding e s j)
  out : (E→Bool)→(Q→Bool)→Memory a.paid.W
  ran : ∀e s,authentic (parentTag a.routing) e s→admitted e s→a.paid.Ran (paidHeader e s) (out e s)
  room : a.paid.W+1≤4*a.paid.m
  terminal : ∀e s j,reads a.routing.encoding e s j→
    (∑ d : a.data→Bool,(∏i,(a.cut i).closed (Sum.elim e (Sum.elim s (Sum.elim d (a.paid.terminal (out e s))))))*
      localSite a.paid a.site e s d (a.paid.terminal (out e s))) =
        if (a.routing.links j).Keep (2^h) then a.routing.route j e else 0

/-- All 57 control slots and all physical costs are those of the guarded
constructor at this parent. -/
theorem built (run : a.Run)
    (m₀ : a.first.m=controlHeight h (a.first.S+(a.first.f+a.first.u)))
    (m₁ : a.paid.m=controlHeight h (a.paid.S+(a.paid.f+a.paid.u)))
    (slots : a.paid.S+(a.paid.f+a.paid.u)≤2^a.paid.m) :
    let counts:=WideHost.dualControlRows h (a.charges.rows false) (a.charges.rows true)
    ∃board : StaticBoard F k h w M (fun i=>(a.cut i).bank (a.cap i)) (fun j=>controlHeight h (counts j)),
      board.cost≤a.charges.total h ∧ board.selectors≤a.charges.selectors := by
  intro counts
  have format : (fun j=>controlHeight h (counts j))=WideHost.dualControlSizes h a.first.m a.paid.m := by
    change (fun j=>controlHeight h (WideHost.dualControlRows h (a.first.S+(a.first.f+a.first.u))
      (a.paid.S+(a.paid.f+a.paid.u)) j))=_
    rw [WideHost.dual_control_sizes,←m₀,←m₁]
  rw [format]
  obtain ⟨board,sel,limit⟩:=guarded_board a.routing a.first a.paid a.cut a.cap a.prefixPins a.paidPins a.flag a.site
    run.prefixHeader run.paidHeader run.prefixRead run.paidRead run.admitted run.accept run.tape run.out run.ran
    slots run.room run.terminal
  exact ⟨board,guarded_native_bill a.routing a.first a.paid a.cut a.cap a.prefixPins a.paidPins a.flag a.site board
    m₀ m₁ limit,sel.le⟩

end Parts
end Hierarchy.Tagged.WideControlJoin

end
end OAI
