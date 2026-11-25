import OAI.Computability.BorderVNP.DiagonalNativePositivePacket
import OAI.Computability.BorderVNP.PackedHistoryEvaluation

/-! # The positive team on the boot trace used by the checked adaptive profile -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator RoutingISA.CompactMachine
open PackedHistoryCircuit BorderVNP.Cube CellMacro.Generator

variable {w d k : ℕ}

/-- Compare the genuine geometric result after a prescribed local pin with the result
of the complete profiled startup on those very bits. The signed processor, boot trace,
initial memory and pin indices agree at the machine instruction level. -/
theorem profile_at_pin_return (f : BroadcastFrame) {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s : Bank w} {initial : Memory w} {es z saved} (boot : Runs pub mac JointHeader.bootHeader s initial es z saved)
    (stable : f.Stable (readings z)) (positive : (saved f.dst).val ≠ 0)
    (pins : (Fin k → Bool) ≃ Pins.Return pub mac (Function.update z 10 (saved f.dst)) saved)
    (streams : ∀ b, (pins b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b)
    (profile : (Fin k → Bool) ≃ Returns (withStartup pinGeometry) pub mac s initial)
    (guesses : ∀ b, (profile b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b)
    (b : Fin k → Bool) (geo : Returns GeometryAdvice.reconstruct pub mac (pins b).val.2.1 (pins b).val.2.2) :
    (profile b).val.2 = geo.val.2 ∧ geo.val.1.flatMap TeamRAM.Event.choices = [] ∧
      traceCost (profile b).val.1 = traceCost es + 2 + traceCost (pins b).val.1 + traceCost geo.val.1 := by
  obtain ⟨u,mu,pre,head,rfl,start,copy⟩ := Runs.seq_iff.mp boot
  let front := dispatchPrefix f saved pre head
  let all : Returns (withStartup pinGeometry) pub mac s initial :=
    ⟨(front++((pins b).val.1++geo.val.1),geo.val.2),
      (evaluation_startup_iff f pinGeometry start copy stable positive).mpr
        ⟨_,rfl,(pins b).property.seq geo.property⟩⟩
  have noFront : front.flatMap TeamRAM.Event.choices = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro e he
    have small := (dispatchPrefix_effects f start copy).1.choices e he
    exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero small)
  obtain ⟨a,eq⟩ := profile.surjective all
  have stream := guesses a
  rw [eq] at stream
  change (front++((pins b).val.1++geo.val.1)).flatMap TeamRAM.Event.choices = List.ofFn a at stream
  simp only [List.flatMap_append,noFront,streams,List.nil_append] at stream
  have lengths := congrArg List.length stream
  simp only [List.length_append,List.length_ofFn] at lengths
  have rest : geo.val.1.flatMap TeamRAM.Event.choices = [] := List.length_eq_zero_iff.mp (by omega)
  rw [rest,List.append_nil] at stream
  have same := List.ofFn_injective stream
  subst a
  refine ⟨congrArg (fun p => p.val.2) eq,rest,?_⟩
  rw [eq]
  change traceCost (front++((pins b).val.1++geo.val.1)) = _
  simp only [front,dispatchPrefix,traceCost,RAMBuckets.cost_append]
  change (traceCost pre+(traceCost head+2))+(traceCost (pins b).val.1+traceCost geo.val.1) =
    (traceCost pre+traceCost head)+2+traceCost (pins b).val.1+traceCost geo.val.1
  omega

variable {dim box lanes selectors symbols R r t link inner n : ℕ} {Edge : Type}

/-- The positive team at the specified measured continuation, retaining its exact
pin equivalence, packed row functions and clock. -/
def PositiveContinuation.team {id : TableEntry dim box lanes selectors symbols → ℕ} {gen : Fragment IO}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {bank : Bank w} {saved : Memory w}
    {pins : (Fin k → Bool) ≃ Pins.Return pub (install gen n mac) bank saved} {used limit : ℕ}
    (C : PositiveContinuation id gen n pub mac bank saved pins used limit) (burst : ℕ)
    (cap : TeamScales.width n (1/2) ≤ burst) (frame : (pub 0).val+15 < 2^w) : PositiveTeam id gen n w :=
  ⟨pub,mac,bank,saved,k,pins,used,limit,burst,cap,frame,C.room,C.cells,C.window⟩

/-- Construct the physical positive team at a specified boot execution. This version
uses the exact saved state of the adaptive history interpreter and the measured startup
cost, so all local history and cell arguments refer to that same state. -/
theorem positiveMasked_at_boot (id : TableEntry dim box lanes selectors symbols → ℕ) (gen : Fragment IO)
    (G : Wiring R r t d link inner n Edge) (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (args : Fin (R+1) → UnitAddresses) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (u : Fin (R+1)) (limit burst : ℕ) (cap : TeamScales.width n (1/2) ≤ burst)
    (trace : List (TeamRAM.Event w)) (z : Bank w) (saved : Memory w) :
    let ad := args u
    let F := G.processorFields u pin ext ad.ibase ad.hbase ad.starbase
    let f := G.transferFrame u ad.header ad.dst
    let L := G.pinLayout u ad.ibase ad.hbase ad.starbase
    let mac := TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n)
    let bank := Function.update z 10 (saved f.dst)
    Runs (pub u) mac JointHeader.bootHeader (reg u) (processorMemory F w) trace z saved →
    f.Stable (readings z) → (saved f.dst).val ≠ 0 → modeTag (w := w) G args pin ext u ≠ 0 →
    traceCost trace + 2 ≤ limit → ∀ (frame : (pub u 0).val+15 < 2^w)
      (pins : (Fin L.guessWidth → Bool) ≃ Pins.Return (pub u) (install gen n mac) bank saved)
      (C : PositiveContinuation id gen n (pub u) mac bank saved pins (traceCost trace+2) limit),
      let T := C.team burst cap frame
      positiveMaskedNativeValue G (signedBody id) mac pub reg args pin limit burst (n^25) ext u =
          boundedValue (signedBody id) T.pub (install gen n T.routines) T.bank T.memory (T.limit-T.used) T.burst (n^25) := by
  intro ad F f L mac bank boot stable savedPositive tagged room frame pins C T
  obtain ⟨v,mv,first,head,spelling,start,copy⟩ := Runs.seq_iff.mp boot
  have use : traceCost trace=first.length+head.length := by
    rw [spelling,show traceCost (first++head)=traceCost first+traceCost head from RAMBuckets.cost_append ..,
      start.deterministic_cost (by decide),copy.deterministic_cost (by decide)]
  have val := startup_selected_value f (signedBody id) F (reg u) start copy stable (signedBody_withoutAccept id)
    limit burst (n^25) (by rw [use] at room; omega)
  rw [selected,ite_eq_right savedPositive] at val
  rw [positiveMaskedNativeValue,ite_eq_right tagged]
  change packetNative G (signedBody id) mac pub reg args pin limit burst (n^25) ext u =
    boundedValue (signedBody id) (pub u) (install gen n mac) bank saved (limit-(traceCost trace+2)) burst (n^25)
  rw [←siteLibrary_installed gen n,use]
  exact val

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
