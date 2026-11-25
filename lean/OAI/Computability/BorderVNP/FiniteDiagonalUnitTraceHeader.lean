import OAI.Computability.BorderVNP.FiniteDiagonalUnitTraceTuple
import OAI.Computability.BorderVNP.DiagonalNativeEvalPacket
import OAI.Computability.BorderVNP.FiniteWideBootRun

/-! # Common first bit on every accepted full tuple of finite team processors

The startup may be the multi-bit loader. Soundness of the actual broadcast
comparison forces agreement at the two ends of each shared physical link.
Every accepting team therefore reads the same zero-or-one selector.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM TeamContraction RoutingISA RoutingISA.Pins RoutingISA.Evaluator
open scoped Classical

/-- The chronological startup, shared-header read and branch selection of one team. -/
def dispatchTable (boot eval : Code) : Code := .seq boot (.seq readBroadcast (select eval))

/-- A returning boot on the genuine header with the unchanged exterior words and
the installed scalar frame used by the following broadcast scan. -/
structure BootSnapshot {R r t d link inner n w : ℕ} {Edge : Type}
    (G : Wiring R r t d link inner n Edge) (u : Fin (R+1)) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (ibase hbase starbase header dst : ℕ)
    (boot : Code) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w) where
  /-- True chronological startup events. -/
  events : List (TeamRAM.Event w)
  /-- Post-startup register bank. -/
  registers : Bank w
  /-- Post-startup shared memory. -/
  mem : Memory w
  /-- Normal execution from the physical processor input. -/
  run : Runs pub mac boot bank (processorMemory (G.processorFields u pin ext ibase hbase starbase) w)
    events registers mem
  /-- Every original processor input word has its true value. -/
  input : (G.processorFields u pin ext ibase hbase starbase).ContainsInput mem
  /-- The scalar frame points at this team's physical broadcast and destination. -/
  frame : (G.transferFrame u header dst).At (readings pub) (readings mem)
  /-- All addresses and the nonempty reference prefix fit the physical word width. -/
  fit : (G.transferFrame u header dst).Fits w (pub 0).val

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
  {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {boot eval : Code}

/-- A bounded path of the complete fetched table can exist only if the actual
post-startup memory passes the incident-header comparisons. -/
theorem BootSnapshot.agrees {u : Fin (R+1)} {ibase hbase starbase header dst : ℕ}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {bank : Bank w}
    (b : BootSnapshot G u pin ext ibase hbase starbase header dst boot pub mac bank)
    (det : boot.deterministic = true) (returns : (dispatchTable boot eval).withoutAccept = true)
    {ticks burst clock : ℕ}
    (p : NativePath (processorMachine (dispatchTable boot eval) pub mac bank
      (G.processorFields u pin ext ibase hbase starbase)) ticks burst clock) :
    (G.transferFrame u header dst).Agrees (readings b.mem) := by
  obtain ⟨⟨z,mz,run⟩,_⟩ := (Code.execute_iff_runs returns).mp p.property.1
  obtain ⟨s,m,_,_,_,pre,tail⟩ := Runs.seq_iff.mp run
  obtain ⟨_,rfl,rfl⟩ := pre.unique_of_deterministic det b.run
  obtain ⟨_,_,_,_,_,bc,_⟩ := Runs.seq_iff.mp tail
  have bits := (G.broadcast_input u pin ext ibase hbase starbase header dst b.mem b.input b.fit).1
  exact ((readBroadcast_test _ pub mac _ _ b.frame b.fit bits).sound bc).1

/-- The word tested at the reference position by every team in an accepting native tuple
is one common Boolean value, including on the all-batch finite boot program. -/
theorem acceptedTuple_commonTag
    (ibase hbase starbase header dst : Fin (R+1) → ℕ) (pub : Fin (R+1) → Arg → Word w)
    (mac : Fin (R+1) → TeamOpcode.Macros w 8) (bank : Fin (R+1) → Bank w)
    (snap : ∀ u, BootSnapshot G u pin ext (ibase u) (hbase u) (starbase u) (header u) (dst u)
      boot (pub u) (mac u) (bank u))
    (det : boot.deterministic = true) (returns : (dispatchTable boot eval).withoutAccept = true) :
    let f (u) := G.transferFrame u (header u) (dst u)
    let M (u) := processorMachine (dispatchTable boot eval) (pub u) (mac u) (bank u)
      (G.processorFields u pin ext (ibase u) (hbase u) (starbase u))
    ∀ bnd : ∀ u, Bounds r (M u).inputSize, NativeTuple M bnd →
      ∃ tag : Bool, ∀ u, readings (snap u).mem ((f u).addr (f u).partner 0) = tag.toNat := by
  intro f M bnd paths
  let val (u : Fin (R+1)) := readings (snap u).mem ((f u).addr (f u).partner 0)
  have atEdge (u v : Fin (R+1)) (hne : u ≠ v) :
      readings (snap u).mem ((f u).addr v 0) = val u :=
    (snap u).agrees det returns (paths u) v v.isLt (fun h => hne (Fin.ext h.symm)) 0 (snap u).fit.branch
  have allEqual (u v : Fin (R+1)) : val u = val v := by
    by_cases he : u = v
    · rw [he]
    have cap := (snap u).fit.branch.trans_le (snap u).fit.cap
    let pos : Fin (r*link) := ⟨0, by simpa [Wiring.transferFrame,BroadcastFrame.capacity,Nat.mul_comm] using cap⟩
    have wire := G.read_exterior_swap u v he pin ext (ibase u) (hbase u) (starbase u)
      (ibase v) (hbase v) (starbase v) (snap u).mem (snap v).mem (snap u).input (snap v).input pos
    exact (atEdge u v he).symm.trans ((congrArg Fin.val wire).trans (atEdge v u (Ne.symm he)))
  have bits := (G.broadcast_input 0 pin ext (ibase 0) (hbase 0) (starbase 0) (header 0) (dst 0)
    (snap 0).mem (snap 0).input (snap 0).fit).1 0 (snap 0).fit.branch
  change val 0 < 2 at bits
  by_cases hz : val 0 = 0
  · exact ⟨false,fun u => (allEqual u 0).trans hz⟩
  · exact ⟨true,fun u => (allEqual u 0).trans (by change val 0 = 1; omega)⟩

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
