import OAI.Hierarchy.ProbeFixedPaidPortData
import OAI.Hierarchy.ProbeFixedSourceGeometry

namespace OAI
/-! # The authenticated original bought socket after the final calendar event -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native CoreBoard AdaptiveProbe PurchaseFrozen
open CatalogueRows BoughtSockets StripDirectory StripChart
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "B" => v.nativeBoards P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "S" => v.sampler
variable (initial : Memory (wordBits z (2^v.W) copies)) (π : Equiv.Perm (Fin (2^z)))
  (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
local notation "old" => Attempt.outer phase.val trial.val
local notation "sh" => ((B).outer phase trial).market.shelf
local notation "hh" => stratumHeader z (2^v.W) k (S).degree v.depth ((B).stratumHeader phase trial)

theorem terminal_port_read
    (whole : Calendar.mounted (v.nativeChart P z width r banks src tab dst owners) (events v.mesh) initial)
    (geometry : Shelf.Geometry π initial) (heap : heapEnd z (2^v.W) copies≤(A).first)
    (keyLow : (hh).stop≤(A).first) (keys : (hh).Loaded initial)
    (m : Memory W) (saved : ∀x,x<(A).endAddress v.mesh→m x=run C (events v.mesh) initial x)
    (i : Key z (2^v.W) k) : (sh).PortData S π v.depth i m := by
  let market := v.frozenMarket P z width phase trial
  obtain ⟨_,input,_,_⟩ := v.activation_parent P z width r banks src tab dst owners initial π phase trial
    phase.isLt trial.isLt whole geometry heap keyLow keys
  have source := v.terminal_port_data P z width r banks src tab dst owners initial π phase trial whole geometry
    heap keyLow keys i
  have ready := outer_head_ready whole phase.isLt trial.isLt
  have checked : market.ready ((guard C old).apply (trialState C initial phase trial)) := ready.2.1
  obtain ⟨_,_,dimension,_,_⟩ := checked
  have blockEnd : (market.shelf.L S v.depth i).endAddress ≤ market.shelf.flagsBase S z (2^v.W) k v.depth :=
    (market.shelf.end_le S v.depth i dimension).trans ((market.shelf.final_after S v.depth i).trans (Nat.le_add_right ..))
  have flags : market.shelf.flagsBase S z (2^v.W) k v.depth = (f old).market.flags := rfl
  have extent := (A).within v.mesh (.attempt old) (dated_outer_occurs v.mesh phase trial)
  have first : (A).first ≤ (A).base v.mesh (.attempt old) := Nat.le_add_right ..
  apply source.of_frame (input.dimensions i).room
  intro x used
  apply saved x
  rcases used with geometryCell | socketCell
  · exact geometryCell.trans_le (heap.trans (first.trans ((Nat.le_add_right ..).trans extent)))
  · have beforeFlags : x < market.shelf.flagsBase S z (2^v.W) k v.depth := socketCell.2.trans_le blockEnd
    rw [flags] at beforeFlags
    have flagsEnd := (v.catalyst_birth_room P z width old).2.2
    exact beforeFlags.trans_le ((Nat.le_add_right ..).trans (flagsEnd.trans extent))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
