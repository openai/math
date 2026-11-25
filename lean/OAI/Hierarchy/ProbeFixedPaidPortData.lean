import OAI.Hierarchy.ProbeFixedPurchasedRowWitness
import OAI.Hierarchy.ProbeFixedNativeStockRun

namespace OAI
/-! # Genuine original purchase tile and socket records on the final reporter tape -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native CoreBoard AdaptiveProbe PurchaseFrozen
open CatalogueRows BoughtSockets StripDirectory StripChart
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
set_option quotPrecheck false
local notation "W" => wordBits z (2^v.W) copies
local notation "B" => v.nativeBoards P z width
local notation "A" => v.privateArena P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "S" => v.sampler
variable (initial : Memory (wordBits z (2^v.W) copies)) (π : Equiv.Perm (Fin (2^z)))
  (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
local notation "old" => Attempt.outer phase.val trial.val
local notation "sh" => ((B).outer phase trial).market.shelf
local notation "hh" => stratumHeader z (2^v.W) k (S).degree v.depth ((B).stratumHeader phase trial)
local notation "market" => v.frozenMarket P z width phase trial
variable (whole : Calendar.mounted (v.nativeChart P z width r banks src tab dst owners) (events v.mesh) initial)
    (geometry : Shelf.Geometry π initial)
    (heap : heapEnd z (2^v.W) copies ≤ (v.privateArena P z width).first)
    (keyLow : (stratumHeader z (2^v.W) k v.sampler.degree v.depth
      ((v.nativeBoards P z width).stratumHeader phase trial)).stop ≤ (v.privateArena P z width).first)
    (keys : (stratumHeader z (2^v.W) k v.sampler.degree v.depth
      ((v.nativeBoards P z width).stratumHeader phase trial)).Loaded initial)

include whole geometry heap keyLow keys in
theorem terminal_port_data (i : Key z (2^v.W) k) :
    (sh).PortData S π v.depth i (run C (events v.mesh) initial) := by
  obtain ⟨fixture,input,prepared,_⟩:=v.activation_parent P z width r banks src tab dst owners initial π phase trial
    phase.isLt trial.isLt whole geometry heap keyLow keys
  have area : (f old).testsStart ≤ (A).base v.mesh (.attempt old) + (A).stride :=
    (v.catalyst_birth_room P z width old).2.2
  have data:=(priced_portData_terminal (N:=Stages z (2^v.W)) v.mesh v.finish (v.basePhase width) A f P.joint.initial
    width v.keepLimit (P.catalogue.sink r banks src tab dst owners) P.catalogue.idBase
    (fun t=>(StripChart.header F B t).fieldTerm) (StripChart.id F B P.catalogue)
    (v.stock_order P z width) initial phase trial phase.isLt trial.isLt π fixture input prepared whole area i)
  exact ⟨data.tiles,data.directory,data.inputSocket,data.outputSocket,data.back⟩

include whole geometry heap keyLow keys in
theorem checkout_port_data (flag : ℕ) (above : (A).endAddress v.mesh≤flag) (i : Key z (2^v.W) k) :
    (sh).PortData S π v.depth i (checkedOut C flag initial) := by
  obtain ⟨_,input,_,_⟩:=v.activation_parent P z width r banks src tab dst owners initial π phase trial
    phase.isLt trial.isLt whole geometry heap keyLow keys
  have data:=v.terminal_port_data P z width r banks src tab dst owners initial π phase trial whole geometry heap keyLow keys i
  let M:=market
  let L:=M.shelf.L S v.depth i
  have beforeTest:=outer_head_ready whole phase.isLt trial.isLt
  have checked : M.ready ((guard C old).apply (trialState C initial phase trial)):=beforeTest.2.1
  obtain ⟨_,_,hd,_,_⟩:=checked
  have block : L.endAddress≤M.shelf.flagsBase S z (2^v.W) k v.depth :=
    (M.shelf.end_le S v.depth i hd).trans ((M.shelf.final_after S v.depth i).trans (Nat.le_add_right ..))
  obtain ⟨_,slot⟩:=outer_slot C initial phase trial phase.isLt trial.isLt whole
  have occurs : Event.attempt old∈events v.mesh := by
    change Event.attempt old∈events (C).mesh
    rw [slot.events]; simp
  have inside:=(A).within v.mesh (.attempt old) occurs
  have lo:(A).first≤(A).base v.mesh (.attempt old):=Nat.le_add_right ..
  have flags : M.shelf.flagsBase S z (2^v.W) k v.depth=(f old).market.flags := rfl
  apply data.of_frame (input.dimensions i).room
  intro x used
  have below : x<flag := by
    rcases used with small|cell
    · exact small.trans_le (heap.trans (lo.trans ((Nat.le_add_right ..).trans (inside.trans above))))
    · have endAt:=v.catalyst_birth_room P z width old
      have known : x<M.shelf.flagsBase S z (2^v.W) k v.depth := cell.2.trans_le block
      rw [flags] at known
      exact known.trans_le ((Nat.le_add_right ..).trans (endAt.2.2.trans (inside.trans above)))
  rw [checkedOut,ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl below)]
  exact congrArg (fun agenda => run C agenda initial x) (show events (C).mesh = events v.mesh from rfl)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
