import OAI.Hierarchy.ProbeFixedRowFaces
import OAI.Hierarchy.ProbeFixedActivationParent
import OAI.Hierarchy.ProbeFixedPurchasedPopulation
import OAI.Hierarchy.ProtocolRAMBoughtTerminalPorts
import OAI.Hierarchy.ProtocolRAMBoughtLocations

namespace OAI
/-! # Retained original DFS record at the actual inner post-repair snapshot -/

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
  (slice : Fin v.mesh.reserveSteps) (inner : Fin v.mesh.innerFuel)
local notation "old" => Attempt.outer phase.val trial.val
local notation "a" => Attempt.inner phase.val trial.val slice.val inner.val
local notation "entry" => innerState C initial phase.val trial.val slice.val inner.val
local notation "sh" => ((B).outer phase trial).market.shelf
local notation "hh" => stratumHeader z (2^v.W) k (S).degree v.depth ((B).stratumHeader phase trial)
local notation "pre" => (guard C a).apply entry
local notation "post" => PurchaseStage.postOutput ((C).layout a) (repair C a) (prepared C a entry)

include slice inner in
theorem row_portData (whole : Calendar.mounted C (events v.mesh) initial) (geometry : Shelf.Geometry π initial)
    (heap : heapEnd z (2^v.W) copies≤(A).first) (keyLow : (hh).stop≤(A).first) (keys : (hh).Loaded initial)
    (i : Key z (2^v.W) k) : (sh).PortData S π v.depth i post := by
  let M:=v.frozenMarket P z width phase trial
  let frozen:=v.frozenInput P z width r banks src tab dst owners initial phase trial
  let x₀:=trialState C initial phase trial
  obtain ⟨fixture,input,prepared0,_⟩:=v.activation_parent P z width r banks src tab dst owners initial π phase trial
    phase.isLt trial.isLt whole geometry heap keyLow keys
  have readyOuter:=outer_head_ready whole phase.isLt trial.isLt
  have live : M.ready ((guard C old).apply x₀):=readyOuter.2.1
  obtain ⟨_,_,hd,room,_⟩:=live
  have saved:=M.shelf.portData S π v.depth hd M.phase M.temperature M.kind frozen fixture input prepared0 room i
  have data : M.shelf.PortData S π v.depth i post := by
    apply saved.of_frame (input.dimensions i).room
    intro x cell
    let L:=M.shelf.L S v.depth i
    have block : L.endAddress≤M.shelf.flagsBase S z (2^v.W) k v.depth :=
      (M.shelf.end_le S v.depth i hd).trans ((M.shelf.final_after S v.depth i).trans (Nat.le_add_right ..))
    have extent:=v.catalyst_birth_room P z width old
    have lo : x<(f old).testsStart ∧ x<(A).base v.mesh (.attempt old)+(A).stride := by
      have flagBase : M.shelf.flagsBase S z (2^v.W) k v.depth=(f old).market.flags:=rfl
      have belowFlags : x<M.shelf.flagsBase S z (2^v.W) k v.depth := by
        rcases cell with ctl|localCell
        · have prelude : heapEnd z (2^v.W) copies≤M.shelf.firstBase := input.afterCT
          have begin : M.shelf.firstBase≤M.shelf.flagsBase S z (2^v.W) k v.depth:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
          exact (ctl.trans_le prelude).trans_le begin
        · exact localCell.2.trans_le block
      have inside : x<(f old).market.flags+(f old).market.rows :=
        belowFlags.trans_le (flagBase.le.trans (Nat.le_add_right ..))
      exact ⟨inside,inside.trans_le extent.2.2⟩
    have retained : reserveState C initial phase trial 0 x=
        (M.shelf.result S k v.depth frozen) x :=
      priced_preserves_market v.mesh v.finish (v.basePhase width) f
        (feedColumns (N:=Stages z (2^v.W)) v.mesh A f P.joint.initial width v.keepLimit)
        (P.catalogue.sink r banks src tab dst owners) P.catalogue.idBase
        (fun i=>(StripChart.header F B i).fieldTerm) (StripChart.id F B P.catalogue)
        old x₀ x lo.1 readyOuter
    have kept:=purchase_archive C initial phase trial slice inner x
      (purchaseTail_mounted whole phase.isLt trial.isLt slice.isLt inner.isLt.le)
      (purchaseTail_safe C A phase trial slice inner x
        (fun e y hy=>(v.event_prefix P z width r banks src tab dst owners e y hy).1) lo.2)
    have prior : position v.mesh (.attempt old)<position v.mesh (.attempt a) := by
      change trialBase v.mesh phase.val trial.val <
        trialBase v.mesh phase.val trial.val + 1 + slice.val * sliceSize v.mesh + inner.val
      exact (Nat.lt_succ_self _).trans_le ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    have small:=lo.2.trans_le ((A).apart v.mesh prior)
    obtain ⟨_,cut⟩:=inner_slot C initial phase trial slice inner phase.isLt trial.isLt slice.isLt inner.isLt whole
    exact (Calendar.postOutput_prior C a entry x cut.currentReady (v.event_prefix P z width r banks src tab dst owners _ x small).1).trans
      (kept.trans retained)
  exact ⟨data.tiles,data.directory,data.inputSocket,data.outputSocket,data.back⟩

/-- The failure mask is the saved native decision at this very flat row, so
the inverse of the true decision bijection recovers its original live chain. -/
theorem purchased_post_path (whole : Calendar.mounted C (events v.mesh) initial) (geometry : Shelf.Geometry π initial)
    (heap : heapEnd z (2^v.W) copies≤(A).first) (keyLow : (hh).stop≤(A).first) (keys : (hh).Loaded initial)
    (born : PurchasedBirth sh S π v.depth ((B).stratumHeader phase trial) entry k) (late : v.stripHeight≤z)
    (row : Fin (f a).market.rows) (on : (f a).market.failures.live.eval pre (row.val:Word W)≠0) :
    ∃marks : StageAt z (2^v.W)→Fin k×Bool→Finset (Fin (2^z)),
      (∀t j j' x,x∈marks t j→x∈marks t j'→j=j') ∧
      ∃path : LiveChains S π v.depth marks,(BoughtLocation.relative path).val=row.val ∧
        (sh).PortData S π v.depth (BoughtLocation.keyOf path) post := by
  let dated : Shelf:={sh with stockBase:=born.stock}
  let bank:=flagBank dated S z (2^v.W) k v.depth
  let n:=count z (2^v.W) k*paths z (S).degree v.depth
  let marks:=actualMarks dated born.phase born.price born.kind born.frozen (k:=k)
  have size : (f a).market.rows=n:=candidate_count F v.mesh A P.joint.initial B a
  let ix : Fin n:=⟨row.val,row.isLt.trans_eq size⟩
  have fit : n≤2^W:=(v.purchased_table_room z late).2.2.1
  have fromCurrent : bank.read entry (row.val:Word W)≠0 := by
    have addr:=Nat.add_lt_add_left (Nat.mod_lt (row.val:Word W).val (Nat.two_pow_pos bank.bits)) bank.base
    have low:= (v.catalyst_bought_archive_room P z width phase trial slice inner).1
    have stop:=(v.catalyst_birth_room P z width a).1.trans (min_le_left _ _)
    let loc:=bank.base+(row.val:Word W).val%bank.size
    have prior : loc<(C).stopAt a:=addr.trans_le (low.trans stop)
    have same : pre loc = entry loc :=
      ProtocolRAMGeneratedWrite.frame_image ((C).stopAt a) 1
        (Calendar.stop (C).mesh (C).modeAt a) entry loc (.inl prior)
    change pre loc ≠ 0 at on
    change entry loc ≠ 0
    exact fun zero => on (same.trans zero)
  have live : entry (dated.flagsBase S z (2^v.W) k v.depth+ix.val)≠0 := by
    have small : row.val<bank.size:=ix.isLt.trans (ProtocolRAMPurchaseSampler.lt_span n)
    have wordRoom : row.val < 2^W := ix.isLt.trans_le fit
    change entry (dated.flagsBase S z (2^v.W) k v.depth +
      (row.val : Word W).val % bank.size) ≠ 0 at fromCurrent
    rw [Fin.val_cast_of_lt wordRoom, Nat.mod_eq_of_lt small] at fromCurrent
    exact fromCurrent
  let yes : BoughtLocation.Yes n (dated.flagsBase S z (2^v.W) k v.depth) entry:=⟨ix,live⟩
  let bij:=BoughtLocation.packedEquiv dated («S»:=S) (π:=π) (depth:=v.depth) born.phase born.price born.kind born.frozen entry born.saved.flags
  let path:=bij.symm yes
  have value : (BoughtLocation.relative path).val=row.val := congrArg (fun j : BoughtLocation.Yes n _ entry=>j.val.val)
    (bij.apply_symm_apply yes)
  exact ⟨marks,actualMarks_unique dated born.phase born.price born.kind born.frozen,path,value,
    v.row_portData P z width r banks src tab dst owners initial π phase trial slice inner whole geometry heap keyLow keys _⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
