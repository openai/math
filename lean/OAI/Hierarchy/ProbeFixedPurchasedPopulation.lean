import OAI.Hierarchy.ProbeFixedCatalystPurchasedLocal
import OAI.Hierarchy.ProbeFixedPayloadPopulation
import OAI.Hierarchy.ProbePublicStageCount
import OAI.Hierarchy.ProbePurchasePopulation
import OAI.Hierarchy.ProbePurchasedBoardEquiv

namespace OAI
/-! # The support of the observed purchased failure test fits the original population -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart
open StripDirectory CatalystArchive PurchaseFrozen BoughtSockets CatalogueRows
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

section Stock
variable (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "G" => v.privateArena P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "s" => v.nativeBoards P z width
local notation "f" => v.nativeFormats P z width

set_option cleanup.letToHave false in
set_option maxHeartbeats 1200000 in
/-- The priced inner test reads the original accepted DFS ordinals through the
literal flag bank. Its support admits an injection into that archived bit set. -/
theorem purchased_population (u h j t : ℕ) (late : v.stripHeight≤z)
    (π : Equiv.Perm (Fin (2^z))) (entry : Memory W)
    (born : PurchasedBirth ((s).outer u h).market.shelf (s).sampler π v.depth ((s).stratumHeader u h) entry k) :
    let e:=Attempt.inner u h j t
    let m:=(guard C e).apply entry
    (Finset.univ.filter (fun i : Fin (f e).market.rows=>(f e).market.failures.live.eval m (i.val:Word W)≠0)).card≤2^z := by
  intro e m
  let sh:=((s).outer u h).market.shelf
  let dated : Shelf:={sh with stockBase:=born.stock}
  let bank:=StripDirectory.flagBank dated (s).sampler z (2^v.W) k v.depth
  let rows:=count z (2^v.W) k*paths z (s).sampler.degree v.depth
  let marks:=actualMarks dated born.phase born.price born.kind born.frozen (k:=k)
  let active:=Finset.univ.filter (fun i : Fin (f e).market.rows=>(f e).market.failures.live.eval m (i.val:Word W)≠0)
  let Active:={i : Fin rows // bank.read entry (i.val:Word W)≠0}
  have size : (f e).market.rows=rows :=
    StripChart.candidate_count F v.mesh (G) P.joint.initial (s) e
  have old : bank.base+bank.size≤(G).base v.mesh (.attempt e) :=
    (v.catalyst_bought_archive_room P z width u h j t).1
  have stop : (G).base v.mesh (.attempt e)≤(C).stopAt e :=
    (v.catalyst_birth_room P z width e).1.trans (min_le_left _ _)
  have reads (i : Fin (f e).market.rows) :
      (f e).market.failures.live.eval m (i.val:Word W)=bank.read entry (i.val:Word W) := by
    change bank.read m (i.val:Word W)=bank.read entry (i.val:Word W)
    let addr:=bank.base+(i.val:Word W).val%bank.size
    have small : addr<(C).stopAt e:=
      (Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos bank.bits)) _).trans_le (old.trans stop)
    change m addr=entry addr
    exact ProtocolRAMGeneratedWrite.frame_image ((C).stopAt e) 1
      (Calendar.stop (C).mesh (C).modeAt e) entry addr (.inl small)
  have compareFlags {n k' : ℕ} (sameRows : n = k') (left right : ℕ → Word W)
      (agree : ∀ i : Fin n, left i.val = right i.val) :
      (Finset.univ.filter (fun i : Fin n => left i.val ≠ 0)).card ≤
        Fintype.card {i : Fin k' // right i.val ≠ 0} := by
    let live := Finset.univ.filter (fun i : Fin n => left i.val ≠ 0)
    let target := {i : Fin k' // right i.val ≠ 0}
    let lift (i : ↥live) : target :=
      ⟨Fin.cast sameRows i.val, fun zero =>
        (Finset.mem_filter.mp i.property).2 ((agree i.val).trans zero)⟩
    have injective : Function.Injective lift := by
      intro i j eq
      exact Subtype.ext (Fin.ext (congrArg (fun x : target => x.val.val) eq))
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective lift injective
  have accepted : active.card ≤ Fintype.card Active :=
    compareFlags size (fun i => (f e).market.failures.live.eval m (i : Word W))
      (fun i => bank.read entry (i : Word W)) reads
  have whole : rows≤2^W := (v.purchased_table_room z late).2.2.1
  have countEq : Fintype.card Active=Fintype.card (LiveChains (s).sampler π v.depth marks) :=
    (packedCount_card dated (s).sampler k v.depth entry whole).symm.trans
      (dated.packedCount_liveChains (s).sampler π v.depth born.phase born.price born.kind born.frozen entry born.saved.flags)
  have cap : Fintype.card (LiveChains (s).sampler π v.depth marks)≤2^z :=
    purchased_card_le (s).sampler π v.depth marks
      (actualMarks_unique dated born.phase born.price born.kind born.frozen) (stages_le_purchased_tiles v.geometry v.positive z)
  change active.card≤2^z
  exact accepted.trans (countEq.le.trans cap)
end Stock

section Origin
variable {K G H R : ℕ} (z width : ℕ) (b : JointHeader.Board) (cat : CatalogueRows.Board)
local notation "eventsN" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
variable (socket : BoughtSockets.Directory ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))
  (r : ℕ) (banks : RouteSettlement.Banks)
  (src tab dst : ℕ) (owners : Bank)
local notation "P" => v.catalystPlacement z K G H R b cat socket
local notation "w" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "core" => CoreRoute.stop v.sampler z v.W k eventsN v.depth K G H R

/-- The public geometry and stratum header at the outer birth and the original
mounted run already imply the population bound at every later inner trial. -/
theorem purchased_population_at (initial : Memory w) (π : Equiv.Perm (Fin (2^z)))
    (u : Fin (v.mesh.inject+v.mesh.cool)) (h : Fin v.mesh.outerFuel)
    (j : Fin v.mesh.reserveSteps) (t : Fin v.mesh.innerFuel) (late : v.stripHeight≤z)
    (whole : Calendar.mounted C (events v.mesh) initial)
    (heap : heapEnd z (2^v.W) copies≤b.initial) (coreRoom : core≤b.initial)
    (geometry : CoreCatalogue.Geometry π (entryMemory C initial (.outer u h)) (2^v.W))
    (header : (Public.keyHead v.sampler (P).routes.column z v.W k v.depth).Loaded
      (entryMemory C initial (.outer u h))) :
    let e:=Attempt.inner u.val h.val j.val t.val
    let market:=(v.nativeFormats P z width e).market
    let m:=(guard C e).apply (entryMemory C initial e)
    (Finset.univ.filter (fun i : Fin market.rows=>market.failures.live.eval m (i.val:Word w)≠0)).card≤2^z := by
  have born:=v.catalyst_birth (K:=K) (G:=G) (H:=H) (R:=R) z width b cat socket r banks src tab dst owners
    initial π u h j t whole u.isLt h.isLt j.isLt t.isLt heap coreRoom geometry header
  exact v.purchased_population P z width r banks src tab dst owners u h j t late π _ born

end Origin
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
