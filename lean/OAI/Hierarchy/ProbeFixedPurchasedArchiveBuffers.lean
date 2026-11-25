import OAI.Hierarchy.ProbeFixedPurchasedArchiveRows
import OAI.Hierarchy.ProbeFixedCatalystBirth
import OAI.Hierarchy.ProbeFixedQuoteFrames

namespace OAI
/-! # Live archive reads through the purchased guard, ballot and commit -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StripDirectory
open PurchaseFrozen PurchaseStage
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "bs" => v.nativeBoards P z width
local notation "G" => v.privateArena P z width
variable (u h j t : ℕ) (entry : Memory (wordBits z (2^v.W) copies)) (π : Equiv.Perm (Fin (2^z)))
local notation "ev" => Attempt.inner u h j t
local notation "sh" => ((bs).outer u h).market.shelf
local notation "S" => (bs).sampler
local notation "h₀" => stratumHeader z (2^v.W) k (S).degree v.depth ((bs).stratumHeader u h)
local notation "pre" => (guard C ev).apply entry
local notation "checked" => postSnapshot ((C).layout ev) (repair C ev) (prepared C ev entry)
local notation "stage" => v.stage P z width r banks src tab dst owners ev entry
local notation "base" => (G).base v.mesh (.attempt ev)

theorem purchased_archive_cell (stock : ℕ) (headLow : (h₀).stop≤base) (x : ℕ)
    (used : ArchiveCell (z:=z) (d:=2^v.W) (k:=k) {sh with stockBase:=stock} S v.depth ((bs).stratumHeader u h) x) :
    x<base := by
  let dated : Shelf:={sh with stockBase:=stock}
  let bank:=StripDirectory.flagBank sh S z (2^v.W) k v.depth
  have room:=v.catalyst_bought_archive_room P z width u h j t
  rcases used with ⟨key,i,pos,rfl⟩|⟨key,i,rfl⟩|header
  · exact ((dated.L S v.depth key).source_range i pos).2.trans_le (v.catalyst_bought_stage_room P z width u h j t key)
  · have keyBound : key.val+1 ≤ PurchaseFrozen.count z (2^v.W) k := key.isLt
    have upper:=Nat.mul_le_mul_right (PurchaseFrozen.paths z (S).degree v.depth) keyBound
    rw [Nat.succ_mul] at upper
    have rowBound := (Nat.add_lt_add_left i.isLt (key.val*PurchaseFrozen.paths z (S).degree v.depth)).trans_le upper
    have span:=ProtocolRAMPurchaseSampler.lt_span (PurchaseFrozen.count z (2^v.W) k*PurchaseFrozen.paths z (S).degree v.depth)
    have early : bank.base+ProtocolRAMPurchaseSampler.span (PurchaseFrozen.count z (2^v.W) k*PurchaseFrozen.paths z (S).degree v.depth)≤base:=room.1
    change bank.base+key.val*PurchaseFrozen.paths z (S).degree v.depth+i.val<base
    simpa only [Nat.add_assoc] using (Nat.add_lt_add_left (rowBound.trans span) bank.base).trans_le early
  · exact header.2.trans_le headLow

/-- The guard only writes its stop cell, so archive entrance does not require
the later repair phase to be ready. -/
theorem purchased_guard_archive_reads (headLow : (h₀).stop≤base)
    (born : PurchasedBirth sh S π v.depth ((bs).stratumHeader u h) entry k) :
    ArchiveReads {sh with stockBase := born.stock} S π v.depth ((bs).stratumHeader u h)
      born.phase born.price born.kind born.frozen pre k := by
  have frame (x : ℕ) (low : x<base) : pre x=entry x := by
    have below:=(v.event_prefix P z width r banks src tab dst owners (.attempt ev) x low).1.1
    simp [guard,Pass.apply,image,ThreeFlat.RAM.fillSegment,not_le.mpr below]
  exact born.saved.change (n:=pre) (fun x used=>frame x
    (v.purchased_archive_cell P z width u h j t born.stock headLow x used))

theorem purchased_guard_archive (headLow : (h₀).stop≤base)
    (born : PurchasedBirth sh S π v.depth ((bs).stratumHeader u h) entry k) :
    (h₀).Loaded pre ∧ ∀key : Key z (2^v.W) k,ProtocolRAMPurchaseGateColumns.TileRows
      ((sh).L S v.depth key).source (Shelf.pathRows S π v.depth key) pre := by
  have kept := v.purchased_guard_archive_reads P z width r banks src tab dst owners u h j t entry π headLow born
  exact ⟨kept.header,kept.tiles⟩

theorem purchased_guard_archive_flags (headLow : (h₀).stop≤base)
    (born : PurchasedBirth sh S π v.depth ((bs).stratumHeader u h) entry k) :
    StoredFlags {sh with stockBase := born.stock} S π v.depth born.phase born.price born.kind born.frozen pre k :=
  (v.purchased_guard_archive_reads P z width r banks src tab dst owners u h j t entry π headLow born).flags

/-- A single true birth supplies the same path archive throughout each of the
three inspected RAM states. The bank address is independent of the old price
pointer, while its accepted decisions use that exact old pointer. -/
def purchased_row_archive (live : ready C (.attempt ev) entry) (headLow : (h₀).stop≤base)
    (born : PurchasedBirth sh S π v.depth ((bs).stratumHeader u h) entry k) :
    v.PurchasedArchiveRows P z width r banks src tab dst owners u h j t entry π := by
  let dated : Shelf:={sh with stockBase:=born.stock}
  let bank:=StripDirectory.flagBank sh S z (2^v.W) k v.depth
  have room:=v.catalyst_bought_archive_room P z width u h j t
  have bounded := v.purchased_archive_cell P z width u h j t born.stock headLow
  have frames := v.row_buffer_frame P z width r banks src tab dst owners ev entry live
  have guardData := born.saved.change (n:=pre) (fun x used=>(frames x (bounded x used)).1)
  have checkData := born.saved.change (n:=checked) (fun x used=>(frames x (bounded x used)).2.1)
  have stageData := born.saved.change (n:=stage) (fun x used=>(frames x (bounded x used)).2.2)
  refine ⟨born.stock,born.phase,born.price,born.kind,born.frozen,guardData.header,checkData.header,stageData.header,
    guardData.tiles,checkData.tiles,stageData.tiles,stageData.flags,?_⟩
  intro i
  have addr:=(Nat.add_lt_add_left (Nat.mod_lt (i.val:Word W).val (Nat.two_pow_pos bank.bits)) bank.base).trans_le room.1
  exact (frames _ addr).2.2.trans (frames _ addr).1.symm

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
