import OAI.Hierarchy.DescentPhysicalMixedCapture

namespace OAI
/-! # Reading the two native sectors at the receiver's actual calendar address -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSIMDLookup DescentPackedZip DescentResetDenseOperand DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {date : PhysicalReset} {floor w : ℕ} {u : date.DateInputs floor w} {N : ℕ} (R : u.MeasuredChannels N)
local notation "D₀" => u.masked
local notation "v₀" => date.successor
local notation "s₀" => (v₀).sheets
local notation "channels" => R.capturedChannels
local notation "cell" => DescentResetFieldAssembler.Meta
local notation:max "out" m:arg => (D₀).image (u.privateResult m)
local notation:max "words" n:arg h:arg g:arg => DescentCandidateMaskRAM.render ((channels).maskValues R.names n h g)
local notation "encode" => DescentResetFieldAssembler.raw (D₀).field

private theorem packed_ghost (job : ℕ) (h : Fin (D₀).hosts) (g : Fin (D₀).groups) (ghost : ¬h.val<N) :
    words job h g=encode DescentResetFieldAssembler.Meta.blank:=by
  apply DescentCandidateMaskRAM.vacant_or_empty _ (.inl ?_)
  change ((channels).work R.names job h g).val=0
  rcases hJob : date.successor.jobAt job with _ | (⟨x,q⟩ | ⟨x,q⟩) <;>
    simp [CandidateChannels.work,hJob,dense,ghost]

theorem mixed_source (job : ℕ) (live : job<(D₀).jobs) (fees : Fin N→Fin (D₀).groups→cell)
    (m : Memory w) (ok : u.Ready) (seen : CaptureRoom R m)
    (shapes : ∀x q (i : Fin 3),i.val<2 → ∀(h : Fin N) g,
      ((channels).privateFields x q i (R.names h) g).val<(v₀).front.peer.shapes)
    (lanes : 0<(D₀).lanes) (rankFit : (D₀).lanes*max ((D₀).field*5) (D₀).field≤w/2)
    (maskFit : (D₀).lanes*max ((D₀).field*9) ((D₀).field*7)≤w/2)
    (observed : ∀h g,words job ((h : Fin N).castLE seen.used) g=encode (fees h g)) :
    Source (.lookup ((D₀).output job) .row)
      (fun (h : Fin (D₀).hosts) g=>encode (if present:h.val<N then fees ⟨h.val,present⟩ g else DescentResetFieldAssembler.Meta.blank)) (D₀).lanes (out m):=by
  have source:=published_channels R ok m seen shapes lanes rankFit maskFit job live
  convert source using 1
  funext h g
  by_cases inside : h.val<N
  · rw [dite_eq_left inside]
    exact (observed ⟨_,inside⟩ g).symm
  · rw [dite_eq_right inside]
    exact (packed_ghost R job h g inside).symm

structure SheetGeometry (u : date.DateInputs floor w) : Prop where
  counts : (s₀).jobs=(s₀).blocks*((s₀).contacts+(s₀).privates)
  contacts : (s₀).contacts=(v₀).contactShape.sockets
  privates : (s₀).privates=(v₀).privateShape.keys
  contactBlocks : (s₀).blocks=(v₀).contactShape.blocks
  privateBlocks : (s₀).blocks=(v₀).privateShape.blocks

/-- The exact expressions that the final field book reads in the two mixed sectors. -/
theorem sector_sources (bounds : SheetGeometry u) (x : Fin (s₀).blocks)
    (charged : Fin (s₀).contacts→Fin N→Fin (D₀).groups→cell)
    (attached : Fin (s₀).privates→Fin N→Fin (D₀).groups→cell)
    (m : Memory w) (ok : u.Ready) (seen : CaptureRoom R m)
    (shapes : ∀x q (i : Fin 3),i.val<2 → ∀(h : Fin N) g,
      ((channels).privateFields x q i (R.names h) g).val<(v₀).front.peer.shapes)
    (lanes : 0<(D₀).lanes) (rankFit : (D₀).lanes*max ((D₀).field*5) (D₀).field≤w/2)
    (maskFit : (D₀).lanes*max ((D₀).field*9) ((D₀).field*7)≤w/2)
    (payment : ∀q h g,words (x.val*((s₀).contacts+(s₀).privates)+q.val) ((h : Fin N).castLE seen.used) g=encode (charged q h g))
    (assigned : ∀q h g,words (x.val*((s₀).contacts+(s₀).privates)+((s₀).contacts+q.val)) ((h : Fin N).castLE seen.used) g=encode (attached q h g)) :
    (∀q,Source (u.sectorHeader x.val (.inr (.inr (.inl q)))) (fun (h : Fin (D₀).hosts) g=>encode
      (if hit:h.val<N then charged q ⟨h.val,hit⟩ g else DescentResetFieldAssembler.Meta.blank)) (D₀).lanes (out m)) ∧
    ∀q,Source (u.sectorHeader x.val (.inr (.inr (.inr q)))) (fun (h : Fin (D₀).hosts) g=>encode
      (if hit:h.val<N then attached q ⟨h.val,hit⟩ g else DescentResetFieldAssembler.Meta.blank)) (D₀).lanes (out m):=by
  let span:=(s₀).contacts+(s₀).privates
  have index (j : ℕ) (ls : j<span) : x.val*span+j<(D₀).jobs:=by
    change _<(s₀).jobs
    rw [bounds.counts]
    exact (Nat.add_lt_add_left ls _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right span x.isLt)
  constructor
  · intro q
    exact mixed_source R _ (index q.val (q.isLt.trans_le (Nat.le_add_right ..))) (charged q) m ok seen shapes
      lanes rankFit maskFit (payment q)
  · intro q
    exact mixed_source R _ (index _ (Nat.add_lt_add_left q.isLt _)) (attached q) m ok seen shapes
      lanes rankFit maskFit (assigned q)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
