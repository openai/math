import OAI.Computability.BorderVNP.GeometryAdviceLiteral
import OAI.Computability.BorderVNP.GeometryOutputStaged
import OAI.Computability.BorderVNP.DiagonalResidueRAMLeadSum
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # From actual processor literals and profile bits to packed public placement words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryAdvice

open VPVNP VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA
open GeometryFrameEncoding DiagonalResidueRAM

variable {u o b w : ℕ}

/-- The gate program, input addresses, validity address, and row-major output addresses. -/
def packet (base start : ℕ) (t : Table (Fin u ⊕ Fin 0) o b) (src : Fin u → ℕ) : List (Word w) :=
  payload w base start t.circuit src ++ GeometryOutput.referenceWords w base t

/-- All staged words are included in the distributed literal length. -/
theorem packet_length (base start : ℕ) (t : Table (Fin u ⊕ Fin 0) o b) (src : Fin u → ℕ) :
    (packet (w := w) base start t src).length = GeometryOutput.packetCount u t.size o b := by
  simp [packet,payload_length,GeometryOutput.packetCount]

/-- The fixed native table, with literal deinterleaving, public gate evaluation, the
validity guard and packing of all selected geometry outputs. -/
def reconstruct : Code := .seq readStripe GeometryOutput.staged

/-- The physical start state of the reconstruction table. The circuit description is
present in actual literal fields and the profile inputs are read through the public
source-address list. This precondition places no decoded advice in scratch. -/
structure PhysicalInput (pub : Arg → Word w) (m : Memory w) (f : BroadcastFrame) (a : Stripe)
    (L : Pins.Layout) (P : Pins.ProcessorFields L) (l : GeometryOutput.Layout) (base start : ℕ)
    (src : Fin u → ℕ) (t : Table (Fin u ⊕ Fin 0) o b) (x : Fin u → Bool) : Prop where
  /-- The parser's field sizes agree with the broadcast program. -/
  dimensions : L.processors = f.processors ∧ L.literal = f.literal ∧ L.stride = f.stride
  /-- Actual time-zero words for the processor fields with geometry stripes installed. -/
  literal : (a.install P (serialized (packet (w := w) base start t src))).ContainsInput m
  /-- The physical input frame. -/
  broadcast : f.At (readings pub) (readings m)
  /-- The geometry stripe's start, per-processor length, dense base, word count and width. -/
  stripe : a.At w (readings pub) (readings m)
  /-- The count agrees with the serialized gate and output-address payload. -/
  count : a.words = GeometryOutput.packetCount u t.size o b
  /-- The unpacker's true directory (frame words 98–101). -/
  pack : GeometryAdvicePrepare.frame98 pub m a.dense start (GeometryOutput.packetCount u t.size o b)
  /-- Output array directory (frame words 104–108). -/
  output : l.loaded pub m
  /-- The circuit's actual public inputs. -/
  sources : ∀ i, m (src i) = wordBit w (x i)
  /-- Copying geometry advice preserves every profile input. -/
  disjoint : ∀ i, src i < a.dense ∨ a.dense+a.words*w ≤ src i

private theorem staged_input (pub : Arg → Word w) (m : Memory w) (f : BroadcastFrame) (a : Stripe)
    (L : Pins.Layout) (P : Pins.ProcessorFields L) (l : GeometryOutput.Layout) (base start : ℕ)
    (src : Fin u → ℕ) (t : Table (Fin u ⊕ Fin 0) o b) (x : Fin u → Bool)
    (space : a.Fits f w (pub 0).val) (h : PhysicalInput pub m f a L P l base start src t x) :
    GeometryOutput.Input pub (a.image f.stride m (a.words*w)) l base start a.dense src t x := by
  have field (j : ℕ) (hj : j ≤ 108) :
      a.image f.stride m (a.words*w) ((pub 0).val+j) = m ((pub 0).val+j) :=
    a.image_outside m (Or.inl (by have := space.afterFrame; omega))
  have hw : 0 < w := by
    by_contra! hw
    have he : w = 0 := by omega
    subst w
    have hn := space.denseFit
    have hb := space.afterFrame
    simp at hn
    omega
  constructor
  case packFrame =>
    unfold GeometryAdvicePrepare.frame98
    simp only [field 98 (by decide),field 99 (by decide),field 100 (by decide),field 101 (by decide)]
    exact h.pack
  case outputFrame =>
    unfold GeometryOutput.Layout.loaded
    simp only [field 104 (by decide),field 105 (by decide),field 106 (by decide),
      field 107 (by decide),field 108 (by decide)]
    exact h.output
  case bits =>
    have bits := a.dense_words P (packet base start t src) m h.literal space.positive
      (h.dimensions.2.1 ▸ space.literal) ((packet_length ..).trans h.count.symm)
      (h.dimensions.1 ▸ space.capacity) hw
    simpa only [h.dimensions.2.2,packet] using bits
  case sources =>
    exact fun i => (a.image_outside m (h.disjoint i)).trans (h.sources i)

/-- True cost bound for the whole ordinary instruction table. -/
def cost (w u k o b : ℕ) :=
  beginStripe.slots + GeometryOutput.packetCount u k o b*w*(copyStripeBit.slots+1) + 1 +
    GeometryOutput.stagedTicks w u k o b

set_option maxRecDepth 4000 in
/-- On a valid profile the native table produces the actual packed output words from the
original Boolean gate model. There are no private branch choices. The bound counts true
RAM ticks and the result includes every untouched memory position. -/
theorem reconstruct_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (f : BroadcastFrame) (a : Stripe) (L : Pins.Layout) (P : Pins.ProcessorFields L)
    (l : GeometryOutput.Layout) (base start : ℕ) (src : Fin u → ℕ) (t : Table (Fin u ⊕ Fin 0) o b)
    (x : Fin u → Bool) (fit : f.Fits w (pub 0).val) (space : a.Fits f w (pub 0).val)
    (layout : GeometryOutput.Placement pub l base start a.dense src t)
    (h : PhysicalInput pub m f a L P l base start src t x)
    (valid : GeometryOutput.validBit t (Sum.elim x Fin.elim0) = true) :
    ∃ es z mz, Runs pub mac reconstruct s m es z mz ∧ traceCost es ≤ cost w u t.size o b ∧
      es.flatMap TeamRAM.Event.choices = [] ∧
      GeometryOutput.Result (a.image f.stride m (a.words*w)) mz l base start t x := by
  obtain ⟨es,v,r,ct⟩ := readStripe_runs a f pub mac s m h.broadcast h.stripe fit space
  obtain ⟨z,mz,⟨fs,rs,tr⟩,result⟩ := GeometryOutput.staged_runs pub mac v _ l base start a.dense src t x
    layout (staged_input pub m f a L P l base start src t x space h) valid
  have actual := (plain_return GeometryOutput.staged (by decide) rs).1
  have used : es.flatMap TeamRAM.Event.choices = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    exact fun e he => (r.unsigned_events (by decide) e he).1
  refine ⟨_,z,mz,r.seq rs,?_,by simp only [List.flatMap_append,used,tr.2.1,List.nil_append],result⟩
  rw [show traceCost (es++fs) = traceCost es+traceCost fs from RAMBuckets.cost_append ..,actual,tr.1]
  exact Nat.add_le_add_right (h.count ▸ ct) _

/-- False validity prevents a return from every execution of the physical reconstruction
program, even when the caller supplies an arbitrary ambient choice tape. -/
theorem reconstruct_invalid (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (f : BroadcastFrame) (a : Stripe) (L : Pins.Layout) (P : Pins.ProcessorFields L)
    (l : GeometryOutput.Layout) (base start : ℕ) (src : Fin u → ℕ) (t : Table (Fin u ⊕ Fin 0) o b)
    (x : Fin u → Bool) (fit : f.Fits w (pub 0).val) (space : a.Fits f w (pub 0).val)
    (layout : GeometryOutput.Placement pub l base start a.dense src t)
    (h : PhysicalInput pub m f a L P l base start src t x)
    (invalid : GeometryOutput.validBit t (Sum.elim x Fin.elim0) = false)
    {es z mz} : ¬ Runs pub mac reconstruct s m es z mz := by
  obtain ⟨ds,v,r,ct⟩ := readStripe_runs a f pub mac s m h.broadcast h.stripe fit space
  intro run
  cases run with
  | atom hh _ _ => cases hh
  | seq first rest =>
    obtain ⟨rfl,rfl,rfl⟩ := first.unique_of_deterministic (by decide) r
    exact GeometryOutput.staged_invalid_no_run pub mac _ _ l base start a.dense src t x layout
      (staged_input pub m f a L P l base start src t x space h) invalid rest

end GeometryAdvice

end BorderVNP
end Computability
end OAI
