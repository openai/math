import OAI.ThreeFlat.Diagonal.TraceMemoryCircuit
import OAI.ThreeFlat.Diagonal.TraceBinaryWitness

namespace OAI
/-! # Putting physical memory-check sites on the shared binary messages -/

namespace ThreeFlat.Diagonal.TraceMemoryCircuit

open Computability.VPVNP BurstRAM RAMSort RAMMemory RAMSerialization
open TraceSlots TraceSortSite TraceRows TraceRecordSort TraceWords

variable {d w : ℕ}

private def emptyBits (hw : 2 ≤ w) := (slotFormat hw).encode none

/-- Bits on the predecessor edge at a site, with a canonical empty slot at the first site. -/
def incomingBits (hw : 2 ≤ w) (z : SortBits d w) : Fin (2^d) → Fin (7*w) → Bool
  | ⟨0,_⟩ => emptyBits hw
  | ⟨j+1,h⟩ => z.2 ⟨j,by omega⟩

/-- The last site has no successor, so its unused output port reads canonical padding. -/
def outgoingBits (hw : 2 ≤ w) (z : SortBits d w) (v : Fin (2^d)) : Fin (7*w) → Bool :=
  if h : v.val+1 < 2^d then z.2 ⟨v.val,by omega⟩ else emptyBits hw

/-- Realize all local pin names against the same outgoing bit arrays. The
other end of a cross-layer wire belongs to that layer's geometric partner. -/
def inputAt (hw : 2 ≤ w) (cur : Fin 2 → Narrow w) (v : Fin (2^d)) (z : SortBits d w) :
    Port d w → Bool
  | .inl (i,f,j) => (slotFormat hw).encode (cur i) (finProdFinEquiv (f,j))
  | .inr (.inl (l,own,i,f,j)) =>
      z.1 l (if own then v else ((RAMLayout.layerEquiv d).symm l).partner v) i (finProdFinEquiv (f,j))
  | .inr (.inr (false,f,j)) => incomingBits hw z v (finProdFinEquiv (f,j))
  | .inr (.inr (true,f,j)) => outgoingBits hw z v (finProdFinEquiv (f,j))

private theorem bits_eq_encode (hw : 2 ≤ w) (a : Fin (7*w) → Bool) (r : Narrow w) :
    (∀ f j, a (finProdFinEquiv (f,j)) = bits (fields hw r f) j) ↔
      a = (slotFormat hw).encode r := by
  constructor
  · intro h
    funext i
    obtain ⟨⟨f,j⟩,rfl⟩ := finProdFinEquiv.surjective i
    exact (h f j).trans (slotFormat_encode_at ..).symm
  · rintro rfl
    exact slotFormat_encode_at hw r

private theorem incoming_write (hw : 2 ≤ w) (m : Packed d w) (v : Fin (2^d)) :
    incomingBits hw (writeSort hw m) v = (slotFormat hw).encode (incoming m v) := by
  cases v with | mk v hv => cases v <;> rfl

private theorem outgoing_write (hw : 2 ≤ w) (m : Packed d w) (v : Fin (2^d)) :
    outgoingBits hw (writeSort hw m) v = (slotFormat hw).encode (outgoing m v) := by
  unfold outgoingBits outgoing
  split <;> rfl

theorem core_on_write (hw : 2 ≤ w) (cur : Fin 2 → Narrow w) (v : Fin (2^d)) (m : Packed d w) :
    ((core v).circuit ()).eval (inputAt hw cur v (writeSort hw m)) = true ↔
      MemoryAt (unpack m) v (toOrdered ∘ cur) := by
  apply core_typed hw
  · intro i f j
    exact slotFormat_encode_at ..
  · intro l own i
    dsimp only
    intro f j
    exact slotFormat_encode_at ..
  · intro f j
    change incomingBits hw (writeSort hw m) v _ = _
    rw [incoming_write, slotFormat_encode_at]
  · intro f j
    change outgoingBits hw (writeSort hw m) v _ = _
    rw [outgoing_write, slotFormat_encode_at]

private theorem owner_on_write (hw : 2 ≤ w) (cur : Fin 2 → Narrow w) (v : Fin (2^d)) (m : Packed d w) :
    OwnerValid hw v (inputAt hw cur v (writeSort hw m)) := by
  constructor
  · intro l i
    exact ⟨_, fun f j => slotFormat_encode_at hw (m.1 ((RAMLayout.layerEquiv d).symm l) v i) f j⟩
  · intro _
    refine ⟨outgoing m v, fun f j => ?_⟩
    change outgoingBits hw (writeSort hw m) v _ = _
    rw [outgoing_write, slotFormat_encode_at]

/-- Validating just the outgoing copy at each site enforces precisely the
global canonicality condition for every shared message, once per edge. -/
theorem owners_iff (hw : 2 ≤ w) (initials : Fin (2^d) → Fin 2 → Narrow w) (z : SortBits d w) :
    (∀ v, OwnerValid hw v (inputAt hw (initials v) v z)) ↔ writeSort hw (readSort hw z) = z := by
  constructor
  · intro H
    apply Prod.ext
    · funext l v i
      obtain ⟨r,h⟩ := (H v).1 l i
      have hz := (bits_eq_encode hw (z.1 l v i) r).mp h
      simp [writeSort, readSort, hz, Format.encode]
    · funext j
      let v : Fin (2^d) := ⟨j.val,by have := j.isLt; omega⟩
      have hv : v.val+1 < 2^d := by dsimp [v]; have := j.isLt; omega
      obtain ⟨r,h⟩ := (H v).2 hv
      have h' : ∀ f i, z.2 j (finProdFinEquiv (f,i)) = bits (fields hw r f) i := by
        intro f i
        simpa [inputAt, boundary, outgoingBits, v, hv] using h f i
      have hz := (bits_eq_encode hw (z.2 j) r).mp h'
      simp [writeSort, readSort, hz, Format.encode]
  · intro hz v
    rw [← hz]
    exact owner_on_write hw _ _ _

/-- The complete memory predicate on arbitrary bit assignments, given bounded
initial slots, equals simultaneous acceptance of the physical site circuits. -/
theorem rows_iff (hw : 2 ≤ w) (initials : Fin (2^d) → Fin 2 → Narrow w) (z : SortBits d w) :
    (∀ v, ((row hw v).circuit ()).eval (inputAt hw (initials v) v z) = true) ↔
      writeSort hw (readSort hw z) = z ∧
        ∀ v, MemoryAt (unpack (readSort hw z)) v (toOrdered ∘ initials v) := by
  constructor
  · intro h
    have both := fun v => (row_split hw v _).mp (h v)
    have hz := (owners_iff hw initials z).mp fun v => (both v).1
    refine ⟨hz, fun v => (core_on_write hw _ _ _).mp ?_⟩
    rw [hz]
    exact (both v).2
  · rintro ⟨hz,h⟩ v
    apply (row_split hw v _).mpr
    refine ⟨(owners_iff hw initials z).mpr hz v, ?_⟩
    have hc := (core_on_write hw _ _ _).mpr (h v)
    simpa only [hz] using hc

/-- Narrow the two bounded records at each input site, in the block's exact
`2*v+i` order. -/
def initialSlots (S d : ℕ) (header : ℕ → Word w) (es : List (Event w))
    (hs : S ≤ 2^w) (ht : es.length ≤ 2^w) (v : Fin (2^d)) (i : Fin 2) : Narrow w :=
  narrowSlot ((wire S (1+d) header es (v.val*2+i.val)).record)
    (wire_fitsWord S (1+d) header es hs ht _)

theorem initialSlots_ordered (S d : ℕ) (header : ℕ → Word w) (es : List (Event w))
    (hs : S ≤ 2^w) (ht : es.length ≤ 2^w) (v : Fin (2^d)) :
    toOrdered ∘ initialSlots S d header es hs ht v = block 1 v.val (wire S (1+d) header es) := by
  funext i
  apply congrArg OrderedSlot.mk
  exact widen_narrowSlot _ _

theorem rows_iff_memoryPass (hw : 2 ≤ w) (S d : ℕ) (header : ℕ → Word w) (es : List (Event w))
    (hs : S ≤ 2^w) (ht : es.length ≤ 2^w) (z : SortBits d w) :
    (∀ v, ((row hw v).circuit ()).eval
      (inputAt hw (initialSlots S d header es hs ht v) v z) = true) ↔
      memoryPass hw S d header es z := by
  rw [rows_iff]
  unfold memoryPass
  apply and_congr_right
  intro _
  apply forall_congr'
  intro v
  rw [initialSlots_ordered S d header es hs ht v]

end ThreeFlat.Diagonal.TraceMemoryCircuit

end OAI
