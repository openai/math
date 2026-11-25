import OAI.Computability.BorderVNP.CellPacketEncode
import OAI.Computability.BorderVNP.RoutingISACompactWrite

/-! # Sparse external inputs for a private call on the dense sewn cell layout

A fragment names its logical position, physical RAM source and the contiguous
bits received there. The private decoder inserts zeros between fragments. The
report tail follows the supplied bank and is transported verbatim, so its last
count words remain available to the independent finite-field scalar read.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

open RationalHitting.StackLanguage VPVNP.BurstRAM

/-- A true interval of a cell's supplied bank. The native descriptor is exactly
the triple consisting of the relative logical start, physical source and width. -/
structure Span where
  /-- Relative index of the first logical bit. -/
  start : ℕ
  /-- Absolute RAM address at which the received interval begins. -/
  source : ℕ
  /-- The contiguous bit values at the source address. -/
  bits : List Bool
  deriving DecidableEq

/-- Exclusive dense logical endpoint. -/
def Span.stop (s : Span) := s.start+s.bits.length

/-- Three physical scalar words in the chronological source table. -/
def Span.words (s : Span) := [s.start,s.source,s.bits.length]

/-- The dense bank and its physical source agree on every listed bit. -/
def Span.Reads {w : ℕ} (s : Span) (m : Memory w) := CompactWrite.Source m s.source s.bits

/-- All intervals are ordered and disjoint and lie within the logical extent. -/
def Ordered (width : ℕ) : ℕ → List Span → Prop
  | pos,[] => pos ≤ width
  | pos,s::ss => pos ≤ s.start ∧ Ordered width s.stop ss

/-- The compact field uses one marker and two prefix-free words per live
interval. The final marker introduces the trailing zero length and raw report bits. -/
def encode (width : ℕ) (tail : List Bool) : ℕ → List Span → List Bool
  | pos,[] => false :: (codeWord (width-pos).bits ++ tail)
  | pos,s::ss => true :: (codeWord (s.start-pos).bits ++ codeWord s.bits ++ encode width tail s.stop ss)

/-- Private restoration of the supplied slots, in the unchanged logical slot order. -/
def expand (width : ℕ) (tail : List Bool) : ℕ → List Span → List Bool
  | pos,[] => List.replicate (width-pos) false ++ tail
  | pos,s::ss => List.replicate (s.start-pos) false ++ s.bits ++ expand width tail s.stop ss

/-- The zero-filled supplied interval has exactly the declared logical length. -/
theorem expand_length {width pos : ℕ} (tail : List Bool) (ss : List Span) (ordered : Ordered width pos ss) :
    pos+(expand width tail pos ss).length=width+tail.length := by
  induction ss generalizing pos with
  | nil => simp only [expand,List.length_append,List.length_replicate]; change pos ≤ width at ordered; omega
  | cons s ss ih =>
    have h := ih ordered.2
    simp only [expand,List.length_append,List.length_replicate,Span.stop] at h ⊢
    have := ordered.1
    omega

/-- Only addressed live bits, the true report tail and the word-sized interval
boundaries are read or written by the exterior serialization pass. -/
theorem encode_length {w width pos : ℕ} (tail : List Bool) (ss : List Span)
    (ordered : Ordered width pos ss) (fit : width < 2^w) :
    (encode width tail pos ss).length ≤ (2*w+4)*(ss.length+1)+2*(ss.map (fun s => s.bits.length)).sum+tail.length := by
  have finish (p : ℕ) (rows : List Span) (h : Ordered width p rows) : p ≤ width := by
    induction rows generalizing p with
    | nil => exact h
    | cons s ss ih => exact h.1.trans ((Nat.le_add_right ..).trans (ih _ h.2))
  have bitWidth (x : ℕ) (hx : x ≤ width) : x.bits.length ≤ w :=
    Nat.size_eq_bits_len x ▸ Nat.size_le.mpr (hx.trans_lt fit)
  induction ss generalizing pos with
  | nil =>
    have gap := bitWidth (width-pos) (Nat.sub_le ..)
    simp only [encode,List.length_cons,List.length_append,codeWord_length,List.length_nil,List.map_nil,List.sum_nil]
    omega
  | cons s ss ih =>
    have more := ih ordered.2
    have gap := bitWidth (s.start-pos) ((Nat.sub_le ..).trans ((Nat.le_add_right ..).trans (finish _ _ ordered.2)))
    simp only [encode,List.length_cons,List.length_append,codeWord_length,List.map_cons,List.sum_cons]
    rw [Nat.mul_succ]
    omega

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
