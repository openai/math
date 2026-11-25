import OAI.Computability.BorderVNP.CellSparseExteriorNativeTail

/-! # Physical descriptor and source invariants for the exterior pass -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior.Native

open VPVNP.BurstRAM RationalHitting.StackLanguage

/-- True initial source rows and bits, checked at their absolute addresses. -/
structure Stored {w : ℕ} (m : Memory w) (table tailBase : ℕ) (ss : List Span) (tail : List Bool) : Prop where
  rows : ∀ i : Fin ss.length, Row m (table+3*i.val) ss[i]
  sources : ∀ r ∈ ss, r.Reads m
  reports : CompactWrite.Source m tailBase tail

/-- All real source addresses and exclusive output cursors fit. Each input
interval is disjoint from the complete compact destination. -/
structure Room (w table tailBase dst outLen : ℕ) (ss : List Span) (tail : List Bool) : Prop where
  tableFits : table+3*ss.length<2^w
  sourcesFit : ∀ r ∈ ss, r.source+r.bits.length<2^w
  reportFits : tailBase+tail.length<2^w
  outputFits : dst+outLen<2^w
  tableApart : CompactWrite.Disjoint table (3*ss.length) dst outLen
  sourcesApart : ∀ r ∈ ss, CompactWrite.Disjoint r.source r.bits.length dst outLen
  reportApart : CompactWrite.Disjoint tailBase tail.length dst outLen

/-- The serialized contribution of one interval before the remaining list. -/
def recordBits (pos : ℕ) (r : Span) : List Bool :=
  true :: (codeWord (r.start-pos).bits ++ codeWord r.bits)

theorem record_length (pos : ℕ) (r : Span) :
    (recordBits pos r).length=1+(codeWord (r.start-pos).bits).length+(codeWord r.bits).length := by
  simp only [recordBits,List.length_cons,List.length_append]; omega

theorem encode_cons (width pos : ℕ) (tail : List Bool) (r : Span) (ss : List Span) :
    encode width tail pos (r::ss)=recordBits pos r++encode width tail r.stop ss := by
  simp only [encode,recordBits,List.cons_append,List.append_assoc]

/-- Removing the first descriptor and its serialized prefix preserves all address bounds. -/
theorem Room.next {w table tb dst k l : ℕ} {r : Span} {ss : List Span} {tail : List Bool}
    (room : Room w table tb dst (k+l) (r::ss) tail) : Room w (table+3) tb (dst+k) l ss tail := by
  have ht := room.tableFits
  simp only [List.length_cons,Nat.mul_succ] at ht
  refine ⟨by omega,fun x hx => room.sourcesFit x (.tail _ hx),room.reportFits,?_,?_,
    fun x hx => (split_apart (room.sourcesApart x (.tail _ hx))).2,(split_apart room.reportApart).2⟩
  · have := room.outputFits
    omega
  · have sep := (split_apart room.tableApart).2
    simp only [List.length_cons,Nat.mul_succ,CompactWrite.Disjoint] at sep ⊢
    omega

theorem Output.unchanged_at {u z : NatState} {bs : List Bool} (effect : Output u bs z)
    {a n j : ℕ} (apart : CompactWrite.Disjoint a n (u.reg 20) bs.length) (lo : a ≤ j) (hi : j<a+n) :
    z.mem j=u.mem j := by
  rw [effect.memory,CellPacketEncode.putDigits_outside _ _ _ _ (by rcases apart with h | h <;> omega)]

/-- Every remaining triple, its original live source, and the raw suffix
survive the exact physical prefix writes. -/
theorem Stored.next {w table tb k : ℕ} {s t : Bank w} {m mt : Memory w} {r : Span} {ss : List Span}
    {tail prefixBits : List Bool} (stored : Stored m table tb (r::ss) tail)
    (room : Room w table tb (readings s 20) (prefixBits.length+k) (r::ss) tail)
    (effect : Output (.ofWords s m) prefixBits (.ofWords t mt)) : Stored mt (table+3) tb ss tail := by
  refine ⟨?_,fun x hx => effect.source (split_apart (room.sourcesApart x (.tail _ hx))).1
    (stored.sources x (.tail _ hx)),effect.source (split_apart room.reportApart).1 stored.reports⟩
  intro i
  have head : Row m (table+3+3*i.val) ss[i] := by
    simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm 3] using stored.rows i.succ
  have saved (j : ℕ) (hj : j<3) : readings mt (table+3+3*i.val+j)=readings m (table+3+3*i.val+j) := by
    apply effect.unchanged_at (split_apart room.tableApart).1
    · omega
    · have bound := i.isLt
      simp only [List.length_cons,Nat.mul_succ]
      omega
  exact ⟨(saved 0 (by decide)).trans head.logical,(saved 1 (by decide)).trans head.physical,
    (saved 2 (by decide)).trans head.length⟩

/-- The exclusive end of every ordered prefix stays in the declared logical bank. -/
theorem ordered_bound {width pos : ℕ} {ss : List Span} (ordered : Ordered width pos ss) : pos ≤ width := by
  induction ss generalizing pos with
  | nil => exact ordered
  | cons r rs ih => exact ordered.1.trans ((Nat.le_add_right ..).trans (ih ordered.2))

end RoutingISA.SparseExterior.Native

end BorderVNP
end Computability
end OAI
