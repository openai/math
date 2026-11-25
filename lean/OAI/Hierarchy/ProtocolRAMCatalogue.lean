import OAI.Hierarchy.ProtocolRAMBatch
import OAI.Hierarchy.ProbeBatchReplacement

namespace OAI
/-! # Real, finite replacement packets in the padded runtime alphabet -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open LinearAlgebra.SpectralBooks.ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Fin.CommRing BigOperators

variable {w k n d t : ℕ} {F A E : Type*} [Field F] [Nonempty (Fin k)] [Fintype E] [Fintype A]
  {edge : E → Chord k} {req : A → E}

def padHistogram (h : Histogram (Fin n) t) (extra : ℕ) : Histogram (Fin (n+extra)) t :=
  ⟨Fin.addCases h.val (fun _ => 0), by
    rw [Fin.sum_univ_add]
    simpa using h.2⟩

def padCounts (C : Fin n → E → ℕ) (extra : ℕ) : Fin (n+extra) → E → ℕ :=
  Fin.addCases C (fun _ _ => 0)

omit [Fintype E] in
theorem pad_width (C : Fin n → E → ℕ) (h : Histogram (Fin n) t) (extra : ℕ) (e : E) :
    histWidth (padCounts C extra) (padHistogram h extra) e = histWidth C h e := by
  simp [histWidth,Fin.sum_univ_add,padCounts,padHistogram]

/-- The sum and zero-tail checks suffice to recover one genuine, unpadded histogram.
The fixed-length representation has no unused multiplicities or alternate spellings. -/
theorem decodeHistogram {n extra t : ℕ} (words : Fin (n+extra) → ℕ)
    (sum : ∑ i, words i = t) (padding : ∀ j : Fin extra, words (Fin.natAdd n j) = 0) :
    ∃! h : Histogram (Fin n) t, ∀ i, ((padHistogram h extra).val i).val = words i := by
  have bound (j : Fin n) : words (j.castAdd extra) < t+1 := by
    have hh := Finset.single_le_sum (fun i _ => Nat.zero_le (words i)) (Finset.mem_univ (j.castAdd extra))
    omega
  let h : Histogram (Fin n) t := ⟨fun j=>⟨words (j.castAdd extra),bound j⟩,by
    rw [Fin.sum_univ_add] at sum
    simpa [padding] using sum⟩
  refine ⟨h,?_,?_⟩
  · intro i
    induction i using Fin.addCases with
    | left j => simp [padHistogram,h]
    | right j => simp [padHistogram,padding]
  · intro other same
    apply Subtype.ext
    funext j
    apply Fin.ext
    simpa [padHistogram,h] using same (j.castAdd extra)

omit [Nonempty (Fin k)] in
theorem decoded_packet (P : Probe.Packet F edge req) (extra : ℕ) (b : Batch (P.terms+extra) d)
    (m : Memory w) (r : Word w) (select : b.selected m r)
    (alphabet : (b.termCount.read m (b.packet.eval m r)).val=P.terms)
    (qFit : P.terms+extra≤2^w) (copiesFit : b.copies<2^w) (sumFit : (P.terms+extra)*b.copies<2^w)
    (word : 0<w) (acceptedWord : (b.ifAdmitted (.lit 1) (.lit 0)).eval m r = 1) :
    ∃! h : Histogram (Fin P.terms) b.copies,
      ∀ i, ((padHistogram h extra).val i).val = ((b.field i).eval m r).val := by
  classical
  rw [Batch.eval_ifAdmitted _ _ _ _ _ qFit copiesFit sumFit] at acceptedWord
  simp only [ite_eq_left select] at acceptedWord
  by_cases ok : b.withinPacket m r ∧ ∑ i, ((b.field i).eval m r).val = b.copies
  · apply decodeHistogram _ ok.2
    intro j
    have test := ok.1 (Fin.natAdd P.terms j)
    simp [alphabet,Fin.val_natAdd] at test
    simpa only [Fin.val_zero] using congrArg Fin.val test
  · rw [ite_eq_right ok] at acceptedWord
    have one : 1 < 2^w := Nat.one_lt_two_pow word.ne'
    have no := congrArg Fin.val acceptedWord
    change (0:Word w).val = (1:Word w).val at no
    rw [show (1:Word w).val=1 from Fin.val_cast_of_lt one] at no
    exact (Nat.zero_ne_one no).elim

omit [Nonempty (Fin k)] in
/-- A packet from the finite failed-ball catalogue has its actual alphabet, width
table and coefficient identity. Padding its alphabet with unused zero lanes preserves
exactly the booked width at every option endpoint. -/
theorem packet_wire (P : Probe.Packet F edge req) (extra : ℕ) (b : Batch (P.terms+extra) d)
    (m : Memory w) (r : Word w) (e : E) (tab : Fin (P.terms+extra) → Expr)
    (h : Histogram (Fin P.terms) b.copies) (active : b.selected m r) (alphabet : b.withinPacket m r)
    (qFit : P.terms+extra ≤ 2^w) (copiesFit : b.copies < 2^w) (sumFit : (P.terms+extra)*b.copies < 2^w)
    (fields : ∀ i, ((b.field i).eval m r).val = ((padHistogram h extra).val i).val)
    (opts : ∀ i, (tab i).eval m r = (padCounts P.count extra i e : Word w))
    (maxBound : ∀ i, P.count i e ≤ b.maxWidth) (fit : b.maxWidth < 2^w) :
    (b.wire tab).eval m r = (histWidth P.count h e : Word w) := by
  rw [← pad_width P.count h extra e]
  apply b.wire_selected m r e tab (padCounts P.count extra) (padHistogram h extra)
    active alphabet qFit copiesFit sumFit fields opts _ fit
  intro i
  induction i using Fin.addCases with
  | left i => simpa [padCounts] using maxBound i
  | right i => simp [padCounts]


end Hierarchy.ProtocolRAM

end OAI
