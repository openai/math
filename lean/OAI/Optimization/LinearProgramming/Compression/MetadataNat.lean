import OAI.Optimization.LinearProgramming.Compression.MetadataPacket
import OAI.Optimization.LinearProgramming.Compression.MetadataDivide

/-! Emit a small RAM address in the oracle's self-delimiting, little-endian binary
format. The writer reads only natural address registers and the two fixed bit cells. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
namespace Metadata

open RAM RAM.Block OracleSpec

private def lowBit (n : Nat) : Bool := decide (0<n%2)

private theorem bits_positive (n : Nat) (hn : 0<n) : n.bits = lowBit n :: (n/2).bits := by
  by_cases h : n%2=0
  · have eq : n=2*(n/2) := by omega
    calc n.bits = (2*(n/2)).bits := congrArg Nat.bits eq
      _ = false :: (n/2).bits := Nat.bit0_bits _ (by omega)
      _ = _ := by simp [lowBit,h]
  · have remd : n%2=1 := by omega
    have eq : n=2*(n/2)+1 := by omega
    calc n.bits = (2*(n/2)+1).bits := congrArg Nat.bits eq
      _ = true :: (n/2).bits := Nat.bit1_bits _
      _ = _ := by simp [lowBit,remd]

private def pairs : Word → Word
  | [] => []
  | b::bs => true::b::pairs bs

private theorem pairs_terminated (bs : Word) : pairs bs ++ [false] = OracleSpec.frame bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change true :: b :: (pairs bs ++ [false]) = true :: b :: OracleSpec.frame bs
    rw [ih]

private def writeLow : Block := .branch (.addrLT 67 69) (emit true) (emit false)

private def digit : Block := .seq halve (.seq (emit true) (.seq writeLow (.op (.addrCopy 69 71))))

private def digits : Block := .loop (.addrLT 67 69) digit

/-- Copy the input header before using the quotient/remainder scratch registers,
then terminate the emitted word with a single false bit. -/
def writeNatFrom (header : Nat) : Block := .seq (.op (.addrCopy 69 header)) (.seq digits (emit false))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

private theorem copyInto69 (s : Memory K) (src : Nat) (hs : s.AllData P) :
    let t := s.putIndex 69 (s.index src)
    Eval (Memory.AllData P) (.op (.addrCopy 69 src)) s 1 t ∧ Effect s t [] := by
  dsimp only
  exact ⟨Eval.op_addrCopy s 69 src hs hs,Effect.empty rfl (by simp) (by simp)
    (fun i _ _ h69 _ => by simp [h69])⟩

private theorem writeLow_correct (s : Memory K) (n : Nat) (hs : s.AllData P) (ready : Ready s)
    (value : s.index 69=n%2) :
    ∃ t k, Eval (Memory.AllData P) writeLow s k t ∧ k≤5 ∧ Effect s t [lowBit n] ∧
      ∀ i, i≠65 → i≠49 → t.index i=s.index i := by
  have test : (Cond.addrLT 67 69).test s = lowBit n := by simp [Cond.test,ready.indexZero,value,lowBit]
  cases hb : lowBit n with
  | false =>
    obtain ⟨t,run,e,keep⟩ := emit_correct s false hs ready
    exact ⟨t,4,.branchFalse (test.trans hb) run,by decide,e,keep⟩
  | true =>
    obtain ⟨t,run,e,keep⟩ := emit_correct s true hs ready
    exact ⟨t,5,.branchTrue (test.trans hb) run,by decide,e,keep⟩

private theorem digit_correct (s : Memory K) (n : Nat) (hs : s.AllData P) (ready : Ready s)
    (value : s.index 69=n) :
    ∃ t k, Eval (Memory.AllData P) digit s k t ∧ k≤5*(n/2)+11 ∧
      Effect s t [true,lowBit n] ∧ t.index 69=n/2 := by
  obtain ⟨a,divide,data,remd,quo,frame⟩ := halve_correct s n hs value ready.indexOne
  have e0 : Effect s a [] := Effect.empty data (frame 65 (by decide) (by decide))
    (frame 49 (by decide) (by decide)) (fun i _ _ h69 h71 => frame i h69 h71)
  obtain ⟨b,marker,e1,keep1⟩ := emit_correct a true divide.safe_end (ready.after e0)
  obtain ⟨c,k,parity,hk,e2,keep2⟩ := writeLow_correct b n marker.safe_end ((ready.after e0).after e1)
    ((keep1 69 (by decide) (by decide)).trans remd)
  have q : c.index 71=n/2 := (keep2 71 (by decide) (by decide)).trans
    ((keep1 71 (by decide) (by decide)).trans quo)
  obtain ⟨move,e3⟩ := copyInto69 c 71 parity.safe_end
  refine ⟨_,_,divide.seq (marker.seq (parity.seq move)),by omega,?_,?_⟩
  · simpa using (((e0.append e1).append e2).append e3)
  · simpa using q

private theorem digits_correct (n : Nat) (s : Memory K) (hs : s.AllData P) (ready : Ready s)
    (value : s.index 69=n) :
    ∃ t k, Eval (Memory.AllData P) digits s k t ∧ k≤(n+1)*(5*n+25) ∧ Effect s t (pairs n.bits) := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hn : n=0
    · have valZero : s.index 69=0 := value.trans hn
      have test : (Cond.addrLT 67 69).test s=false := by simp [Cond.test,ready.indexZero,valZero]
      refine ⟨s,1,.loopFalse test hs,?_,?_⟩
      · rw [hn]; decide
      · rw [hn,Nat.zero_bits]; exact Effect.refl s
    · have pos : 0<n := by omega
      have lt : n/2<n := by omega
      have test : (Cond.addrLT 67 69).test s=true := by simp [Cond.test,ready.indexZero,value,pos]
      obtain ⟨u,j,head,hj,e0,next⟩ := digit_correct s n hs ready value
      obtain ⟨t,k,tail,hk,e1⟩ := ih (n/2) lt u head.safe_end (ready.after e0) next
      have recCap : k≤n*(5*n+25) := hk.trans (Nat.mul_le_mul (by omega) (by omega))
      refine ⟨t,_,.loopTrue test head tail,?_,?_⟩
      · rw [Nat.add_mul, Nat.one_mul]
        omega
      · rw [bits_positive n pos]
        exact e0.append e1

/-- Write the actual canonical binary code for the original header. All scalar
registers stay in the supplied invariant, and the two public cursors advance by
precisely the number of bits emitted. -/
theorem writeNatFrom_correct (s : Memory K) (header n : Nat) (hs : s.AllData P)
    (ready : Ready s) (value : s.index header=n) :
    ∃ t k, Eval (Memory.AllData P) (writeNatFrom header) s k t ∧ k≤(n+1)*(5*n+25)+5 ∧
      Effect s t (encodeNat n) := by
  let a := s.putIndex 69 (s.index header)
  obtain ⟨copy,e0⟩ := copyInto69 s header hs
  have atA : a.index 69=n := by simp [a,value]
  obtain ⟨u,k,loop,hk,e1⟩ := digits_correct n a copy.safe_end (ready.after e0) atA
  obtain ⟨t,last,e2,_⟩ := emit_correct u false loop.safe_end ((ready.after e0).after e1)
  refine ⟨t,_,copy.seq (loop.seq last),by omega,?_⟩
  simpa only [List.nil_append,pairs_terminated,encodeNat] using (e0.append e1).append e2

end Metadata
end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
