import OAI.Optimization.LinearProgramming.NativePrice.BitRAM
import OAI.Optimization.LinearProgramming.NativePrice.Bounds
import OAI.Optimization.LinearProgramming.NativePrice.Designation
import OAI.Optimization.LinearProgramming.NativePrice.VectorRAM
import OAI.Optimization.LinearProgramming.NativePrice.PacketBits

/-! One uniform ordered-field program for decoding the designated PCG price packet
on the scalar bit tape produced at an actual oracle exchange. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NativePrice

open RAM OracleSpec

def packetBlock : Block :=
  .seq boundsBlock <| .seq natBlock <| .seq designationBlock <| .seq vectorBlock checkEnd

def packetTime (N L : ℕ) := (N+1)*(24*L+50)+32*L+6*N+64

/-- BitRAM supplies both the length and the bit window. The caller supplies the
number of prices and a disjoint numerical output array. -/
structure Header {K : Type*} {N : ℕ} (i : Fin N) (p : Fin N → ℚ) (s : Memory K)
    (c d : ℕ) : Prop where
  dimension : s.index 0=N
  output : s.index 9=d
  length : s.index 37=(priceQuery i p).length
  source : s.index 43=c
  sourceScratch : 9≤c
  outputScratch : 9≤d
  disjoint : d+N≤c ∨ c+(priceQuery i p).length≤d

/-- Decoded prices and both designated addresses. Address 13 records that the
entire declared packet was consumed. The BitRAM heap and exchange header survive. -/
structure Output {K : Type*} [Field K] {N : ℕ} (i : Fin N) (p : Fin N → ℚ)
    (s t : Memory K) (c d : ℕ) : Prop where
  prices : ∀ j : Fin N, t.data (d+j.val)=((p j):K)
  designation : t.index 14=i.val
  coordinate : t.index 2=d+i.val
  consumed : t.index 3=c+(priceQuery i p).length
  checked : t.index 13=1
  data : ∀ j, (j<3 ∨ 8<j) → (j<d ∨ d+N≤j) → t.data j=s.data j
  index : ∀ j, (j=0 ∨ j=1 ∨ j=9 ∨ 15≤j) → t.index j=s.index j

theorem packetBlock_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) {N : ℕ} (i : Fin N) (p : Fin N → ℚ) (s : Memory K) (c d : ℕ)
    (h : Header i p s c d) (hw : WordAt s c (priceQuery i p)) (hm : s.AllData P)
    (safe : Values P i p) :
    ∃ t k, k≤packetTime N (priceQuery i p).length ∧
      Block.Eval (Memory.AllData P) packetBlock s k t ∧ Output i p s t c d := by
  let pre := encodeNat i.val
  let fields := (List.ofFn p).flatMap encodeRat
  have word : priceQuery i p = pre++fields := rfl
  have total : (priceQuery i p).length=pre.length+fields.length := by rw [word,List.length_append]
  obtain ⟨b,eb,bd,bcur,bend,bi⟩ := boundsBlock_spec P s hm
  have hc : b.index 3=c := bcur.trans h.source
  have same : WordAt b c (pre++fields) := hw.of_data (fun j _ _ => congrFun bd j)
  obtain ⟨hin,hfields⟩ := wordAt_append.mp same
  obtain ⟨a,ka,hka,ea,aval,acur,ad,ai⟩ :=
    natBlock_spec P i.val b c hc h.sourceScratch hin eb.safe_end safe.designation
  obtain ⟨u,eu,raw,target,ud,ui⟩ :=
    designationBlock_spec P a i.val ea.safe_end aval safe.counter
  have und : u.index 0=N := (ui 0 (by decide) (by decide)).trans
    ((ai 0 (by decide)).trans ((bi 0 (by decide) (by decide) (by decide)).trans h.dimension))
  have udst : u.index 9=d := (ui 9 (by decide) (by decide)).trans
    ((ai 9 (by decide)).trans ((bi 9 (by decide) (by decide) (by decide)).trans h.output))
  have ucur : u.index 3=c+pre.length := (ui 3 (by decide) (by decide)).trans acur
  have unread : WordAt u (c+pre.length) fields := hfields.of_data (by
    intro j hj _
    have hlo := h.sourceScratch
    exact (ud j (by omega) (by omega)).trans (ad j (by omega)))
  have sep : d+N≤c+pre.length ∨ c+pre.length+fields.length≤d := by
    have hs := h.disjoint
    omega
  obtain ⟨v,kv,hkv,ev,vcur,prices,vd,vi⟩ := vectorBlock_spec P p u (c+pre.length) d
    und ucur udst (by have := h.sourceScratch; omega) h.outputScratch unread sep
    eu.safe_end safe.fields safe.signed safe.price
  have closed : v.index 3=c+(priceQuery i p).length := by
    change v.index 3=c+pre.length+fields.length at vcur
    omega
  have last : v.index 12=c+(priceQuery i p).length := by
    have eq := (vi 12 (by decide) (by decide) (by decide)).trans
      ((ui 12 (by decide) (by decide)).trans ((ai 12 (by decide)).trans bend))
    simpa [h.source,h.length] using eq
  have ec := checkEnd_spec P v ev.safe_end (closed.trans last.symm)
  let t := v.putIndex 13 1
  refine ⟨t,_,?_,eb.seq (ea.seq (eu.seq (ev.seq ec))),?_⟩
  · change kv≤(N+1)*(24*fields.length+50) at hkv
    change ka≤16*pre.length+16 at hka
    have pbound : (N+1)*(24*fields.length+50) ≤ (N+1)*(24*(priceQuery i p).length+50) :=
      Nat.mul_le_mul_left _ (by omega)
    have hlo := i.isLt
    unfold packetTime
    rw [h.length]
    omega
  · refine ⟨prices,?_,?_,?_,by simp [t],?_,?_⟩
    · simpa [t] using (vi 14 (by decide) (by decide) (by decide)).trans raw
    · have absidx := (vi 2 (by decide) (by decide) (by decide)).trans target
      have hb : a.index 9=d := (ai 9 (by decide)).trans
        ((bi 9 (by decide) (by decide) (by decide)).trans h.output)
      simpa [t,hb] using absidx
    · simpa [t] using closed
    · intro j hj gap
      exact (vd j hj gap).trans ((ud j (by omega) (by omega)).trans
        ((ad j (by omega)).trans (congrFun bd j)))
    · intro j hj
      have ef := (vi j (by omega) (by omega) (by omega)).trans
        ((ui j (by omega) (by omega)).trans ((ai j (by omega)).trans
          (bi j (by omega) (by omega) (by omega))))
      simpa [t,show j≠13 by omega] using ef

/-- On rational registers the canonical tape itself controls every newly decoded
scalar, including the two Horner accumulators and the signed numerator. -/
theorem packetBlock_rational {N : ℕ} (i : Fin N) (p : Fin N → ℚ) (s : Memory ℚ) (c d B : ℕ)
    (h : Header i p s c d) (hw : WordAt s c (priceQuery i p))
    (hm : s.AllData (fun x => ratBits x≤B)) (hB : (priceQuery i p).length+3≤B) :
    ∃ t k, k≤packetTime N (priceQuery i p).length ∧
      Block.Eval (Memory.AllData (fun x => ratBits x≤B)) packetBlock s k t ∧ Output i p s t c d :=
  packetBlock_spec _ i p s c d h hw hm (values_packet i p B hB)

/-- Accept the packet invariant produced directly by the BitRAM emitter. -/
theorem packetBlock_exchange {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) {N : ℕ} (i : Fin N) (p : Fin N → ℚ) (s : Memory K) (c d : ℕ)
    (h : Header i p s c d) (hw : BitRAM.ScalarPacket s c (priceQuery i p)) (hm : s.AllData P)
    (safe : Values P i p) :
    ∃ t k, k≤packetTime N (priceQuery i p).length ∧
      Block.Eval (Memory.AllData P) packetBlock s k t ∧ Output i p s t c d :=
  packetBlock_spec P i p s c d h ((scalarPacket_iff_wordAt ..).mp hw) hm safe

/-- The standalone compiled entry, including its final halt. -/
def program : Program := packetBlock.compile 0 ++ [.halt 0]

theorem packetBlock_trace {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) {N : ℕ} (i : Fin N) (p : Fin N → ℚ) (s : Memory K) (c d : ℕ)
    (h : Header i p s c d) (hw : BitRAM.ScalarPacket s c (priceQuery i p)) (hm : s.AllData P)
    (safe : Values P i p) :
    ∃ k ≤ packetTime N (priceQuery i p).length+1, ∃ z : Fin (k+1) → State K,
      RAM.Trace program (s.atPC 0) k z ∧ (z (Fin.last k)).output=some 0 ∧
      Output i p s (z (Fin.last k)).memory c d ∧ ∀ j, (z j).memory.AllData P := by
  obtain ⟨t,k,hk,e,output⟩ := packetBlock_exchange P i p s c d h hw hm safe
  obtain ⟨z,ht,ho,mem,hs⟩ := e.halted_trace (tag:=0)
  exact ⟨k+1,by omega,z,ht,ho,by simpa only [mem] using output,hs⟩

theorem packetTime_polynomial (N L : ℕ) : packetTime N L ≤ 200*(N+L+1)^2 := by
  unfold packetTime
  ring_nf
  omega

end NativePrice
end LinearProgramming
end Optimization
end OAI
