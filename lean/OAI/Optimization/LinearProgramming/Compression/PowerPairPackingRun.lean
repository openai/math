import OAI.Optimization.LinearProgramming.Compression.PowerPairPacking
import OAI.Optimization.LinearProgramming.Compression.PowerPairWords
import OAI.Optimization.LinearProgramming.Compression.PowerPairData

/-! A fixed RAM block prepares both input tapes of the native power comparator
from two compacted arrays of scalar bases and signed integer exponents. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem signedBitTape_length_le {w : ℕ} (es : List ℤ) (hw : ∀ x ∈ es, x.natAbs < 2^w) :
    (signedBitTape es).length ≤ es.length*(w+2) := by
  rw [signedBitTape_length]
  induction es with
  | nil => simp
  | cons x es ih =>
    have h := ih (fun y hy => hw y (by simp [hy]))
    have hx := Nat.size_le.mpr (hw x (by simp))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    omega

/-- A single cubic envelope for the concrete preparation count in the number
of pairs and the maximum bit width of their exponents. -/
theorem packPowerPairs_cost_poly (w n : ℕ) :
    (w*(16*w+32)+37)*n+12*(n*(w+2))+7*n+51 ≤ polyBound 68 3 (n+w) := by
  unfold polyBound
  ring_nf
  omega

/-- Finish both native tapes after the caller has obtained the literal exponent
tokens. This stage operates directly on bases in the ambient ordered field. -/
def finishPowerPairsBlock : Block := .seq packPowerAddressBlock packPowerBasesBlock

def packPowerPairsBlock (word : Block) : Block :=
  .seq (.op (.addrCopy 34 59)) (.seq (packPowerExponentsBlock word) finishPowerPairsBlock)

/-- The four input array headers of the frame copier, both entire signed-product
tapes, and the saved previous-callee extent in register 60. -/
structure PowerPairsReady (xs : List K) (es : List ℤ) (dataBase addrBase : ℕ)
    (initial final : Memory K) : Prop where
  scalarPointer : final.index 55 = dataBase
  scalarLength : final.index 56 = (powerPairScalarWords xs).length
  addressPointer : final.index 57 = addrBase
  addressLength : final.index 58 = (powerEncoderAddressInput (signedBitTape es)).length
  oldExtent : final.index 60 = initial.index 60
  scalar : ∀ i, ∀ hi : i < (powerPairScalarWords xs).length,
    final.data (dataBase+i) = (powerPairScalarWords xs)[i]
  address : ∀ i, ∀ hi : i < (powerEncoderAddressInput (signedBitTape es)).length,
    final.index (addrBase+i) = (powerEncoderAddressInput (signedBitTape es))[i]

/-- Prepare the two ordinary input arrays from already emitted literal tokens
and arbitrary native field bases. This also supports a caller that computed the
tokens on a separate rational register bank. -/
theorem finishPowerPairsBlock_spec {P : K → Prop} (xs : List K) (es : List ℤ) (m : Memory K)
    (src dst tokenStart : ℕ) (hm : m.AllData P) (h0 : P 0) (h1 : P 1)
    (h50 : m.index 50 = xs.length) (h51 : m.index 51 = src) (h55 : m.index 55 = dst)
    (h59 : m.index 59 = tokenStart) (h34 : m.index 34 = tokenStart+(signedBitTape es).length)
    (hs : 64 ≤ src) (hd : 64 ≤ dst) (room : 64+2*(signedBitTape es).length+8 ≤ tokenStart)
    (hsd : src+xs.length ≤ dst ∨ dst+4+xs.length ≤ src)
    (bases : ∀ i, ∀ hi : i < xs.length, m.data (src+i) = xs[i])
    (tokens : ∀ i, ∀ hi : i < (signedBitTape es).length,
      m.index (tokenStart+i) = ((signedBitTape es)[i]).code) :
    ∃ t, Block.Eval (Memory.AllData P) finishPowerPairsBlock m
        (12*(signedBitTape es).length+27+(7*xs.length+21)) t ∧
      PowerPairsReady xs es dst (tokenStart-(2*(signedBitTape es).length+8)) m t ∧
      (∀ i, i ≠ 0 → (i < dst ∨ dst+(powerPairScalarWords xs).length ≤ i) → t.data i = m.data i) ∧
      ∀ i, 43 ≤ i → i ≠ 56 → i ≠ 57 → i ≠ 58 →
        (i < tokenStart-(2*(signedBitTape es).length+8) ∨ tokenStart ≤ i) → t.index i = m.index i := by
  obtain ⟨b,eb,bd,bptr,blen,bw,bf⟩ := packPowerAddressBlock_spec (signedBitTape es) m tokenStart
    hm h59 h34 room tokens
  have bi (i : ℕ) (hi : 43 ≤ i) (h57 : i ≠ 57) (h58 : i ≠ 58)
      (hf : i < tokenStart-(2*(signedBitTape es).length+8) ∨ tokenStart ≤ i) :
      b.index i = m.index i := bf i (by simp [powerAddressScratch];omega) hf
  obtain ⟨t,et,tlen,tw,td,ti⟩ := packPowerBasesBlock_spec xs b src dst eb.safe_end h0 h1
    ((bi 50 (by decide) (by decide) (by decide) (Or.inl (by omega))).trans h50)
    ((bi 51 (by decide) (by decide) (by decide) (Or.inl (by omega))).trans h51)
    ((bi 55 (by decide) (by decide) (by decide) (Or.inl (by omega))).trans h55)
    hs hd hsd (fun i hi => (congrFun bd _).trans (bases i hi))
  have frame (i : ℕ) (hi : 43 ≤ i) (h56 : i ≠ 56) (h57 : i ≠ 57) (h58 : i ≠ 58)
      (hf : i < tokenStart-(2*(signedBitTape es).length+8) ∨ tokenStart ≤ i) : t.index i = m.index i :=
    (ti i (by omega) (by omega) (by omega) h56).trans (bi i hi h57 h58 hf)
  refine ⟨t,eb.seq et,?_,fun i hi hf => (td i hi hf).trans (congrFun bd i),frame⟩
  refine ⟨(frame 55 (by decide) (by decide) (by decide) (by decide) (Or.inl (by omega))).trans h55,
    tlen,(ti 57 (by decide) (by decide) (by decide) (by decide)).trans bptr,
    (ti 58 (by decide) (by decide) (by decide) (by decide)).trans blen,
    frame 60 (by decide) (by decide) (by decide) (by decide) (Or.inl (by omega)),tw,?_⟩
  intro i hi
  rw [ti _ (by omega) (by omega) (by omega) (by omega)]
  exact bw i hi

/-- Scalar input arrays and previously allocated remote cells survive the
counted, in-place preparation of a canonical pair of input tapes. -/
theorem packPowerPairsBlock_spec {word : Block} {P : K → Prop} {w : ℕ}
    (emitter : PowerTokenEmitterSpec word w P) (xs : List K) (es : List ℤ) (m : Memory K)
    (scratch src dst expSrc tokenStart : ℕ) (hm : m.AllData P) (h0 : P 0) (h1 : P 1)
    (hlen : xs.length = es.length) (h2 : m.index 2 = scratch) (h50 : m.index 50 = es.length)
    (h51 : m.index 51 = src) (h52 : m.index 52 = expSrc) (h55 : m.index 55 = dst)
    (h59 : m.index 59 = tokenStart) (hb : 41 < scratch) (hs : 64 ≤ src)
    (hd : 64 ≤ dst) (he : 64 ≤ expSrc) (hspace : 64+2*(es.length*(w+2))+8 ≤ tokenStart)
    (hse : expSrc+es.length ≤ scratch ∨ scratch+w ≤ expSrc)
    (hss : src+xs.length ≤ scratch ∨ scratch+w ≤ src)
    (hsd : src+xs.length ≤ dst ∨ dst+4+xs.length ≤ src)
    (bases : ∀ i, ∀ hi : i < xs.length, m.data (src+i) = xs[i])
    (exponents : ∀ i, ∀ hi : i < es.length, m.data (expSrc+i) = (es[i] : K))
    (width : ∀ x ∈ es, x.natAbs < 2^w) :
    ∃ t k, k ≤ (w*(16*w+32)+37)*es.length+12*(es.length*(w+2))+7*es.length+51 ∧
      Block.Eval (Memory.AllData P) (packPowerPairsBlock word) m k t ∧
      PowerPairsReady xs es dst (tokenStart-(2*(signedBitTape es).length+8)) m t ∧
      (∀ i, 6 ≤ i → i ≠ 40 → i ≠ 41 → (i < scratch ∨ scratch+w ≤ i) →
        (i < dst ∨ dst+(powerPairScalarWords xs).length ≤ i) → t.data i = m.data i) ∧
      ∀ i, 43 ≤ i → i ≠ 52 → i ≠ 54 → i ≠ 56 → i ≠ 57 → i ≠ 58 →
        (i < tokenStart-(2*(signedBitTape es).length+8) ∨ tokenStart+(signedBitTape es).length ≤ i) →
        t.index i = m.index i := by
  let v := m.putIndex 34 tokenStart
  have entry : Block.Eval (Memory.AllData P) (.op (.addrCopy 34 59)) m 1 v := by
    simpa only [v,h59] using Block.Eval.op_addrCopy (safe := Memory.AllData P) m 34 59 hm hm
  have hT := signedBitTape_length_le es width
  have room : 64+2*(signedBitTape es).length+8 ≤ tokenStart := by omega
  obtain ⟨a,k,hk,ea,post⟩ := packPowerExponentsBlock_spec emitter es v scratch expSrc tokenStart
    hm hb he (by omega) hse (by simpa [v] using h2) (by simp [v]) (by simpa [v] using h50)
    (by simpa [v] using h52) exponents width
  have ai (i : ℕ) (hi : 43 ≤ i) (h52' : i ≠ 52) (h54' : i ≠ 54)
      (hf : i < tokenStart ∨ tokenStart+(signedBitTape es).length ≤ i) : a.index i = m.index i := by
    have e := post.indexFrame i (by omega) (by omega) (by omega) (by omega) (by omega) h52' h54' hf
    simpa [v,show i ≠ 34 by omega] using e
  obtain ⟨t,ef,ready,df,addr⟩ := finishPowerPairsBlock_spec xs es a src dst tokenStart
    ea.safe_end h0 h1 (post.limit.trans hlen.symm)
    ((ai 51 (by decide) (by decide) (by decide) (Or.inl (by omega))).trans h51)
    ((ai 55 (by decide) (by decide) (by decide) (Or.inl (by omega))).trans h55)
    ((ai 59 (by decide) (by decide) (by decide) (Or.inl (by omega))).trans h59)
    post.tokenCursor hs hd room hsd (fun i hi => by
      rw [post.dataFrame (src+i) (by omega) (by omega) (by omega) (by omega)]
      exact bases i hi) post.tokens
  have saved : t.index 60 = m.index 60 :=
    ready.oldExtent.trans (ai 60 (by decide) (by decide) (by decide) (Or.inl (by omega)))
  have prepared : PowerPairsReady xs es dst (tokenStart-(2*(signedBitTape es).length+8)) m t :=
    ⟨ready.scalarPointer,ready.scalarLength,ready.addressPointer,ready.addressLength,saved,
     ready.scalar,ready.address⟩
  refine ⟨t,_,?_,entry.seq (ea.seq ef),prepared,?_,?_⟩
  · rw [hlen]; omega
  · intro i hi h40 h41 hscratch hdst
    exact (df i (by omega) hdst).trans (post.dataFrame i hi h40 h41 hscratch)
  · intro i hi h52' h54' h56' h57' h58' hf
    exact (addr i hi h56' h57' h58' (by omega)).trans (ai i hi h52' h54' (by omega))

end Compression
end LinearProgramming
end Optimization
end OAI
