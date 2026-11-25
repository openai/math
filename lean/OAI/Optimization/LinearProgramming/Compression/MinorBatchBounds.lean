import OAI.Optimization.LinearProgramming.Compression.MinorBatchLoop
import OAI.Optimization.LinearProgramming.Compression.DetRamBits

/-! Repeated exact minor requests through one fixed scalar/address RAM program. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorLoad

open RAM

/-- This code is independent of both the matrix dimensions and the number and identities of the requests. -/
def batchProgram (call : Block) : Program := (batchBlock call).compile 0 ++ [.halt 0]

/-- Every case runs in the same program at the same instruction address. The descriptor tape
and original input remain available after all answers have been placed in consecutive slots. -/
theorem batchProgram_trace {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (call : Block) (hcall : BatchCallSpec K call)
    {q : ℕ} (v : BatchLayout K q) (m : Memory K) (initial : BatchInput v m)
    (N : ℕ) (hN : ∀a, (v.query a).m≤N ∧ (v.query a).n≤N ∧ (v.query a).k≤N) (P : K → Prop)
    (initialP : ∀ p, P (m.data p)) (hz : P 0) (ho : P 1) (hneg : ∀ x, P x → P (-x))
    (hreg : ∀a, ∀j<(v.query a).k, ∀r : BirdRegister (v.query a).k,
      P (r.read ((v.query a).matrix.submatrix (v.query a).row (v.query a).col)
        (birdLayer ((v.query a).matrix.submatrix (v.query a).row (v.query a).col) j))) :
    ∃ k ≤ q*(2200*(N+1)^7+17)+3, ∃ tr : Fin (k+1) → State K,
      Trace (batchProgram call) (m.atPC 0) k tr ∧ (tr (Fin.last k)).output = some 0 ∧
      (∀ a : Fin q, (tr (Fin.last k)).data (v.answerBase+a.val)=answerOf (v.query a)) ∧
      (∀ a, 7≤a → a<v.answerBase → (tr (Fin.last k)).data a=m.data a) ∧
      (∀ a, 20≤a → (tr (Fin.last k)).index a=m.index a) ∧ ∀ i p, P ((tr i).data p) := by
  obtain ⟨t,c,hc,hbody,answers,scalars,indices⟩ :=
    batchBlock_eval call hcall v m initial N hN P initialP hz ho hneg hreg
  obtain ⟨tr,hrun,halt,mem,hs⟩ := hbody.halted_trace (tag := 0)
  refine ⟨c+1, by omega, tr, hrun, halt, ?_, ?_, ?_, hs⟩
  · intro a
    exact (congrArg (fun z : Memory K => z.data (v.answerBase+a.val)) mem).trans (answers a)
  · intro a ha hlo
    exact (congrArg (fun z : Memory K => z.data a) mem).trans (scalars a ha hlo)
  · intro a ha
    exact (congrArg (fun z : Memory K => z.index a) mem).trans (indices a ha)

/-- All values used for a request depend on the sizes of that request's original entries.
The lengths of unrelated registers and previous answers do not enter this estimate. -/
theorem queryRegisterBits {q : ℕ} (v : BatchLayout ℚ q) (N B : ℕ)
    (hN : ∀a, (v.query a).k≤N) (hinput : ∀a i j,
      ratBits ((v.query a).matrix ((v.query a).row i) ((v.query a).col j)) ≤ B)
    (a : Fin q) (j : ℕ) (hj : j < (v.query a).k) (r : BirdRegister (v.query a).k) :
    ratBits (r.read ((v.query a).matrix.submatrix (v.query a).row (v.query a).col)
      (birdLayer ((v.query a).matrix.submatrix (v.query a).row (v.query a).col) j)) ≤ detRegisterBits N B := by
  let V := v.query a
  let A := V.matrix.submatrix V.row V.col
  apply (birdRegister_bits A (hinput a) j r).trans
  have hk : V.k≤N := hN a
  have hjN : j≤N := hj.le.trans hk
  change 3 + (V.k+B+2*B*V.k^2+3)*(j+2) ≤ 3 + (N+B+2*B*N^2+3)*(N+2)
  gcongr

/-- A fall-through call using a global bit allowance `M` and a possibly smaller input-block
allowance `B`. The calling program can retain other scalar data throughout all the requests. -/
theorem batchBlock_bits_at (call : Block) (hcall : BatchCallSpec ℚ call) {q : ℕ}
    (v : BatchLayout ℚ q) (m : Memory ℚ) (initial : BatchInput v m) (N B M : ℕ)
    (hN : ∀a, (v.query a).m≤N ∧ (v.query a).n≤N ∧ (v.query a).k≤N)
    (hstart : ∀p, ratBits (m.data p) ≤ M) (hinput : ∀a i j,
      ratBits ((v.query a).matrix ((v.query a).row i) ((v.query a).col j)) ≤ B)
    (hcap : detRegisterBits N B ≤ M) :
    ∃ t cost, cost ≤ q*(2200*(N+1)^7+17)+2 ∧
      Block.Eval (fun z => ∀p, ratBits (z.data p) ≤ M) (batchBlock call) m cost t ∧
      (∀ a : Fin q, t.data (v.answerBase+a.val)=answerOf (v.query a)) ∧
      (∀ a, 7≤a → a<v.answerBase → t.data a=m.data a) ∧ ∀ a, 20≤a → t.index a=m.index a := by
  have hsmall : 3 ≤ M := (Nat.le_add_right 3 _).trans hcap
  exact batchBlock_eval call hcall v m initial N hN (fun x => ratBits x ≤ M) hstart
    (show 3 ≤ M from hsmall) (show 3 ≤ M from hsmall) (fun x hx => by simpa [ratBits] using hx)
    (fun a j hj r => (queryRegisterBits v N B (fun a => (hN a).2.2) hinput a j hj r).trans hcap)

/-- In the rational case, performing additional determinant calls never compounds the bit bound.
The polynomial depends on the largest matrix dimension and the initial scalar encoding lengths. -/
theorem batchProgram_bits (call : Block) (hcall : BatchCallSpec ℚ call) {q : ℕ} (v : BatchLayout ℚ q) (m : Memory ℚ) (initial : BatchInput v m)
    (N B : ℕ) (hN : ∀a, (v.query a).m≤N ∧ (v.query a).n≤N ∧ (v.query a).k≤N)
    (hb : ∀ p, ratBits (m.data p) ≤ B) :
    ∃ k ≤ q*(2200*(N+1)^7+17)+3, ∃ tr : Fin (k+1) → State ℚ,
      Trace (batchProgram call) (m.atPC 0) k tr ∧ (tr (Fin.last k)).output = some 0 ∧
      (∀ a : Fin q, (tr (Fin.last k)).data (v.answerBase+a.val)=answerOf (v.query a)) ∧
      (∀ a, 7≤a → a<v.answerBase → (tr (Fin.last k)).data a=m.data a) ∧
      (∀ a, 20≤a → (tr (Fin.last k)).index a=m.index a) ∧ ∀ i, scalarBound (detRegisterBits N B) (tr i) := by
  let M := detRegisterBits N B
  have hc : B ≤ M := by
    let d := N+B+2*B*N^2+3
    have h : d * 1 ≤ d * (N+2) := Nat.mul_le_mul_left d (by omega)
    have h' : B ≤ d := by dsimp [d]; omega
    rw [Nat.mul_one] at h
    change B ≤ 3+d*(N+2); omega
  have hmin : 3≤M := Nat.le_add_right 3 _
  apply batchProgram_trace call hcall v m initial N hN (fun x => ratBits x ≤ M)
    (fun p => (hb p).trans hc) (show 3≤M from hmin) (show 3≤M from hmin)
    (fun x hx => by simpa [ratBits] using hx)
  apply queryRegisterBits v N B (fun a => (hN a).2.2)
  intro a i j
  rw [← initial.source a ((v.query a).row i) ((v.query a).col j)]
  exact hb _

end MinorLoad
end Compression
end LinearProgramming
end Optimization
end OAI
