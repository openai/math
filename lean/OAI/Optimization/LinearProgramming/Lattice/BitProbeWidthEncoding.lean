import OAI.Optimization.LinearProgramming.Lattice.BitProbeWidth
import OAI.Optimization.LinearProgramming.Lattice.BitProbeCodes

/-! Physical tape lengths of all continuations and actions in the adaptive probe. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
namespace Probe

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure

private def scale (p k B : ℕ) := p+k+B+2
private def atomSize (p k B : ℕ) := 50*(scale p k B+1)^3

def probeWordSize (p k B : ℕ) := 200*(atomSize p k B+1)

noncomputable def probeWordPolynomial : Polynomial ℕ := 200*(50*(Polynomial.X+3)^3+1)

theorem probeWordPolynomial_eval (p k B : ℕ) :
    probeWordPolynomial.eval (p+k+B) = probeWordSize p k B := by
  change (200*(50*(Polynomial.X+3)^3+1) : Polynomial ℕ).eval (p+k+B) =
    200*(50*((p+k+B)+3)^3+1)
  simp

private theorem list_size {A : Type} {N W : ℕ} (ea : A → List Bool) (xs : List A) (hL : xs.length ≤ N)
    (h : ∀ a ∈ xs,(ea a).length ≤ W) : (listCode ea xs).length ≤ N*(2*W+2)+1 := by
  have he := listCode_length_map_bound ea id xs W h
  simpa only [List.map_id] using he.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hL) 1)

private theorem int_length (z : ℤ) : (intCode z).length = z.natAbs.size+3 := by
  simp [intCode,intData,prodCode,pairBits_length,boolCode,Nat.size_eq_bits_len]
  omega

private theorem rat_length (q : ℚ) : (ratCode q).length = 2*q.num.natAbs.size+q.den.size+7 := by
  simp only [ratCode,prodCode,pairBits_length,int_length,Nat.size_eq_bits_len]
  omega

private theorem scale_le_atom (p k B : ℕ) : scale p k B ≤ atomSize p k B := by
  unfold atomSize
  generalize scale p k B = w
  ring_nf
  omega

private theorem row_size {p k B : ℕ} {r : Row} (h : RowBound p (queryMagnitude k (2^B)) r) :
    (intRowCode r).length ≤ scale p k B*(2*(scale p k B+3)+2)+1 := by
  let w := scale p k B
  apply list_size intCode r (h.length.trans (show p ≤ w by dsimp [w,scale]; omega))
  intro a ha
  have hm : queryMagnitude k (2^B) = 2^(k+B+1) := by
    simp [queryMagnitude,pow_succ,pow_add]
    ring
  have hw := Nat.size_le_size ((h.entry a ha).trans_eq hm)
  rw [Nat.size_pow] at hw
  rw [int_length]
  dsimp [scale]
  omega

private theorem row_atom {p k B : ℕ} {r : Row} (h : RowBound p (queryMagnitude k (2^B)) r) :
    (intRowCode r).length ≤ atomSize p k B := by
  apply (row_size h).trans
  unfold atomSize
  generalize scale p k B = w
  ring_nf
  omega

private theorem matrix_atom {p k B : ℕ} {a : IntMatrix} (h : TableBound p (2^B) a) :
    (intMatrixCode a).length ≤ atomSize p k B := by
  let w := scale p k B
  have ht : (intMatrixCode a).length ≤ w*(2*(w*(2*(w+3)+2)+1)+2)+1 := by
    apply list_size intRowCode a (h.length.trans (show p ≤ w by dsimp [w,scale]; omega))
    intro r hr
    apply row_size
    have z := h.row r hr
    refine ⟨z.length,fun v hv => (z.entry v hv).trans ?_⟩
    exact Nat.le_mul_of_pos_left (2^B) (by positivity)
  apply ht.trans
  change w*(2*(w*(2*(w+3)+2)+1)+2)+1 ≤ 50*(w+1)^3
  ring_nf
  omega

private theorem plain_row_atom {p k B : ℕ} {r : Row} (h : RowBound p (2^B) r) :
    (intRowCode r).length ≤ atomSize p k B := by
  apply row_atom
  refine ⟨h.length,fun v hv => (h.entry v hv).trans ?_⟩
  exact Nat.le_mul_of_pos_left (2^B) (by positivity)

private theorem values_atom {p k B : ℕ} {xs : List ℚ} (hl : xs.length ≤ p) (h : ValueBound k xs) :
    (ratListCode xs).length ≤ atomSize p k B := by
  let w := scale p k B
  have hh : (ratListCode xs).length ≤ w*(2*(3*w+7)+2)+1 := by
    apply list_size ratCode xs (hl.trans (show p ≤ w by dsimp [w,scale]; omega))
    intro q hq
    obtain ⟨hn,hd⟩ := h q hq
    rw [rat_length]
    dsimp [w,scale]
    omega
  apply hh.trans
  change w*(2*(3*w+7)+2)+1 ≤ 50*(w+1)^3
  ring_nf
  omega

private theorem params_size {p k B : ℕ} {z : Params} (h : ParamBound p k (2^B) z) :
    (paramsCode z).length ≤ 8*atomSize p k B+4 := by
  have ht := matrix_atom (k := k) h.rows
  have hw := scale_le_atom p k B
  have hp := h.dimension
  have hk := h.precision
  dsimp [scale] at hw
  simp only [paramsCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
  omega

theorem maxCode_length {p k B : ℕ} {s : MaxState} (h : MaxBound p k (2^B) s) :
    (maxCode s).length ≤ 40*atomSize p k B+20 := by
  have hz := params_size h.params
  have hr := matrix_atom (k := k) h.remaining
  have ha := plain_row_atom (k := k) h.candidate
  have hb := plain_row_atom (k := k) h.best
  simp only [maxCode,maxBaseCode,rowPairCode,prodCode,pairBits_length]
  omega

theorem pivotCode_length {p k B : ℕ} {s : Pivot} (h : PivotBound p k (2^B) s) :
    (pivotCode s).length ≤ 18*atomSize p k B+10 := by
  have hz := params_size h.params
  have hr := plain_row_atom (k := k) h.row
  simp only [pivotCode,prodCode,pairBits_length]
  omega

theorem ratioCode_length {p k B : ℕ} {s : Ratio} (h : RatioBound p k (2^B) s) :
    (ratioCode s).length ≤ 100*atomSize p k B+60 := by
  have hp := pivotCode_length h.pivot
  have hr := plain_row_atom (k := k) h.row
  have ht := matrix_atom (k := k) h.remaining
  have hc := h.count
  have hv := values_atom (B := B) (p := p) (by omega : s.2.2.2.length ≤ p) h.values
  obtain ⟨t,hd,hn,hleft⟩ := h.counter
  have hsize := (Nat.size_le_size hn.le).trans_eq (congrArg Nat.size hd)
  rw [Nat.size_pow] at hsize
  have hdsize := (congrArg Nat.size hd).trans Nat.size_pow
  have hprec := h.pivot.params.precision
  have hscale := scale_le_atom p k B
  dsimp [scale] at hscale
  simp only [ratioCode,ratioLeftCode,ratioRightCode,counterCode,remainingCode,prodCode,pairBits_length,
    int_length,unaryCode,List.length_replicate,Nat.size_eq_bits_len]
  omega

theorem carryCode_length {p k B : ℕ} {c : Carry} (h : CarryBound p k (2^B) c) :
    (carryCode c).length ≤ 102*atomSize p k B+65 := by
  rcases c with (s|s)|(s|s)
  · have hh := maxCode_length h
    simp only [carryCode,carryLeftCode,sumCode,List.length_cons]
    omega
  · have hh := maxCode_length h
    simp only [carryCode,carryLeftCode,sumCode,List.length_cons]
    omega
  · have hh := pivotCode_length h
    simp only [carryCode,carryRightCode,sumCode,List.length_cons]
    omega
  · have hh := ratioCode_length h
    simp only [carryCode,carryRightCode,sumCode,List.length_cons]
    omega

/-- One cubic polynomial bounds every physical probe action on all sign histories. -/
theorem actionCode_length {p k B : ℕ} {a : Action} (h : ActionBound p k (2^B) a) :
    (actionCode a).length ≤ probeWordSize p k B := by
  rcases a with r | ⟨q,c⟩
  · have hv := values_atom (B := B) h.1 h.2
    simp only [actionCode,resultCode,sumCode,prodCode,pairBits_length,boolCode,List.length_cons,List.length_nil]
    unfold probeWordSize
    omega
  · have hq := row_atom h.1
    have hc := carryCode_length h.2
    simp only [actionCode,sumCode,prodCode,pairBits_length,List.length_cons]
    unfold probeWordSize
    omega

/-- The three physical continuation layouts obey the identical polynomial clock. -/
theorem maxCode_uniform {p k B : ℕ} {s : MaxState} (h : MaxBound p k (2^B) s) :
    (maxCode s).length ≤ probeWordPolynomial.eval (p+k+B) := by
  rw [probeWordPolynomial_eval]
  have hh := maxCode_length h
  unfold probeWordSize
  omega

theorem pivotCode_uniform {p k B : ℕ} {s : Pivot} (h : PivotBound p k (2^B) s) :
    (pivotCode s).length ≤ probeWordPolynomial.eval (p+k+B) := by
  rw [probeWordPolynomial_eval]
  have hh := pivotCode_length h
  unfold probeWordSize
  omega

theorem ratioCode_uniform {p k B : ℕ} {s : Ratio} (h : RatioBound p k (2^B) s) :
    (ratioCode s).length ≤ probeWordPolynomial.eval (p+k+B) := by
  rw [probeWordPolynomial_eval]
  have hh := ratioCode_length h
  unfold probeWordSize
  omega

theorem carryCode_le_wordSize {p k B : ℕ} {c : Carry} (hc : CarryBound p k (2^B) c) :
    (carryCode c).length ≤ probeWordSize p k B := by
  have hh := carryCode_length hc
  unfold probeWordSize
  omega

/-- The serialized action and its tagged continuation remain bounded after every
actual prefix of oracle answers, independently of the signs supplied. -/
theorem reachable_word_size {p k B : ℕ} {z : Params} (hz : ParamBound p k (2^B) z)
    {a : Action} (ha : Reaches (start z) a) : (actionCode a).length ≤ probeWordPolynomial.eval (p+k+B) := by
  rw [probeWordPolynomial_eval]
  exact actionCode_length (bounded_of_reaches hz ha)

theorem reachable_query_size {p k B : ℕ} {z : Params} (hz : ParamBound p k (2^B) z)
    {q : Row} {c : Carry} (ha : Reaches (start z) (ask q c)) :
    (intRowCode q).length ≤ probeWordPolynomial.eval (p+k+B) := by
  rw [probeWordPolynomial_eval]
  have hh := row_atom (bounded_of_reaches hz ha).1
  unfold probeWordSize
  omega

theorem reachable_carry_size {p k B : ℕ} {z : Params} (hz : ParamBound p k (2^B) z)
    {q : Row} {c : Carry} (ha : Reaches (start z) (ask q c)) :
    (carryCode c).length ≤ probeWordPolynomial.eval (p+k+B) := by
  rw [probeWordPolynomial_eval]
  exact carryCode_le_wordSize (bounded_of_reaches hz ha).2

end Probe
end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
