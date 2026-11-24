import OAI.Computability.VPVNP.JointScalarLeafPrepare

/-! # Composing the two count calls and the signed field conversion -/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointScalar.Leaf

open RAMTape UniversalCountStack

/-- The same finite control is used for every row, modulus, and circuit. -/
def machine : FiniteRoutine Port :=
  ((((((load.followedBy prependRow).followedBy (pushSign false)).followedBy (counter false)).followedBy
    switchSign).followedBy (counter true)).followedBy reduce).followedBy cleanup

/-- Maximum of the static and live words needed at subroutine boundaries. -/
def bankSize (L : Layout) (wr payload : ℕ) :=
  wr + payload + L.rowBits + L.witnessBits + L.limbWidth + L.degree + L.degree*L.limbWidth +
    L.circuitAdvice.length + 2

/-- All work except the two witness enumerations, including their field conversion. -/
def localCost (L : Layout) (b : ℕ) :=
  (4*(5*b+2)+1) + (9*L.rowBits+3) + 3 + (4*(b+1)+1) +
    (2*(L.witnessBits+1) + L.degree + L.limbWidth) +
    SliceArithmeticSignedCount.callCap (L.witnessBits+1) (L.witnessBits+1) L.degree L.limbWidth

private theorem bank_le (L : Layout) (row payload q ch pos neg result : List Bool)
    (b : ℕ) (hrow : row.length ≤ b) (hpayload : payload.length ≤ b) (hq : q.length ≤ b)
    (hc : ch.length ≤ b) (hp : pos.length ≤ b) (hn : neg.length ≤ b) (hr : result.length ≤ b)
    (ha : L.circuitAdvice.length ≤ b) (hw : L.rowBits ≤ b) (hk : L.witnessBits+1 ≤ b)
    (hv : L.limbWidth ≤ b) (he : L.degree ≤ b) : ∀ j, (bank L row payload q ch pos neg result j).length ≤ b := by
  intro j
  cases j with
  | count i => cases i with
    | aux i => cases i <;> first | exact hq | exact ha | exact Nat.zero_le _
    | _ => first | exact hc | exact Nat.zero_le _
  | arithmetic i =>
    rcases i with i|i
    · cases i with
      | divide j => cases j <;> exact Nat.zero_le _
      | _ => exact Nat.zero_le _
    · cases i <;> first | exact hp | exact hn | exact hr | simpa [bank, SliceArithmeticSignedCount.clean,
        SliceArithmeticSignedCount.frame, SliceArithmeticSignedCount.external] using hv |
        simpa [bank, SliceArithmeticSignedCount.clean, SliceArithmeticSignedCount.frame,
          SliceArithmeticSignedCount.external] using he
  | row => exact hrow
  | packed => exact hpayload
  | rowWidth => simpa [bank] using hw
  | blankChoice => simpa [bank] using (show L.witnessBits ≤ b by omega)
  | blankTotal => simpa [bank] using hk
  | saved | staged => exact Nat.zero_le _

/-- Every immutable width template and circuit advice stack in the
initial coefficient bank fits its live-space budget. -/
theorem clean_length_le (L : Layout) (wr payload : ℕ) (i : Port) :
    (clean L [] [] [] i).length ≤ bankSize L wr payload := by
  apply bank_le
  all_goals simp [bankSize] <;> omega

private theorem short_bounded {r : FiniteRoutine Port} {steps b cap : ℕ} {s u : Stacks Port}
    (run : r.Runs steps s u) (room : ∀ i, (s i).length ≤ b) (hc : b+steps ≤ cap) :
    r.BoundedRun cap steps s u :=
  spaceRun_of_steps run fun i => (Nat.add_le_add_right (room i) steps).trans hc

/-- Frame-preserving composition with separate count time and space bounds. -/
theorem call_bounded {p e v : ℕ} [Fact p.Prime] [NeZero e] (modulus : SliceArithmetic.Vector p e)
    (hv : SliceArithmetic.Word.workingWidth p ≤ v) (L : Layout) (hp : L.prime = p)
    (he : L.degree = e) (hw : L.limbWidth = v) (wr j : ℕ) (hj : j < 2^wr) (payload : List Bool)
    (value : Bool → ℕ) (z : ℤ) (countSpace countTime : ℕ)
    (counts : ∀ sign, ∃ ticks ≤ countTime, SpaceRun countCircuit.standalone countSpace ticks
      (some countCircuit.entry) (UniversalCountStack.bank
        (AdviceCountAdapter.inputs (sign :: (digits L.rowBits j ++ payload)) L.circuitAdvice)
        (digits L.witnessBits 0) (digits (L.witnessBits+1) 0) [] []) none
      (UniversalCountStack.bank
        (AdviceCountAdapter.inputs (sign :: (digits L.rowBits j ++ payload)) L.circuitAdvice)
        (digits L.witnessBits 0) (digits (L.witnessBits+1) (value sign)) [] []))
    (signed : (TapeWord.value (digits (L.witnessBits+1) (value false)) : ℤ) -
      (TapeWord.value (digits (L.witnessBits+1) (value true)) : ℤ) = z) :
    let b := bankSize L wr payload.length
    let k := localCost L b
    ∃ steps ≤ 2*countTime+k, machine.BoundedRun (max countSpace b+k) steps
      (clean L (digits wr j) payload [])
      (clean L (digits wr j) payload (RankQuery.Stack.Engine.scalar v (z : RankQuery.Stack.Scalar modulus))) := by
  intro b k
  let cap := max countSpace b+k
  let row := digits wr j
  let q := digits L.rowBits j ++ payload
  let ch := digits L.witnessBits 0
  let zero := digits (L.witnessBits+1) 0
  let out (s : Bool) := digits (L.witnessBits+1) (value s)
  let bits := RankQuery.Stack.Engine.scalar v (z : RankQuery.Stack.Scalar modulus)
  have hrow : row.length ≤ b := by simp [row,b,bankSize]; omega
  have hpay : payload.length ≤ b := by dsimp [b,bankSize]; omega
  have hrowbits : L.rowBits ≤ b := by dsimp [b,bankSize]; omega
  have hwit : L.witnessBits+1 ≤ b := by dsimp [b,bankSize]; omega
  have hv' : L.limbWidth ≤ b := by dsimp [b,bankSize]; omega
  have he' : L.degree ≤ b := by dsimp [b,bankSize]; omega
  have hadv : L.circuitAdvice.length ≤ b := by dsimp [b,bankSize]; omega
  have hq : q.length+1 ≤ b := by simp [q,b,bankSize]; omega
  have hch : ch.length ≤ b := by simp [ch]; omega
  have hz : zero.length ≤ b := by simpa [zero] using hwit
  have hout (s) : (out s).length ≤ b := by simpa [out] using hwit
  have hbits : bits.length ≤ b := by simp [bits,b,bankSize,he,hw]; omega
  have hbank (q' ch' p' n' r' : List Bool) (hq' : q'.length ≤ b) (hc : ch'.length ≤ b)
      (hp' : p'.length ≤ b) (hn : n'.length ≤ b) (hr : r'.length ≤ b) :=
    bank_le L row payload q' ch' p' n' r' b hrow hpay hq' hc hp' hn hr hadv hrowbits hwit hv' he'
  have hcspace : countSpace ≤ cap := by dsimp [cap]; omega
  have hbc : b+k ≤ cap := by dsimp [cap]; omega
  have hbc' : b ≤ cap := by omega
  obtain ⟨ta,hta,ra⟩ := load_runs L row payload [] b hpay hwit
  obtain ⟨tb,htb,rb⟩ := prefix_runs L wr j hj payload payload ch zero zero []
  have rc := pushSign_runs L row payload q ch zero zero [] false
  have a := short_bounded ra (hbank [] [] [] [] [] (by simp) (by simp) (by simp) (by simp) (by simp))
    (cap := cap) (by dsimp [k,localCost] at hbc; omega)
  have b' := short_bounded rb (hbank payload ch zero zero [] hpay hch hz hz (by simp))
    (cap := cap) (by dsimp [k,localCost] at hbc; omega)
  have c' := short_bounded rc (hbank q ch zero zero [] (by omega) hch hz hz (by simp))
    (cap := cap) (by dsimp [k,localCost] at hbc; omega)
  have hqs (s : Bool) : (s::q).length ≤ b := by simpa using hq
  have hbankCap (q' ch' p' n' r' : List Bool) (hq' : q'.length ≤ b) (hc : ch'.length ≤ b)
      (hp' : p'.length ≤ b) (hn : n'.length ≤ b) (hr : r'.length ≤ b) (i : Port) :=
    (hbank q' ch' p' n' r' hq' hc hp' hn hr i).trans hbc'
  obtain ⟨td,htd,rd⟩ := counts false
  have d := counter_bounded false L row payload (false::q) ch zero zero (out false) []
    (rd.mono_cap hcspace) (hbankCap _ _ _ _ _ (hqs false) hch hz hz (by simp))
  have f := short_bounded (switchSign_runs L row payload q ch (out false) zero [])
    (hbank (false::q) ch (out false) zero [] (hqs false) hch (hout false) hz (by simp))
    (cap := cap) (by dsimp [k,localCost] at hbc; omega)
  obtain ⟨tg,htg,rg⟩ := counts true
  have g := counter_bounded true L row payload (true::q) ch (out false) zero (out true) []
    (rg.mono_cap hcspace) (hbankCap _ _ _ _ _ (hqs true) hch (hout false) hz (by simp))
  obtain ⟨th,hth,h⟩ := reduce_bounded modulus hv L hp he hw z row payload (true::q) ch (out false) (out true) []
    signed cap (by
      simp only [out,length_digits,List.length_nil,add_zero]
      dsimp [k,localCost] at hbc
      rw [he,hw] at hbc
      omega)
    (hbankCap _ _ _ _ _ (hqs true) hch (hout false) (hout true) (by simp))
  simp only [List.append_nil] at h
  obtain ⟨ti,hti,ri⟩ := cleanup_runs L row payload (true::q) ch (out false) (out true) bits b
    (hqs true) hch (hout false) (hout true)
  have i := short_bounded ri (hbank _ _ _ _ _ (hqs true) hch (hout false) (hout true) hbits)
    (cap := cap) (by dsimp [k,localCost] at hbc; omega)
  refine ⟨_,?_,((((((a.followedBy b').followedBy c').followedBy d).followedBy f).followedBy g).followedBy h).followedBy i⟩
  dsimp only [k,localCost]
  simp only [out,length_digits] at hth
  rw [he,hw]
  omega

end JointScalar.Leaf

end VPVNP
end Computability
end OAI
