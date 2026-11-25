import OAI.Computability.NearSquareRoot.InterchangeROMPrelude
import OAI.Computability.NearSquareRoot.InterchangeROMRecursionThick
import OAI.Computability.NearSquareRoot.InterchangeROMTableArithmetic

/-! # A uniform clock for the native interchange prelude -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMFront

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeROMFrame
  NearSquareRoot.InterchangeROMRecursion

namespace Input

noncomputable def middle (i : Input) : Tree := if h : i.stage then
  .fork (send (InterchangeROMExpose.centerHeader (i.inside h))) (InterchangeROMExpose.centerPayload (i.inside h))
  else (Request.job i.b).reply i.req

theorem result_eq (i : Input) : i.result = .fork (.atom (decide i.stage)) i.middle := by
  by_cases h : i.stage <;> simp [result,middle,h]

end Input

structure Core where
  cmd : Cmd
  registers : ℕ
  degree : ℕ
  clock : ℕ
  pos : 0 < registers
  cutoff : CommonRegisters.Within registers cmd
  run (i : Input) (env : Env) (deck : Deck) : Fits env cmd (pile 0 i.query deck)
    (pile 0 i.result deck) (clock*(Input.scale.work degree i+1))
  size_bound (i : Input) : i.result.count ≤ i.query.count + clock*(Input.scale.work degree i+1)

/-- The fixed hardware is chosen on the mixed domain of all radices, lane
counts, and request streams. -/
theorem exists_core : Nonempty Core := by
  obtain ⟨d,code⟩ := Input.prelude
  obtain ⟨E,sz⟩ := code.sizeBound
  obtain ⟨c,C,run⟩ := code
  obtain ⟨R,pos,bounded⟩ := ((Filter.eventually_gt_atTop (0:ℕ)).and (RegisterSelect.within_eventually c)).exists
  exact ⟨⟨c,R,d,max C E,pos,bounded,
    fun i env deck => (run i env deck).mono (Nat.mul_le_mul_right _ (le_max_left ..)),
    fun i => (sz i).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (le_max_right ..)) _)⟩⟩

abbrev digit {p : ℕ} (x : ZMod p) := InterchangeROMTable.numeral x.val

theorem payload_bound {b p : ℕ} [NeZero p] (q : Request b) (good : Request.Packed (b:=b) (@digit p) q)
    (rows : 0 < q.rows.count) : q.payload.count + 1 ≤ (2*p+7)*q.recordVolume := by
  have symbol (v : ZMod p) : (digit v).count ≤ 2*p+1 := by
    change size (tally v.val) ≤ _
    rw [size_tally,tally_length]
    have := v.val_lt
    omega
  have cell (x) : (q.contents x).count ≤ q.recordWidth*(2*p+2)+1 := by
    obtain ⟨v,e⟩ := good.2.2 x
    rw [e]
    simpa only [Series.count_natural,Nat.add_assoc] using
      stripe_size (Series.natural q.recordWidth) (digit ∘ v) (2*p+1) (fun y => symbol _)
  have size := stripe_size q.rows q.contents _ cell
  change (stripe q.rows q.contents).count + 1 ≤ _
  unfold Request.recordVolume
  nlinarith

/-- Integer majorant for local operations on one epoch. The additive setup
cost and the factor on actual payload bytes are both explicit. -/
def rate (F : Core) (p b n : ℕ) :=
  let spec := 2*b+2*n+3
  let bytes := 2*p+7
  let growth := (b^n+1)^F.degree*bytes + (spec+2)^F.degree
  16*(spec+bytes+F.clock*(growth+1)+10)

theorem rate_bound (F : Core) (p : ℕ) [NeZero p] (i : Input) (good : Request.Packed (@digit p) i.req) :
    5*(literal i.b i.n).count + F.clock*(Input.scale.work F.degree i+1) +
      ((Request.job i.b).issue i.req).count + i.middle.count + 20 ≤
        rate F p i.b i.n * localMass i.req (F.degree+1) := by
  let q := i.req
  let M := localMass q (F.degree+1)
  let A := (i.b^i.n+1)^F.degree
  let S := (literal i.b i.n).count
  let B := (S+2)^F.degree
  let T := 2*p+7
  have hs : S = 2*i.b+2*i.n+3 := by
    change size (tally i.b,tally i.n) = _
    simp only [size_prod,size_tally,tally_length]
    omega
  have rows : 0 < q.rows.count := (Nat.pow_pos (by decide : 0 < 2)).trans_le
    (Request.pow_digits_le i.req i.radix i.valid)
  have H0 : 1 ≤ (q.header.count+1)^F.degree := Nat.one_le_pow _ _ (by omega)
  have H1 : q.header.count+1 ≤ (q.header.count+1)^(F.degree+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < q.header.count+1 by omega)
      (show 1 ≤ F.degree+1 by omega)
  have big : q.header.count+1 ≤ M := H1.trans ((Nat.le_add_left ..).trans (Nat.le_mul_of_pos_left _ rows))
  have pos : 1 ≤ M := by omega
  have vol : q.recordVolume ≤ M := Nat.mul_le_mul_left _ (Nat.add_le_add_left (by omega) _)
  have payload : q.payload.count+1 ≤ T*M := (payload_bound q good rows).trans (Nat.mul_le_mul_left T vol)
  have descriptor : size i.template + 1 ≤ (S+2)*(q.header.count+1) := by
    change S + q.header.count + 1 + 1 ≤ _
    nlinarith
  have power : (size i.template+1)^F.degree ≤ B*M := by
    apply (Nat.pow_le_pow_left descriptor _).trans
    rw [Nat.mul_pow]
    apply Nat.mul_le_mul_left
    exact ((Nat.pow_le_pow_right (by omega : 0 < q.header.count+1) (by omega : F.degree ≤ F.degree+1)).trans
      ((Nat.le_add_left ..).trans (Nat.le_mul_of_pos_left _ rows)))
  have weight : Input.scale.work F.degree i ≤ (A*T+B)*M := by
    change A*(q.payload.count+1)+(size i.template+1)^F.degree ≤ _
    rw [Nat.add_mul,Nat.mul_assoc]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ payload) power
  have time : F.clock*(Input.scale.work F.degree i+1) ≤ (F.clock*(A*T+B+1))*M := by
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    rw [Nat.add_mul,Nat.one_mul]
    omega
  have issue : ((Request.job i.b).issue q).count ≤ (T+1)*M := by
    change q.header.count+q.payload.count+1 ≤ _
    rw [Nat.add_mul,Nat.one_mul]
    omega
  have out := F.size_bound i
  rw [Input.result_eq] at out
  change 1+i.middle.count+1 ≤ S + ((Request.job i.b).issue q).count + 1 +
      F.clock*(Input.scale.work F.degree i+1) at out
  change _ ≤ 16*(2*i.b+2*i.n+3+T+F.clock*(A*T+(2*i.b+2*i.n+3+2)^F.degree+1)+10)*M
  rw [← hs]
  change 5*S+_+_+i.middle.count+20 ≤ 16*(S+T+F.clock*(A*T+B+1)+10)*M
  have spec := Nat.mul_le_mul_left S pos
  nlinarith

end InterchangeROMFront

end NearSquareRoot
end Computability
end OAI
