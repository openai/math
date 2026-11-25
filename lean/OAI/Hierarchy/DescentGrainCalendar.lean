import OAI.Hierarchy.DescentAtomSchedule

namespace OAI
/-! # Integral wire grains at the actual ordinary and reset ages -/

namespace Hierarchy.DescentCompiler.AtomSchedule
variable (S : AtomSchedule)

/-- Each completed block of rounds contains exactly one reset. -/
def ordinaryDone (i : ℕ) := i-i/(S.rounds+1)

/-- The terminal multiplier is shared by all ages. Only an ordinary stage removes a factor b. -/
def grainAt (b p i : ℕ) := p*b^(S.rounds*S.height-S.ordinaryDone i)
def firstWidth (b p : ℕ) := S.grainAt b p 0*b

theorem ordinaryDone_at {epoch slot : ℕ} (within : slot≤S.rounds) :
    S.ordinaryDone (epoch*(S.rounds+1)+slot)=epoch*S.rounds+slot := by
  unfold ordinaryDone
  rw [Nat.mul_comm epoch (S.rounds+1),Nat.mul_add_div (Nat.succ_pos _),Nat.div_eq_of_lt (Nat.lt_succ_of_le within),Nat.add_zero]
  rw [Nat.add_mul,one_mul,Nat.mul_comm S.rounds epoch]
  omega

theorem grain_initial (b p : ℕ) : S.grainAt b p 0=p*b^(S.rounds*S.height) := by
  simp [grainAt,ordinaryDone]

theorem grain_terminal (b p : ℕ) : S.grainAt b p S.length=p := by
  have atEnd : S.length=S.height*(S.rounds+1)+0 := by simp [length,Nat.mul_comm]
  rw [grainAt,atEnd,S.ordinaryDone_at (Nat.zero_le _)]
  simp [Nat.mul_comm]

theorem grain_positive {b p : ℕ} (hb : 0<b) (hp : 0<p) (age : ℕ) : 0<S.grainAt b p age :=
  Nat.mul_pos hp (Nat.pow_pos hb)

theorem grain_ordinary (b p : ℕ) {epoch slot : ℕ} (period : epoch<S.height) (inside : slot<S.rounds) :
    S.grainAt b p (epoch*(S.rounds+1)+slot)=S.grainAt b p (epoch*(S.rounds+1)+slot+1)*b := by
  rw [show epoch*(S.rounds+1)+slot+1=epoch*(S.rounds+1)+(slot+1) by omega]
  simp only [grainAt,S.ordinaryDone_at inside.le,S.ordinaryDone_at inside]
  have avail : epoch*S.rounds+slot+1≤S.rounds*S.height := by
    have endOfEpoch := Nat.mul_le_mul_right S.rounds period
    rw [Nat.succ_mul] at endOfEpoch
    rw [Nat.mul_comm S.rounds S.height]
    omega
  have next : S.rounds*S.height-(epoch*S.rounds+slot)=
      (S.rounds*S.height-(epoch*S.rounds+(slot+1)))+1 := by omega
  rw [next,pow_succ,Nat.mul_assoc]

theorem grain_reset (b p epoch : ℕ) :
    S.grainAt b p (epoch*(S.rounds+1)+S.rounds)=S.grainAt b p ((epoch+1)*(S.rounds+1)) := by
  have right : S.ordinaryDone ((epoch+1)*(S.rounds+1))=(epoch+1)*S.rounds := by
    simpa only [Nat.add_zero] using S.ordinaryDone_at (epoch:=epoch+1) (Nat.zero_le S.rounds)
  unfold grainAt
  rw [S.ordinaryDone_at (Nat.le_refl _),right,Nat.succ_mul]

private theorem all_powers (positive : 0<S.height) {b : ℕ} (branch : b≤2^S.capGain) :
    6*b^(S.rounds*S.height)≤S.epochPower^S.priceExponent := by
  have exp : 3+S.capGain*S.rounds≤S.priceExponent := by
    dsimp [priceExponent,atomExponent]
    rw [Nat.mul_add S.capGain]
    omega
  have big : 3+S.capGain*(S.rounds*S.height)≤S.height*S.priceExponent := by
    apply le_trans _ (Nat.mul_le_mul_left S.height exp)
    rw [Nat.mul_add]
    have grow : 3≤S.height*3 := by omega
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using
      Nat.add_le_add_right grow (S.capGain*(S.rounds*S.height))
  calc
    _ ≤ 2^3*(2^S.capGain)^(S.rounds*S.height) := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left branch _)
    _ = 2^(3+S.capGain*(S.rounds*S.height)) := by rw [←pow_mul,←pow_add]
    _ ≤ _ := by rw [epochPower,←pow_mul];exact Nat.pow_le_pow_right (by decide) big

/-- Pay all six prospective new history records at every positive wire width, including
the last grain p. Neither the price exponent nor this inequality depends on p. -/
theorem grain_history (positive : 0<S.height) {b : ℕ} (hb : 0<b) (branch : b≤2^S.capGain) (p age : ℕ) :
    6*S.firstWidth b p ≤ S.epochPower^S.priceExponent*(S.grainAt b p age*b) := by
  have fit : p≤S.grainAt b p age := Nat.le_mul_of_pos_right _ (Nat.pow_pos hb)
  calc
    _ = (6*b^(S.rounds*S.height))*(p*b) := by rw [firstWidth,grain_initial];ring
    _ ≤ _ := Nat.mul_le_mul (all_powers S positive branch) (Nat.mul_le_mul_right _ fit)

end Hierarchy.DescentCompiler.AtomSchedule

end OAI
