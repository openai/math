import OAI.Hierarchy.DescentRetainedPrefix

namespace OAI
/-! # Fixed history price for a chronological branch, including its final group -/

namespace Hierarchy.DescentCompiler

/-- The schedule starts with one extra radix factor in the population. Its last installed
stage can therefore still publish a full group to the common host. -/
structure AtomSchedule where
  rounds : ℕ
  height : ℕ
  hostGain : ℕ
  capGain : ℕ
  baseGroups : ℕ
  radix : ℕ
  initialSites : ℕ

namespace AtomSchedule
variable (S : AtomSchedule)

def length := (S.rounds+1)*S.height
def copies := S.baseGroups*S.radix^(S.length+1)
def groupCount (i : ℕ) := S.baseGroups*S.radix^(S.length-i)
def hostSize (i : ℕ) := S.initialSites*(2^S.hostGain*S.radix)^i
def epochPower := 2^S.height
def priceExponent := atomExponent S.rounds S.hostGain 11 (S.capGain*(S.rounds+1))
def batch := (S.initialSites*S.copies)*(2^S.hostGain)^S.length*2^(11+S.capGain*S.length)

/-- Counts the records accumulated so far. The increment is charged only on its birth. -/
def Within (i atoms : ℕ) : Prop := atoms≤(i+1)*S.batch

/-- Split off the next complete group from the actual chronological count. -/
def groupDigits {i k : ℕ} (age : i<S.length) (radix : S.radix=2^k) :
    Fin (S.groupCount i) ≃ Fin (S.groupCount (i+1)) × Fin (2^k) := by
  apply Equiv.trans _ finProdFinEquiv.symm
  apply finCongr
  change S.baseGroups*S.radix^(S.length-i)=S.baseGroups*S.radix^(S.length-(i+1))*2^k
  rw [←radix,Nat.mul_assoc,←pow_succ]
  congr 2
  omega

/-- The first census carries one extra finite radix digit, including at a zero-step horizon. -/
def initialDigits {k : ℕ} (radix : S.radix=2^k) :
    Fin S.copies ≃ Fin (S.groupCount 0) × Fin (2^k) := by
  apply Equiv.trans _ finProdFinEquiv.symm
  apply finCongr
  simp only [copies,groupCount,Nat.sub_zero,pow_succ,←radix,Nat.mul_assoc]

theorem host_step {i old new : ℕ} (fit : old≤S.hostSize i)
    (growth : new≤old*(2^S.hostGain*S.radix)) : new≤S.hostSize (i+1) := by
  have grew := Nat.mul_le_mul_right (2^S.hostGain*S.radix) fit
  exact growth.trans (by simpa [hostSize,pow_succ,Nat.mul_assoc] using grew)

/-- Read the normalized new cap directly from the old and new cable grains
and the actual integer cap published by the step. A reset may keep the grain. -/
theorem cap_step {i wire oldGrain newGrain ratio gain oldCap newCap : ℕ}
    (positive : 0<wire*newGrain) (grain : oldGrain=newGrain*ratio)
    (scale : wire*newGrain*newCap=2^gain*(wire*oldGrain*oldCap))
    (growth : 2^gain*ratio≤2^S.capGain) (old : oldCap≤2^(8+S.capGain*i)) :
    newCap≤2^(8+S.capGain*(i+1)) := by
  have recover : newCap=(2^gain*ratio)*oldCap := by
    apply Nat.eq_of_mul_eq_mul_left positive
    rw [scale,grain]
    ring
  rw [recover]
  apply (Nat.mul_le_mul growth old).trans_eq
  rw [←pow_add]
  congr 1
  ring

/-- Host rows times the actual population at that age cancel the radix paid at every past step. -/
theorem slot_reserve {i : ℕ} (age : i≤S.length) :
    S.hostSize i*(S.groupCount i*S.radix) ≤ (S.initialSites*S.copies)*(2^S.hostGain)^S.length := by
  have eqn : S.radix^i*S.radix^(S.length-i)=S.radix^S.length := by
    rw [←pow_add,Nat.add_sub_of_le age]
  calc
    _ = (S.initialSites*(S.baseGroups*((S.radix^i*S.radix^(S.length-i))*S.radix)))*(2^S.hostGain)^i := by
      dsimp only [hostSize,groupCount]
      rw [mul_pow]
      ring
    _ = (S.initialSites*S.copies)*(2^S.hostGain)^i := by rw [eqn,copies,pow_succ]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.two_pow_pos _) age)

/-- Multiplying the per-bin capacity by six covers all parties from every selected pair. -/
theorem ordinary_reserve {i hosts liveBlocks cap pairs : ℕ} (age : i≤S.length)
    (positions : hosts≤S.hostSize i) (population : liveBlocks≤S.groupCount i*S.radix)
    (capacity : cap≤2^(8+S.capGain*i)) (pairsBound : pairs≤(hosts*liveBlocks)*cap) :
    6*pairs≤S.batch := by
  have slots := (Nat.mul_le_mul positions population).trans (S.slot_reserve age)
  have capTop : cap≤2^(8+S.capGain*S.length) :=
    capacity.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (Nat.mul_le_mul_left _ age) 8))
  have scales : 6*cap≤2^(11+S.capGain*S.length) := by
    calc
      _ ≤ 2^3*2^(8+S.capGain*S.length) := Nat.mul_le_mul (by decide) capTop
      _ = _ := by rw [←pow_add]; congr 1; omega
  calc
    _ ≤ 6*((hosts*liveBlocks)*cap) := Nat.mul_le_mul_left 6 pairsBound
    _ = (hosts*liveBlocks)*(6*cap) := by ring
    _ ≤ _ := Nat.mul_le_mul slots scales

theorem reset_reserve {i hosts liveBlocks bank : ℕ} (age : i≤S.length)
    (positions : hosts≤S.hostSize i) (population : liveBlocks≤S.groupCount i*S.radix)
    (injected : bank≤hosts*liveBlocks) : bank≤S.batch := by
  have slots := injected.trans ((Nat.mul_le_mul positions population).trans (S.slot_reserve age))
  exact slots.trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))

theorem initial {atoms sourceSites : ℕ} (sites : sourceSites≤S.initialSites)
    (counted : atoms=S.copies*sourceSites) : S.Within 0 atoms := by
  subst atoms
  have bound : S.copies*sourceSites≤S.initialSites*S.copies := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right S.copies sites
  have p₁ : 0<(2^S.hostGain)^S.length := pow_pos (Nat.two_pow_pos _) _
  have p₂ : 0<2^(11+S.capGain*S.length) := Nat.two_pow_pos _
  simpa [Within,batch] using
    (bound.trans ((Nat.le_mul_of_pos_right _ p₁).trans (Nat.le_mul_of_pos_right _ p₂)))

theorem advance {i old fresh : ℕ} (before : S.Within i old) (inc : fresh≤S.batch) :
    S.Within (i+1) (old+fresh) := by
  simpa [Within,Nat.succ_mul] using Nat.add_le_add before inc

/-- Convert the entire chronological prefix to the fixed real history budget. -/
theorem paid {i atoms hist : ℕ} (positive : 0<S.height) (hh : 0<hist) (age : i≤S.length)
    (enough : S.Within i atoms) :
    (1/((hist:ℝ)*(S.epochPower:ℝ)^S.priceExponent))*hist*(atoms:ℝ) ≤
      ((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower := by
  have heightGain : 11≤11*S.height := by omega
  have exponent : S.length+S.hostGain*S.length+(11+S.capGain*S.length)+S.height ≤ S.height*S.priceExponent := by
    dsimp only [length,priceExponent,atomExponent]
    nlinarith only [heightGain]
  have powers : 2^S.length*(2^S.hostGain)^S.length*2^(11+S.capGain*S.length)*S.epochPower≤
      S.epochPower^S.priceExponent := by
    dsimp only [epochPower]
    rw [←pow_mul,←pow_add,←pow_add,←pow_add,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) exponent
  have total : atoms*S.epochPower≤(S.initialSites*S.copies)*S.epochPower^S.priceExponent := by
    have stages : i+1≤2^S.length := (Nat.succ_le_succ age).trans Nat.lt_two_pow_self
    have upper := Nat.mul_le_mul_right S.epochPower (enough.trans (Nat.mul_le_mul_right S.batch stages))
    exact upper.trans (by
      simpa only [batch,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using
        Nat.mul_le_mul_left (S.initialSites*S.copies) powers)
  have tpos : 0<S.epochPower := Nat.two_pow_pos _
  have scale : (1/((hist:ℝ)*(S.epochPower:ℝ)^S.priceExponent))*hist=1/(S.epochPower:ℝ)^S.priceExponent := by
    have h : (hist:ℝ)≠0 := by exact_mod_cast hh.ne'
    have t : (S.epochPower:ℝ)≠0 := by exact_mod_cast tpos.ne'
    field_simp
  rw [scale]
  exact retained_real tpos total

end AtomSchedule
end Hierarchy.DescentCompiler

end OAI
