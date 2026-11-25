import OAI.Hierarchy.DescentStageCopyRoom
import OAI.Hierarchy.DescentPrivateMeterNumbers
import OAI.Hierarchy.DescentPrivateClockScale

namespace OAI
/-! # A fixed native word width holds the whole private counter at every compiler age -/

namespace Hierarchy.DescentSixParty.NativeBranch
open DescentCompiler GadgetNetwork
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)

/-- All seed sites and every bit of their stacked copies are counted. -/
def privatePopulation (p : ℕ) := S.initialSites*(S.copies*S.firstWidth G.b p)

theorem private_population_budget (p : ℕ) (radix : 2≤S.radix) :
    privateMax G S p≤privateRate G*(privatePopulation G S p)^3 := by
  let population:=privatePopulation G S p
  change _≤privateRate G*population^3
  have arr : privateMax G S p=privateRate G*(S.length*S.radix*population) := by
    unfold privateMax population privatePopulation
    ring
  rw [arr]
  apply Nat.mul_le_mul_left
  by_cases empty : population=0
  · simp [empty]
  have slots : 0<S.initialSites := by
    by_contra! h
    have zero:=Nat.eq_zero_of_le_zero h
    exact empty (by simp [population,privatePopulation,zero])
  have sw : 0<S.firstWidth G.b p := by
    by_contra! h
    have zero:=Nat.eq_zero_of_le_zero h
    exact empty (by simp [population,privatePopulation,zero])
  have groups : 0<S.baseGroups := by
    by_contra! h
    have zero:=Nat.eq_zero_of_le_zero h
    exact empty (by simp [population,privatePopulation,AtomSchedule.copies,zero])
  have copy : S.copies≤population :=
    (Nat.le_mul_of_pos_right _ sw).trans (Nat.le_mul_of_pos_left _ slots)
  have cloud : S.radix^(S.length+1)≤S.copies := Nat.le_mul_of_pos_left _ groups
  have count : S.length≤S.radix^(S.length+1) :=
    Nat.lt_two_pow_self.le.trans ((Nat.pow_le_pow_left radix S.length).trans
      (Nat.pow_le_pow_right (by omega) (Nat.le_succ _)))
  have digit : S.radix≤S.radix^(S.length+1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)
  calc
    _ ≤ population*population*population := Nat.mul_le_mul_right _ (Nat.mul_le_mul (count.trans (cloud.trans copy)) (digit.trans (cloud.trans copy)))
    _ = _ := by ring

theorem private_population_word (p : ℕ) (radix : 2≤S.radix) :
    privateMax G S p<2^((Nat.log 2 (privateRate G)+1)+3*(Nat.log 2 (privatePopulation G S p)+1)) :=
  (private_population_budget G S p radix).trans_lt (private_volume_fits _ _)

def clockRate (t f g reset tail : ℕ) :=
  let c:=hostRate t reset
  let e:=capRate G t g
  let k:=privateGroupRate t c e (cutRate t f g)
  privateRate G+3*(2+(tail+k)+(1+G.b*(t+1)))+1



/-- A separately budgeted tail and the square of the compiler age bound all copy bits. -/
theorem private_clock_budget (t J f g reset M tail τ p h : ℕ) (hh : 0<h) (age : (J+1)^2≤h)
    (reserve : tail≤τ*h) (sites : M≤2^(2*h)) (payload : p≤h) :
    privateMax G (stageNumbers G t J f g reset M tail) p<2^(clockRate G t f g reset τ*h) := by
  let c:=hostRate t reset
  let e:=capRate G t g
  let f₀:=cutRate t f g
  let S:=stageNumbers G t J f g reset M tail
  let K:=privateGroupRate t c e f₀
  let E:=2+(τ+K)+(1+G.b*(t+1))
  have hJ : J≤h := by nlinarith only [age,Nat.zero_le J]
  have kel : 0<groupBits t J c e f₀ := by unfold groupBits;omega
  have radix : 2≤S.radix := by
    change 2≤2^groupBits t J c e f₀
    exact (show (2:ℕ)=2^1 by decide).le.trans (Nat.pow_le_pow_right (by decide) kel)
  have copy : S.copies≤2^((τ+K)*h) :=stage_copies_word G t J f g reset M tail τ h hh age reserve
  have ampl : t*J+1≤(t+1)*h := by
    have hi:=Nat.mul_le_mul_left t hJ
    rw [Nat.succ_mul]
    omega
  have start : S.firstWidth G.b p≤2^((1+G.b*(t+1))*h) := by
    unfold AtomSchedule.firstWidth
    rw [S.grain_initial,Nat.mul_assoc,←pow_succ]
    change p*G.b^(t*J+1)≤_
    have hp : p≤2^h :=payload.trans Nat.lt_two_pow_self.le
    calc
      _ ≤ (2^h)*((2^G.b)^(t*J+1)) := Nat.mul_le_mul hp (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _)
      _ = 2^(h+G.b*(t*J+1)) := by rw [pow_add (2:ℕ) h (G.b*(t*J+1)),pow_mul (2:ℕ) G.b (t*J+1)]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
        have hi:=Nat.mul_le_mul_left G.b ampl
        rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc]
        omega)
  have pop : privatePopulation G S p≤2^(E*h) := calc
    _ ≤ 2^(2*h)*(2^((τ+K)*h)*2^((1+G.b*(t+1))*h)) := Nat.mul_le_mul sites (Nat.mul_le_mul copy start)
    _ = _ := by dsimp [E];rw [←pow_add,←pow_add];congr 1;ring
  have bounds := private_population_budget G S p radix
  have rate : privateRate G<2^(privateRate G*h) :=
    Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ hh))
  calc
    _ ≤ _ := bounds
    _ ≤ privateRate G*(2^(E*h))^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left pop 3)
    _ < 2^(privateRate G*h)*(2^(E*h))^3 := Nat.mul_lt_mul_of_pos_right rate (by positivity)
    _ ≤ _ := by
      rw [←pow_mul,←pow_add]
      apply Nat.pow_le_pow_right (by decide)
      change privateRate G*h+(E*h)*3≤(privateRate G+3*E+1)*h
      calc
        _ = (privateRate G+3*E)*h := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ _)

theorem private_clock_at (t J f g reset M tail p h : ℕ) (hh : 0<h) (age : (J+1)^2≤h)
    (sites : M≤2^(2*h)) (payload : p≤h) :
    privateMax G (stageNumbers G t J f g reset M tail) p<2^(clockRate G t f g reset tail*h) :=
  private_clock_budget G t J f g reset M tail tail p h hh age (Nat.le_mul_of_pos_right _ hh) sites payload

/-- The original logarithmic age choice needs no further hidden-bit room hypothesis. -/
theorem private_clock (t f g reset M tail p h B : ℕ) (hh : 0<h) (hB : 0<B)
    (sites : M≤2^(2*h)) (payload : p≤h) :
    privateMax G (stageNumbers G t (Nat.log 2 h/(2*B)) f g reset M tail) p<2^(clockRate G t f g reset tail*h) :=
  private_clock_at G _ _ _ _ _ _ _ _ _ hh (private_age_square h B hh hB) sites payload

/-- The physical tail grows with the compiler age while the CPU word factor stays fixed. -/
theorem private_clock_chosen (t f g reset M τ p h B : ℕ) (hh : 0<h) (hB : 0<B)
    (sites : M≤2^(2*h)) (payload : p≤h) :
    let J:=Nat.log 2 h/(2*B)
    let S:=stageNumbers G t J f g reset M (τ*(J+1))
    Nat.log 2 (privateMax G S p)+1≤clockRate G t f g reset τ*h := by
  dsimp only
  have age := private_age_square h B hh hB
  dsimp only at age
  have ageBound : Nat.log 2 h/(2*B)+1≤h :=by nlinarith only [age]
  have bound:=private_clock_budget G t _ f g reset M _ τ p h hh age
    (Nat.mul_le_mul_left τ ageBound) sites payload
  by_cases zero : privateMax G (stageNumbers G t (Nat.log 2 h/(2*B)) f g reset M (τ*(Nat.log 2 h/(2*B)+1))) p=0
  · rw [zero,Nat.log_zero_right]
    exact Nat.mul_pos (show 0<clockRate G t f g reset τ by exact Nat.succ_pos _) hh
  · exact (Nat.log_lt_of_lt_pow (by omega) bound)

end Hierarchy.DescentSixParty.NativeBranch

end OAI
