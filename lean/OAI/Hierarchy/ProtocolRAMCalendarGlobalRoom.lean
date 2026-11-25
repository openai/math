import OAI.Hierarchy.ProtocolRAMCalendarGlobalTests
import OAI.Hierarchy.ProtocolRAMCalendarLinearRoom

namespace OAI
/-! # Bounding the two global score words uniformly over all retained stocks -/

namespace Hierarchy.ProtocolRAM.Calendar.GlobalTests
open Computability.VPVNP.BurstRAM PrivateRAM AttemptGate AdaptiveProbe ProbeStage.Native
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {z N k w : ℕ}

def upper (s : PhasePrice) (i : ℕ) := s.cap i+(s.a+s.bonus i)*(s.cap i)^2

def unitBound (l : Layout) (N k : ℕ) (s : PhasePrice) :=
  ∑i : Fin (kinds N k), ⌊(l.precision:ℝ)*upper s i.val⌋₊

@[simp] theorem unitBound_time_bits (l : Layout) (N k : ℕ) (s : PhasePrice) (t : ℝ) (width : ℕ) :
    unitBound l N k {s with time:=t,bits:=width}=unitBound l N k s := rfl

theorem value_le (s : PhasePrice) (p : Bool) (i n : ℕ) (a : 0<s.a) (b : 0≤ s.bonus i)
    (mk : 0≤ s.M) (time : 0<s.time) (positive : 0≤ s.cap i) : value s p i n≤upper s i := by
  let x := s.quote i n
  have within : 0≤x ∧ x≤ s.cap i := (offer_spec a b mk time (by positivity) positive).1
  have sq : x^2≤(s.cap i)^2 := pow_le_pow_left₀ within.1 within.2 2
  have up : rise s.M x≤x := max_le (sub_le_self _ mk) within.1
  have rs : rise s.M x≤ s.cap i := up.trans within.2
  have rsq : (rise s.M x)^2≤(s.cap i)^2 := pow_le_pow_left₀ (rise_nonneg s.M x) rs 2
  have sum := add_le_add (mul_le_mul_of_nonneg_left sq a.le) (mul_le_mul_of_nonneg_left rsq b)
  have big : 0≤(s.a+s.bonus i)*(s.cap i)^2 := by positivity
  cases p
  · change s.a*x^2+s.bonus i*(rise s.M x)^2≤ s.cap i+(s.a+s.bonus i)*(s.cap i)^2
    linarith [sum]
  · change (if decide (i=0) then x else 0)≤ s.cap i+(s.a+s.bonus i)*(s.cap i)^2
    split <;> linarith [within.2]

theorem valueWord_le (l : Layout) (s : PhasePrice) (p : Bool) (i : Fin (kinds N k)) (n : ℕ)
    (a : 0<s.a) (b : 0≤ s.bonus i.val) (mk : 0≤ s.M) (time : 0<s.time) (pos : 0≤ s.cap i.val) :
    valueWord l.precision (value s p) i.val n≤unitBound l N k s :=
  (Nat.floor_mono (mul_le_mul_of_nonneg_left (value_le s p i.val n a b mk time pos) (by positivity))).trans
    (Finset.single_le_sum (f := fun j : Fin (kinds N k) => ⌊(l.precision : ℝ) * upper s j.val⌋₊)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))

theorem global_sum {l : Layout} {s : PhasePrice} {p : Bool} {out bound : ℕ} {stocks : Bank} {m : Memory w}
    (R : ScoreWords (check l z N k p out bound stocks) m (value s p) l.precision)
    (actual : ∀ i,(R.kind i).val<kinds N k) (a : 0<s.a) (b : ∀ i<kinds N k,0≤ s.bonus i)
    (mk : 0≤ s.M) (time : 0<s.time) (pos : ∀ i<kinds N k,0≤ s.cap i) :
    ∑ i,(check l z N k p out bound stocks).score m i ≤ rows z N k*unitBound l N k s := by
  calc
    _ ≤ ∑ _i : Fin (rows z N k),unitBound l N k s := by
      apply Finset.sum_le_sum
      intro i _
      rw [R.read]
      let j : Fin (kinds N k) := ⟨(R.kind i).val,actual i⟩
      exact valueWord_le l s p j (R.bits i).val a (b _ j.isLt) mk time (pos _ j.isLt)
    _ = _ := by simp

theorem large_room (l : Layout) (z d N k : ℕ) (s : PhasePrice)
    (large : kinds N k*unitBound l N k s≤z) :
    rows z N k*unitBound l N k s<2^(wordBits z d copies) := by
  rw [rowCount,Nat.mul_comm (kinds N k),Nat.mul_assoc]
  exact linear_room z d _ large

end
end Hierarchy.ProtocolRAM.Calendar.GlobalTests

end OAI
