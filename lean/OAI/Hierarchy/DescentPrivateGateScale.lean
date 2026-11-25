import OAI.Hierarchy.DescentTerminalChartScale
import OAI.Hierarchy.DescentPackedPayloadBudget
import OAI.Hierarchy.ProtocolRAMPortScale

namespace OAI
/-! # Paying for the fixed spent-variable table with the actual final stack width -/

namespace Hierarchy.DescentCompiler.TerminalScale
open Filter

/-- One packed cell contains one alias for every argument position at its site. -/
def aliasBits (T R n : ℕ) : ℕ :=
  let K:=(R+1)*T^n
  (Nat.log 2 K+1)*K

theorem alias_power {T R n : ℕ} (two : 2≤T) (stride : R+1≤T) :
    aliasBits T R n≤T^(2*(n+1)+1) := by
  let K:=(R+1)*T^n
  have pos : 0<K := by dsimp [K];positivity
  have cap : K≤T^(n+1) := by
    rw [pow_succ,Nat.mul_comm (T^n)]
    exact Nat.mul_le_mul_right _ stride
  have bits : Nat.log 2 K+1≤2*K := by have h:=Nat.log_le_self 2 K; omega
  calc
    aliasBits T R n ≤ (2*K)*K := Nat.mul_le_mul_right _ bits
    _ ≤ (T*T^(n+1))*T^(n+1) := Nat.mul_le_mul (Nat.mul_le_mul two cap) cap
    _ = T^(2*(n+1)+1) := by rw [←pow_succ',←pow_add];congr 1;ring

/-- The complete native clock includes the score-ROM installation and the
final multiplication of a grain count by the stack width. -/
def terminalGateBill (h W factor sites bits p : ℕ) :=
  (4+10*2^(h/2))*W+
    factor*(40*(h+h+4*sites*bits)+(56+4*ProtocolRAMPortScale.bitWidth p)*h)

private theorem scale_width {h p : ℕ} (width : p≤h) :
    ProtocolRAMPortScale.bitWidth p≤2*2^(h/2) := by
  have top : h/2+1≤2^(h/2) := Nat.lt_two_pow_self
  have short:=Nat.log_le_self 2 p
  unfold ProtocolRAMPortScale.bitWidth
  omega

/-- Labels, registers and slots of the very same installed program. -/
theorem gate_hardware_at {h W factor M copies T p text words : ℕ}
    (cpu : W≤factor*h) (width : p≤h) (count : words≤2^(h/2))
    (physical : text≤15*(words+1)+199+8*ProtocolRAMPortScale.bitWidth p)
    (table : (2^(h/2)*h)*T≤(M*copies)*p) :
    text*W*T≤245*factor*((M*copies)*p) := by
  let U:=2^(h/2)
  have one : 1≤U := Nat.one_le_two_pow
  have bitcap : ProtocolRAMPortScale.bitWidth p≤2*U := scale_width width
  have capacity : text≤245*U := by omega
  calc
    text*W*T ≤ ((245*U)*(factor*h))*T := Nat.mul_le_mul_right _ (Nat.mul_le_mul capacity cpu)
    _ = (245*factor)*((U*h)*T) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ table

theorem gate_bill_at {h W factor M copies T sites bits p : ℕ}
    (cpu : W≤factor*h) (width : p≤h)
    (table : (2^(h/2)*h)*T≤(M*copies)*p) (slots : (sites*bits)*T≤(M*copies)*p) :
    terminalGateBill h W factor sites bits p*T ≤ 318*factor*((M*copies)*p) := by
  let U:=2^(h/2)
  have one : 1≤U := Nat.one_le_two_pow
  have bitsmall : ProtocolRAMPortScale.bitWidth p≤2*U := scale_width width
  have hw : (4+10*U)*W≤(14*U)*(factor*h) :=
    Nat.mul_le_mul (by omega) cpu
  have exponent : (56+4*ProtocolRAMPortScale.bitWidth p)*h≤(64*U)*h :=
    Nat.mul_le_mul_right _ (by omega)
  have plain : 80*h≤80*(U*h) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ one)
  have price : terminalGateBill h W factor sites bits p≤
      factor*(158*(U*h)+160*(sites*bits)) := by
    unfold terminalGateBill
    change (4+10*U)*W+_≤_
    calc
      _ ≤ (14*U)*(factor*h) + factor*(40*(h+h+4*sites*bits)+(64*U)*h) :=
        Nat.add_le_add hw (Nat.mul_le_mul_left _ (Nat.add_le_add_left exponent _))
      _ = factor*(78*(U*h)+80*h+160*(sites*bits)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  calc
    terminalGateBill h W factor sites bits p*T ≤ (factor*(158*(U*h)+160*(sites*bits)))*T :=
      Nat.mul_le_mul_right _ price
    _ = factor*(158*((U*h)*T)+160*((sites*bits)*T)) := by ring
    _ ≤ factor*(158*((M*copies)*p)+160*((M*copies)*p)) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ table) (Nat.mul_le_mul_left _ slots))
    _ = _ := by ring

/-- A ceiling logarithm may overshoot the physical population by a factor of two. -/
theorem table_fund {h population : ℕ} (large : 10≤h) (room : 2^h≤2*population) :
    (2^(h/2))*h≤population := by
  let a:=h/2-5
  have eq : h/2=a+5 := by dsimp [a];omega
  have cap : 2*h≤2^(h-h/2) := by
    calc
      2*h≤(a+1)*32 := by dsimp [a];omega
      _ ≤ 2^a*32 := Nat.mul_le_mul_right _ Nat.lt_two_pow_self
      _ = 2^(a+5) := by rw [pow_add];rfl
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega)
  have price : 2*((2^(h/2))*h)≤2^h := by
    calc
      _ = 2^(h/2)*(2*h) := by ring
      _ ≤ 2^(h/2)*2^(h-h/2) := Nat.mul_le_mul_left _ cap
      _ = _ := by rw [←pow_add];congr 1;omega
  omega

/-- Take the same age as the other terminal arrays. Increasing the coefficient
of the age denominator preserves this estimate. The lane stride and both
structural exponents are fixed before choosing the word width. -/
theorem eventually_private_gate (R n v e B : ℕ)
    (bought : 2*e+(v+(2*(n+1)+1)+1)≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B); let T:=2^J
      ∀ M copies stages factor W socket : ℕ, 2^h≤2*(M*copies) →
      stages=(M*copies)*T^v → W≤factor*h → 0< socket → socket≤ scale J e →
      let p:=h/(16*socket)
      2*aliasBits T R n≤h ∧ terminalGateBill h W factor stages (aliasBits T R n) p*T≤
        318*factor*((M*copies)*p) := by
  have pos : 0<B := by omega
  filter_upwards [age_room B pos,eventually_late (R+1) B pos,eventually_ge_atTop 10] with h room age large
  let J:=Nat.log 2 h/(2*B)
  let T:=2^J
  change 0<J ∧ 32*T^B≤h at room
  change R+1≤J at age
  dsimp only
  intro M copies stages factor W socket fund pop cpu occupied footprint
  let m:=2*(n+1)+1
  let d:=v+m+1
  let p:=h/(16*socket)
  have one : 0<T := Nat.two_pow_pos _
  have two : 2≤T := Nat.one_lt_two_pow (by omega : J≠0)
  have bits : aliasBits T R n≤T^m := alias_power two (age.trans (Nat.lt_two_pow_self.le))
  have socketCap : socket≤T^(2*e) := by
    apply footprint.trans
    change 2^(e*(J+1))≤(2^J)^(2*e)
    rw [←pow_mul]
    apply Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
    have c:=Nat.mul_le_mul_left e (show J+1≤2*J by omega)
    nlinarith only [c]
  have stack : T^d≤p := by
    apply (Nat.le_div_iff_mul_le (show 0<16*socket by positivity)).mpr
    calc
      T^d*(16*socket) ≤ T^d*(16*T^(2*e)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ socketCap)
      _ = 16*T^(2*e+d) := by rw [pow_add];ring
      _ ≤ 32*T^B := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right one bought)
      _ ≤ h := room.2
  have bitRoom : T^m≤T^B := Nat.pow_le_pow_right one (by dsimp [m] at *;omega)
  have fits : 2*aliasBits T R n≤h :=
    (Nat.mul_le_mul (by decide : 2≤32) (bits.trans bitRoom)).trans room.2
  have area : (stages*aliasBits T R n)*T≤(M*copies)*p := by
    rw [pop]
    calc
      _ ≤ ((M*copies)*T^v*T^m)*T :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ bits)
      _ = (M*copies)*T^d := by dsimp [d];rw [pow_succ,pow_add];ring
      _ ≤ _ := Nat.mul_le_mul_left _ stack
  have paid : T≤p := by
    have order : 1≤d := by dsimp [d];omega
    simpa only [pow_one] using (Nat.pow_le_pow_right one order).trans stack
  exact ⟨fits,gate_bill_at cpu (Nat.div_le_self ..) (Nat.mul_le_mul (table_fund large fund) paid) area⟩

end Hierarchy.DescentCompiler.TerminalScale

end OAI
