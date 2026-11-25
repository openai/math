import OAI.Hierarchy.DescentExteriorNativeInvoice
import OAI.Hierarchy.DescentTerminalCohortRun
import OAI.Hierarchy.DescentPrivateGateScale

namespace OAI
/-! # Native price of remixed-copy ancestry and the genuine stable frozen roster -/
namespace Hierarchy.DescentExteriorReplay
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentStaticWordColumn DescentTerminalFrozenRoster DescentTerminalCohortArena
noncomputable section

theorem replay_names (w n : ℕ) (hs:List Hop) : names (steps w n hs)≤211*hs.length+20 := by
  induction hs with
  | nil => simp [steps,names_scan,Expr.work]
  | cons hop hs ih =>
    have charge:names (code w n hop)≤211:=by
      rcases hop with ⟨s,b,g,t,c,d⟩
      cases c <;> simp [code,names_scan,read,key,Expr.work]
    simp only [steps,names_seq,List.length_cons]
    omega

variable (hop:ℕ→Hop) (start f bits age n homes w:ℕ) (ends:stop start f bits n homes<2^w) (src:Bank)
local notation "run" => Procedure.seq (steps w n (schedule hop age)) (machine start f bits n homes ends src)
local notation "ticks_" => clocks n (schedule hop age)+ticks start f bits n homes ends src

/-- One program printed for the full selected matrix chronology and the final roster.
Only the genuine frozen-cohort count is multiplied by the number of dates. -/
theorem cohort_counts : ticks_+7*names run≤
    115*ROM.size f bits+31000*(age+homes+1)+800*(age+1)*n := by
  have cpu:=total_price n (schedule hop age)
  have listing:=replay_names w n (schedule hop age)
  have roster:=ticks_le start f bits n homes ends src
  have text:=names_le start f bits n homes ends src
  rw [names_seq]
  simp only [schedule, List.length_map, List.length_range] at cpu listing ⊢
  rw [Nat.mul_add] at cpu
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at *
  rw [Nat.mul_left_comm age 96 n] at cpu
  simp only [Nat.mul_assoc] at *
  omega

/-- Every original exterior port has `copies` literal descendants of `s` bits.
The remixed live fibre retains `2^live` of them behind one replayed row. -/
theorem cohort_tariff (M copies s E live T h factor:ℕ) (pop:n*(2^live)=E*copies)
    (ancestor:800*(age+1)*h≤ s*2^live) (dates:age+1≤2^(h/2))
    (dictionary:ROM.size f bits≤3*2^(h/2)) (host:homes*h*T≤M*(copies*s))
    (fixed:2^(h/2)*h*T≤M*(copies*s)) (arch:w≤factor*h) :
    (ticks_+7*names run)*w*T≤63000*factor*((copies*s)*(M+T*E)) := by
  let fund:=(copies*s)*(M+T*E)
  have inside:M*(copies*s)≤fund:=by
    dsimp [fund];rw [Nat.mul_comm M,Nat.mul_add];omega
  have outside:(E*copies)*s*T≤fund:=by
    change _≤(copies*s)*(M+T*E)
    rw [Nat.mul_add,show E*copies*s*T=(copies*s)*(T*E) by ring];omega
  have tables: ROM.size f bits*h*T≤3*fund:=calc
    _ ≤ (3*2^(h/2))*h*T := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ dictionary)
    _ = 3*(2^(h/2)*h*T) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (fixed.trans inside)
  have time_: (age+1)*h*T≤fund := (Nat.mul_le_mul_right T (Nat.mul_le_mul_right h dates)).trans (fixed.trans inside)
  have ancestry:(800*(age+1)*n)*h*T≤fund:=calc
    _ = (800*(age+1)*h)*n*T := by ring
    _ ≤ (s*2^live)*n*T := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ancestor)
    _ = (E*copies)*s*T := by rw [←pop];ring
    _ ≤ _ := outside
  have core:=cohort_counts hop start f bits age n homes w ends src
  calc
    _ ≤ ((115*ROM.size f bits+31000*(age+homes+1)+800*(age+1)*n)*h*T)*factor := by
      calc
        _ ≤ (115*ROM.size f bits+31000*(age+homes+1)+800*(age+1)*n)*(factor*h)*T :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul core arch)
        _ = _ := by ring
    _ = (115*(ROM.size f bits*h*T)+31000*((age+1)*h*T+homes*h*T)+((800*(age+1)*n)*h*T))*factor := by ring
    _ ≤ (115*(3*fund)+31000*(fund+fund)+fund)*factor :=
      Nat.mul_le_mul_right _ (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ tables)
        (Nat.mul_le_mul_left _ (Nat.add_le_add time_ (host.trans inside)))) ancestry)
    _ ≤ _ := by dsimp [fund];ring_nf;omega
end
end Hierarchy.DescentExteriorReplay

end OAI
