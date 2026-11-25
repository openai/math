import OAI.Hierarchy.DescentExteriorSnapshotSeed
import OAI.Hierarchy.DescentExteriorHopTariff

namespace OAI
/-! # Charging the authentic literal and seed initialization of exterior ancestry -/
namespace Hierarchy.DescentExteriorReplay.Snapshots
open DescentStaticWordColumn
open scoped BigOperators
variable {k : ℕ} (A : Snapshots k)

theorem printed (w start f age : ℕ) :
    A.clocks f age + 7*names (A.program w start f age)=
      109*(age+1)+115*(∑ j ∈ Finset.range age,HopLiteral.words (A.hosts j) k f) := by
  induction age with
  | zero => simp [program,clocks,names_mount]
  | succ t ih =>
    rw [clocks,program,names_seq,Finset.sum_range_succ]
    unfold HopLiteral.program
    rw [names_mount]
    omega

theorem seeded_price {n : ℕ} (w base f scratch age : ℕ) (rank : Fin n → ℕ)
    (h T H E copies s live M factor : ℕ)
    (extent : A.start base f age ≤ base+2*H+3*2^(h/2))
    (whole : w≤factor*h) (dates : age+1≤2^(h/2))
    (fibre : n*2^live=E*copies) (visits : 800*(age+1)*h≤ s*2^live)
    (hosts : H*h*T≤M*(copies*s)) (rom : 2^(h/2)*h*T≤M*(copies*s)) :
    (A.clocks f age+(4+10*n)+7*names ((A.program w base f age).seq (seedProgram w scratch rank)))*w*T
      ≤ 1000*factor*((copies*s)*(M+T*E)) := by
  let fund := (copies*s)*(M+T*E)
  have inner : M*(copies*s)≤fund := by dsimp [fund]; rw [Nat.mul_comm M,Nat.mul_add]; omega
  have outer : E*copies*s*T≤fund := by
    dsimp [fund]; rw [Nat.mul_add,show E*copies*s*T=(copies*s)*(T*E) by ring];omega
  have one : 115*h≤800*(age+1)*h := Nat.mul_le_mul_right h (by omega)
  have ancestry : 115*n*h*T ≤ fund := calc
    _ = (115*h)*n*T := by ring
    _ ≤ (s*2^live)*n*T := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (one.trans visits))
    _ = E*copies*s*T := by rw [←fibre];ring
    _ ≤ fund := outer
  have mass : (∑ j ∈ Finset.range age,HopLiteral.words (A.hosts j) k f) ≤ 2*H+3*2^(h/2) := by
    rw [A.start_eq_sum] at extent;omega
  have snapshotPrice := A.printed w base f age
  have labels : names (seedProgram w scratch rank)=15*(n+1) :=
    names_mount w scratch (seedData rank) n
  have bound : A.clocks f age+(4+10*n)+7*names ((A.program w base f age).seq (seedProgram w scratch rank))
      ≤ 230*H+563*2^(h/2)+115*n := by
    have nonempty:=Nat.two_pow_pos (h/2)
    rw [names_seq,labels]
    omega
  calc
    _ ≤ (230*H+563*2^(h/2)+115*n)*(factor*h)*T := Nat.mul_le_mul_right _ (Nat.mul_le_mul bound whole)
    _ = (230*(H*h*T)+563*(2^(h/2)*h*T)+115*n*h*T)*factor := by ring
    _ ≤ (230*fund+563*fund+fund)*factor := Nat.mul_le_mul_right _ (Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left _ (hosts.trans inner)) (Nat.mul_le_mul_left _ (rom.trans inner))) ancestry)
    _ = 794*(factor*fund) := by ring
    _ ≤ 1000*(factor*fund) := Nat.mul_le_mul_right _ (by decide : 794 ≤ 1000)
    _ = _ := (Nat.mul_assoc 1000 factor fund).symm

end Hierarchy.DescentExteriorReplay.Snapshots

end OAI
