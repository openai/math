import OAI.Hierarchy.TaggedShorterControlCost
import OAI.Hierarchy.ProtocolRAMMachine
import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.ProbeStageProgramSize

namespace OAI
/-! # Charging the physical calendar verifier by its native text and row extent -/

noncomputable section
namespace Hierarchy.TaggedShorterControlHistory
open ThreeFlat Routing Diagonal TraceRows TraceBanks TraceIssue
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProbeStage.Native
open scoped Classical BigOperators

theorem code_price {W : ℕ} (A : Procedure W) (N : ℕ) (bound : text A≤N) :
    TaggedShorterClock.unitPrice 1 (A.labels+3) (A.registers+1) ≤ 100000*(N+1)^2 := by
  have labels : A.labels≤N := by unfold text at bound; omega
  have regs : A.registers≤N := by unfold text at bound; omega
  have instr (r : ℕ) : instructionBudget 1 r =
      2*(8+(1*10+1)+(r*((1*10+1)+1)+1)+2)+2*((1+1)*10+1)+10 := rfl
  calc
    _ ≤ TaggedShorterClock.unitPrice 1 (N+3) (N+1) := by
      simp only [TaggedShorterClock.unitPrice,TaggedShorterClock.initialPrice,
        TraceUniformRow.canonicalCost,TaggedShorterCPURow.price,instr]
      gcongr
    _ ≤ _ := by
      simp only [TaggedShorterClock.unitPrice,TaggedShorterClock.initialPrice,
        TraceUniformRow.canonicalCost,TaggedShorterCPURow.price,instr]
      ring_nf
      omega

/-- On the actual linked native machine, all CPU, sort, chronology,
exposed and hidden pins cost at most a constant times the padded list,
times one parent word, times the square of the program text. -/
theorem native_control_bill_width {F : Type*} [CommRing F] {W h m f u S : ℕ}
    (A : Procedure W) (ret st : Word W) (N : ℕ) (cost : text A≤N)
    (cheap : ProtocolRAM.CheapCode A) (hw : 3≤W+1) (word : W+1≤4*(h+1)) (height : m≤2*h)
    (labels : A.labels+3≤2^(W+1)) (hs : S≤2^(W+1))
    (times : f+u≤2^(W+1)) (fits : S+(f+u)≤2^m) (addr : Fin u → Word (W+1)) :
    let net := (network (F:=F) (m:=m) (a:=28) (machine A ret) hw labels st hs times addr).compactHidden
    net.cells + net.internal + Fintype.card (Pin S f u W (A.registers+1) m 28) ≤
      20000000*2^m*(h+1)*(N+1)^2 := by
  intro net
  have ok := machine_cheap A ret (fun pc reg pub out i=>cheap pc reg pub out i)
  have whole := normalized_size (F:=F) (a:=28) (machine A ret) ok hw labels st hs times addr fits
  apply whole.trans
  let V := (N+1)^2
  have regs : A.registers≤N := by unfold text at cost; omega
  have ver : TaggedShorterClock.unitPrice 1 (A.labels+3) (A.registers+1) ≤ 100000*V := code_price A N cost
  have extent : f+1≤2*2^m := by have enough : 1≤2^m := Nat.one_le_two_pow; omega
  have mc : m+1≤2*(h+1) := by omega
  have vl : 1≤V := by
    change 0 < (N+1)^2
    positivity
  have rc : 100000+(A.registers+1) ≤ 100001*V := by dsimp [V]; nlinarith
  have sc : 1000+400*28 ≤ 12200*V := by omega
  calc
    _ ≤ (2*2^m)*(4*(h+1))*(4*(100000*V))+
         2^m*((100001*V)*(4*(h+1))+(12200*V)*(2*(h+1))) := by gcongr
    _ ≤ _ := by
      change _ ≤ 20000000*2^m*(h+1)*V
      ring_nf
      omega

theorem native_control_bill {F : Type*} [CommRing F] {h m f u S : ℕ}
    (A : Procedure (2*h+1)) (ret st : Word (2*h+1)) (N : ℕ) (cost : text A≤N)
    (cheap : ProtocolRAM.CheapCode A) (hh : 0<h) (height : m≤2*h)
    (labels : A.labels+3≤2^((2*h+1)+1)) (hs : S≤2^((2*h+1)+1))
    (times : f+u≤2^((2*h+1)+1)) (fits : S+(f+u)≤2^m) (addr : Fin u → Word ((2*h+1)+1)) :
    let net := (network (F:=F) (m:=m) (a:=28) (machine A ret) (by omega) labels st hs times addr).compactHidden
    net.cells + net.internal + Fintype.card (Pin S f u (2*h+1) (A.registers+1) m 28) ≤
      20000000*2^m*(h+1)*(N+1)^2 :=
  native_control_bill_width A ret st N cost cheap (by omega) (by omega) height labels hs times fits addr

end Hierarchy.TaggedShorterControlHistory

end
end OAI
