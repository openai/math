import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentMachineAmplitude
import OAI.Optimization.LinearProgramming.PriceGame.MarketActionsMachine

/-! A single finite bit-stack program for every quantity vector, bid matrix and initial
flow/dual frame. Even noncanonical frames satisfy the ordinary unguarded fold's size bound. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Augment
namespace Machine

variable {α β : Type}

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure

private theorem fst_len (e₁ : α → List Bool) (e₂ : β → List Bool) (z : α × β) :
    (e₁ z.1).length ≤ (prodCode e₁ e₂ z).length := by
  simp only [prodCode, pairBits_length]
  omega

private theorem snd_len (e₁ : α → List Bool) (e₂ : β → List Bool) (z : α × β) :
    (e₂ z.2).length ≤ (prodCode e₁ e₂ z).length := by
  simp only [prodCode, pairBits_length]
  omega

private theorem signed_len (z : ℤ) : (intCode z).length = z.natAbs.size+3 := by
  simp [intCode, intData, prodCode, pairBits_length, boolCode, Nat.size_eq_bits_len]
  omega

private theorem pow_of_size {x h : ℕ} (hx : x.size ≤ h) : x ≤ 2^h :=
  (Nat.lt_size_self x).le.trans (Nat.pow_le_pow_right (by decide) hx)

private theorem unsigned_control {xs : List ℕ} {H : ℕ} (h : (listCode Nat.bits xs).length ≤ H) :
    ∀ v ∈ xs, v ≤ 2^H := by
  intro v hv
  apply pow_of_size
  rw [← Nat.size_eq_bits_len]
  exact (code_le_of_mem Nat.bits hv).trans h

private theorem signed_control {xs : List ℤ} {H : ℕ} (h : (bankCode xs).length ≤ H) :
    ∀ v ∈ xs, v.natAbs ≤ 2^H := by
  intro v hv
  have hv' := (code_le_of_mem intCode hv).trans h
  rw [signed_len] at hv'
  exact pow_of_size (by omega)

private structure Room (s : Environment) (H : ℕ) : Prop where
  fixed : (fixedCode s.1).length ≤ H
  signs : s.1.2.1.length ≤ H
  flow : s.2.1.length ≤ H
  expert : s.2.2.1.length ≤ H
  option : s.2.2.2.length ≤ H
  den : s.1.1.natAbs ≤ 2^H
  bid : ∀ v ∈ s.1.2.2.2, v.natAbs ≤ 2^H

private theorem initial_room (s : Environment) (H : ℕ) (hl : (envCode s).length ≤ H) :
    Room s H ∧ DynamicBound s.2 (2^H) := by
  have fx := (fst_len fixedCode dynCode s).trans hl
  have dy := (snd_len fixedCode dynCode s).trans hl
  have den := (fst_len intCode FlowMachine.Rows.statCode s.1).trans fx
  have st := (snd_len intCode FlowMachine.Rows.statCode s.1).trans fx
  have sig := (fst_len FlowMachine.Rows.blist (prodCode FlowMachine.Rows.blist bankCode) s.1.2).trans st
  have rest := (snd_len FlowMachine.Rows.blist (prodCode FlowMachine.Rows.blist bankCode) s.1.2).trans st
  have bid := (snd_len FlowMachine.Rows.blist bankCode s.1.2.2).trans rest
  have fl := (fst_len FlowMachine.flowCode banksCode s.2).trans dy
  have bk := (snd_len FlowMachine.flowCode banksCode s.2).trans dy
  have ex := (fst_len bankCode bankCode s.2.2).trans bk
  have opt := (snd_len bankCode bankCode s.2.2).trans bk
  rw [signed_len] at den
  exact ⟨⟨fx,(list_length_le_code boolCode _).trans sig,(list_length_le_code Nat.bits _).trans fl,
    (list_length_le_code intCode _).trans ex,(list_length_le_code intCode _).trans opt,
    pow_of_size (by omega),signed_control bid⟩,⟨unsigned_control fl,signed_control ex,signed_control opt⟩⟩

private theorem action_shape (a : ℕ) (s : Environment) :
    (action (a,s)).2.1.length = s.2.1.length ∧ (action (a,s)).2.2.1.length = s.2.2.1.length ∧
      (action (a,s)).2.2.2.length = s.2.2.2.length := by
  by_cases h : a = 0
  · simp [action,h,marketDouble]
  · simp [action,h,marketUnit,finishStep,FlowMachine.update,block,makeSeed]

private def amplitude (H k : ℕ) := 2^((2*H+4)*(k+1))

private theorem amplitude_ge (H k : ℕ) : 2^H ≤ amplitude H k := by
  apply Nat.pow_le_pow_right (by decide)
  nlinarith

private theorem dynamic_mono {s : Dynamic} {x y : ℕ} (h : DynamicBound s x) (hxy : x ≤ y) :
    DynamicBound s y :=
  ⟨fun v hv => (h.flow v hv).trans hxy, fun v hv => (h.expert v hv).trans hxy,
   fun v hv => (h.option v hv).trans hxy⟩

private theorem transport_bound (s : Environment) (a H k : ℕ) (room : Room s H)
    (bound : DynamicBound s.2 (amplitude H k)) :
    Room (action (a,s)) H ∧ DynamicBound (action (a,s)).2 (amplitude H (k+1)) := by
  obtain ⟨hf,he,ho⟩ := action_shape a s
  refine ⟨⟨room.fixed,room.signs,hf.le.trans room.flow,he.le.trans room.expert,ho.le.trans room.option,
    room.den,room.bid⟩,?_⟩
  let U := amplitude H k
  have hU : 1 ≤ U := Nat.one_le_two_pow
  have hC : 2^H ≤ U := amplitude_ge _ _
  have hK : horizon s ≤ 2*H := (Nat.sub_le ..).trans (by
    have h1 := room.signs; have h2 := room.option; omega)
  have hM : 2*H+4 ≤ 2^(2*H+4) := (2*H+4).lt_two_pow_self.le
  have next : amplitude H (k+1) = (2^(2*H+4))*U := by
    dsimp [U,amplitude]
    rw [show (2*H+4)*(k+1+1) = (2*H+4)+(2*H+4)*(k+1) by ring,pow_add]
  have hnext : (2*H+4)*U ≤ amplitude H (k+1) := next ▸ Nat.mul_le_mul_right _ hM
  by_cases hz : a = 0
  · simp only [action,hz,ite_true]
    refine ⟨?_,fun v hv => (bound.expert v hv).trans (by nlinarith),
      fun v hv => (bound.option v hv).trans (by nlinarith)⟩
    intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    have hw' : w ≤ U := bound.flow w hw
    nlinarith
  · simp only [action,hz,ite_false]
    apply dynamic_mono (marketUnit_bound (a-1) s U (2^H) bound room.den room.bid)
    apply (max_le _ _).trans hnext
    · have ht := Nat.mul_le_mul_right (horizon s) hU
      have hv := Nat.mul_le_mul_right U hK
      nlinarith
    · have ht := Nat.mul_le_mul_right U hK
      have hs := Nat.mul_le_mul_left (horizon s) hC
      nlinarith

private theorem fold_bounds (xs : List ℕ) (s : Environment) (H j : ℕ) (room : Room s H)
    (bound : DynamicBound s.2 (amplitude H j)) :
    let t := xs.foldl (fun x i => action (i,x)) s
    Room t H ∧ DynamicBound t.2 (amplitude H (j+xs.length)) := by
  induction xs generalizing s j with
  | nil => simpa using And.intro room bound
  | cons a xs ih =>
    obtain ⟨hr,hb⟩ := transport_bound s a H j room bound
    simpa [List.foldl_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (action (a,s)) (j+1) hr hb

private theorem list_bound (ea : α → List Bool) (xs : List α) (B : ℕ)
    (h : ∀ x ∈ xs, (ea x).length ≤ B) :
    (listCode ea xs).length ≤ xs.length*(2*B+2)+1 := by
  simpa using listCode_length_map_bound ea id xs B h

private noncomputable def foldGrowth : Polynomial ℕ := Polynomial.C 100 * (Polynomial.X+1)^4

/-- Every encoding visited by any execution has polynomial length in the original binary
input. The proof accounts for all integer words and their list and product framing. -/
theorem fold_length (xs : List ℕ) (s : Environment) (i : ℕ) :
    (envCode ((xs.take i).foldl (fun x j => action (j,x)) s)).length ≤
      foldGrowth.eval ((listCode Nat.bits xs).length+(envCode s).length) := by
  let H := (listCode Nat.bits xs).length+(envCode s).length
  have hs : (envCode s).length ≤ H := Nat.le_add_left ..
  obtain ⟨room,bound⟩ := initial_room s H hs
  let t := (xs.take i).foldl (fun x j => action (j,x)) s
  obtain ⟨ht,hc⟩ := fold_bounds (xs.take i) s H 0 room (dynamic_mono bound (amplitude_ge H 0))
  have hn : (xs.take i).length ≤ H :=
    (show (xs.take i).length ≤ xs.length by simp).trans
      ((list_length_le_code Nat.bits xs).trans (Nat.le_add_right ..))
  let E := (2*H+4)*(H+1)
  have hexp : (2*H+4)*(0+(xs.take i).length+1) ≤ E := Nat.mul_le_mul_left _ (by omega)
  have size (n : ℕ) (h : n ≤ amplitude H (0+(xs.take i).length)) : n.size ≤ E+1 := by
    have hv := Nat.size_le_size (h.trans (Nat.pow_le_pow_right (by decide) hexp))
    simpa [Nat.size_pow] using hv
  have fl := list_bound Nat.bits t.2.1 (E+1) (fun v hv => by
    rw [Nat.size_eq_bits_len]; exact size v (hc.flow v hv))
  have ex := list_bound intCode t.2.2.1 (E+4) (fun v hv => by
    rw [signed_len]; have h := size v.natAbs (hc.expert v hv); omega)
  have opt := list_bound intCode t.2.2.2 (E+4) (fun v hv => by
    rw [signed_len]; have h := size v.natAbs (hc.option v hv); omega)
  have fh := fl.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ ht.flow) _)
  have eh := ex.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ ht.expert) _)
  have oh := opt.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ ht.option) _)
  change (envCode t).length ≤ foldGrowth.eval H
  simp only [envCode,dynCode,FlowMachine.Rows.dynamicCode,FlowMachine.Rows.nlist,
    FlowMachine.Rows.ilist,prodCode,pairBits_length,foldGrowth,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  have ff : (fixedCode t.1).length ≤ H := ht.fixed
  simp only [fixedCode,FlowMachine.Rows.statCode,FlowMachine.Rows.ilist,prodCode,pairBits_length] at ff
  dsimp [E] at fh eh oh
  nlinarith only [ff,fh,eh,oh,Nat.zero_le H,Nat.zero_le (H^2),Nat.zero_le (H^3),Nat.zero_le (H^4)]

abbrev SolverInput := List ℕ × Environment
abbrev solverInputCode : SolverInput → List Bool := prodCode (listCode Nat.bits) envCode

/-- The supply digits generate the actual number of doublings and single-expert increments. -/
def execute (z : SolverInput) : Dynamic :=
  ((ScheduleMachine.actionStream z.1).foldl (fun t i => action (i,t)) z.2).2

/-- A uniform finite program which reads every bit plane, computes every augmenting path,
and writes the final flow and dual arrays. -/
noncomputable def solveP : Procedure solverInputCode dynCode execute := by
  let actions := ScheduleMachine.actionStreamP.comp (first (listCode Nat.bits) envCode)
  let initial := second (listCode Nat.bits) envCode
  let fold := foldList 0 actionP foldGrowth fold_length
  let result := fold.comp (actions.pair initial)
  exact (second fixedCode dynCode).comp result

theorem solve_deploy (o : OracleSpec.WordOracle) (z : SolverInput) :
    (OracleSpec.BitCode.deploy solveP).ComputesWithin o (solverInputCode z)
      (3*solveP.bound.eval (solverInputCode z).length+2*(solverInputCode z).length+2)
      (fun history bits => history=[] ∧ bits = dynCode (execute z)) :=
  OracleSpec.BitCode.deploy_correct solveP o z

end Machine
end Augment
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
