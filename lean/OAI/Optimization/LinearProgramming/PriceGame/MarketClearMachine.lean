import OAI.Optimization.LinearProgramming.PriceGame.MarketInitializeBridge
import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentMachineSolution
import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineCanonicalOutput

/-! Full signed rational price clearing on ordinary binary words, from the
original input through LCM, augmentation and canonical zero-terminal readout. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace InitializeMachine
open ExactQuantumFactoring.BitStackProgram Procedure
open Augment.Machine FlowMachine

abbrev LCMInput := List ℚ × (ℕ × RationalStatic)
abbrev lcmInputCode : LCMInput → List Bool := prodCode qlist (prodCode unaryCode rationalStaticCode)

def withUnit (a : LCMInput) : Input :=
  ((a.1.foldl (fun d q => Nat.lcm d q.den) 1,a.1),a.2)

private def solveAndExtract (z : SolverInput) : List ℚ × List ℚ :=
  Output.output (z.1,(z.2.1,execute z))

private noncomputable def solveAndExtractP : Procedure solverInputCode (prodCode qlist qlist)
    solveAndExtract := by
  let q := first nlist environmentCode
  let state := second nlist environmentCode
  let staticWord := (first fixedCode dynCode).comp state
  exact (Output.outputP.comp (q.pair (staticWord.pair solveP))).congrFun (fun _ => rfl)

def clearWithUnit (a : Input) : List ℚ × List ℚ := solveAndExtract (initialWord a)

def clearMarket (a : LCMInput) : List ℚ × List ℚ := clearWithUnit (withUnit a)

/-- Compute prices and transfers on a common supply unit given in the binary input. -/
noncomputable def clearWithUnitP : Procedure inputCode (prodCode qlist qlist) clearWithUnit :=
  solveAndExtractP.comp initializeP

/-- A single finite oracle-free program computes the market from scratch. -/
noncomputable def clearP : Procedure lcmInputCode (prodCode qlist qlist) clearMarket :=
  solveAndExtractP.comp initialLCMP

variable {m g : ℕ}

/-- A prescribed supply denominator refines the exact same rational algorithm. -/
theorem clearWithUnit_eq (I : Augment.Input m g) (L : Fin m → ℚ) (Q : ℕ) :
    let out := computeWithDenominator I.positive L I.available I.intercept Q
    clearWithUnit (typed I Q L) = (List.ofFn out.1,packedCells out.2) := by
  let D := grid (packedCells (bid I.intercept))
  let qty (e : Fin m) := Denominator.qty Q (L e)
  have hi : initialWord (typed I Q L) = (List.ofFn qty,packEnv I D I.initial) := initial_agrees I Q L
  have hd := grid_pos (packedCells (bid I.intercept))
  have hc := intercept_grid I
  unfold clearWithUnit
  rw [hi]
  change Output.output (List.ofFn qty,
    ((packEnv I D I.initial).1, execute (List.ofFn qty,packEnv I D I.initial))) = _
  have run : execute (List.ofFn qty, packEnv I D I.initial) = (packEnv I D (I.solve qty)).2 := by
    simpa only [List.ofFn_eq_map] using execute_exact I qty D hd hc
  rw [run]
  exact Output.output_pack I qty D (I.solve qty) hd (fun e j _ => hc e j)

/-- The computed least common unit yields the same exact price vector and
tie-broken allocation as the recursive trial, including zero-weight experts. -/
theorem clear_eq (I : Augment.Input m g) (L : Fin m → ℚ) :
    let req : LCMInput := (List.ofFn L, (typed I 1 L).2)
    let out := TrialExecution.computeAtCommonWeightUnit I.positive L I.available I.intercept
    clearMarket req = (List.ofFn out.1, packedCells out.2) := by
  let Q := TrialExecution.weightDenominator L
  let req : LCMInput := (List.ofFn L,(typed I 1 L).2)
  have hq : (List.ofFn L).foldl (fun d q => Nat.lcm d q.den) 1 = Q := by
    simpa only [List.ofFn_eq_map] using InputMachine.leastDenominator_agrees L
  have hw : withUnit req = typed I Q L :=
    congrArg (fun d : ℕ => ((d,List.ofFn L),(typed I 1 L).2)) hq
  change clearWithUnit (withUnit req) = _
  rw [hw]
  exact clearWithUnit_eq I L Q

/-- A supplied common denominator controls each transfer in the output of
this single uniform polynomial bit program. The price grid and the paper's
absolute bound use only the input bids. -/
theorem balanced_with_prescribed_unit (oracle : OracleSpec.WordOracle)
    (I : Augment.Input m g) (L : Fin m → ℚ) (Q : ℕ) (hQ : 0 < Q)
    (hL : ∀ e, 0 ≤ L e) (hden : ∀ e, (L e).den ∣ Q) :
    let req := typed I Q L
    let out := computeWithDenominator I.positive L I.available I.intercept Q
    Balanced I.positive L I.accepts I.intercept out.1 out.2 ∧
    (∀ e o, ∃ a : ℕ, L e*out.2 e o = (a:ℚ)/(Q:ℚ)) ∧
    (∀ D : ℕ, (∀ e j, I.accepts e j → NumberBounds.OnGrid D (I.intercept e j)) →
      ∀ j, NumberBounds.OnGrid D (out.1 j)) ∧
    (∀ C : ℚ, 0 ≤ C → (∀ e j, I.accepts e j → |I.intercept e j| ≤ C) →
      ∀ j, |out.1 j| ≤ 2*((m+g+1:ℕ):ℚ)*C) ∧
    (OracleSpec.BitCode.deploy clearWithUnitP).ComputesWithin oracle (inputCode req)
      (3*clearWithUnitP.bound.eval (inputCode req).length+2*(inputCode req).length+2)
      (fun hist bits => hist=[] ∧ bits = prodCode qlist qlist (List.ofFn out.1,packedCells out.2)) := by
  obtain ⟨hb,hm,hg,ha⟩ := computeWithDenominator_spec I.positive L I.available I.intercept Q hQ hL hden
  have run := OracleSpec.BitCode.deploy_correct clearWithUnitP oracle (typed I Q L)
  exact ⟨hb,hm,hg,ha,by simpa only [clearWithUnit_eq I L Q] using run⟩

/-- End-to-end unit-cost model is the bit-stack interpreter with its actual
polynomial instruction budget and recorded empty oracle history. -/
theorem clear_deploy (o : OracleSpec.WordOracle) (I : Augment.Input m g) (L : Fin m → ℚ) :
    let req : LCMInput := (List.ofFn L, (typed I 1 L).2)
    let out := TrialExecution.computeAtCommonWeightUnit I.positive L I.available I.intercept
    (OracleSpec.BitCode.deploy clearP).ComputesWithin o (lcmInputCode req)
      (3*clearP.bound.eval (lcmInputCode req).length+2*(lcmInputCode req).length+2)
      (fun hist bits => hist=[] ∧ bits=prodCode qlist qlist (List.ofFn out.1,packedCells out.2)) := by
  have h := OracleSpec.BitCode.deploy_correct clearP o (List.ofFn L,(typed I 1 L).2)
  simpa only [clear_eq I L] using h

/-- The balanced-prices theorem in the ordinary bit model. The same code
and polynomial apply to all dimensions, signs, rational bids and supplies. -/
theorem balanced_outputs_in_polynomial_time (oracle : OracleSpec.WordOracle)
    (I : Augment.Input m g) (L : Fin m → ℚ) (hL : ∀ e, 0 ≤ L e) :
    let req : LCMInput := (List.ofFn L, (typed I 1 L).2)
    ∃ (y : Fin g → ℚ) (f : Fin m → Option (Fin g) → ℚ),
      Balanced I.positive L I.accepts I.intercept y f ∧
      (∀ e o, ∃ a : ℕ, L e*f e o = (a:ℚ)/(TrialExecution.weightDenominator L : ℚ)) ∧
      (∀ D : ℕ, (∀ e j, I.accepts e j → NumberBounds.OnGrid D (I.intercept e j)) →
        ∀ i, NumberBounds.OnGrid D (y i)) ∧
      (∀ C : ℚ, 0 ≤ C → (∀ e j, I.accepts e j → |I.intercept e j| ≤ C) →
        ∀ i, |y i| ≤ 2*((m+g+1:ℕ):ℚ)*C) ∧
      (OracleSpec.BitCode.deploy clearP).ComputesWithin oracle (lcmInputCode req)
        (3*clearP.bound.eval (lcmInputCode req).length+2*(lcmInputCode req).length+2)
        (fun hist bits => hist=[] ∧ bits=prodCode qlist qlist (List.ofFn y,packedCells f)) := by
  let out := TrialExecution.computeAtCommonWeightUnit I.positive L I.available I.intercept
  obtain ⟨hb,hm,hg,ha⟩ := computeWithDenominator_spec I.positive L I.available I.intercept
    (TrialExecution.weightDenominator L) (TrialExecution.weightDenominator_pos L) hL
    (TrialExecution.den_dvd_weightDenominator L)
  exact ⟨out.1,out.2,hb,hm,hg,ha,clear_deploy oracle I L⟩

end InitializeMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
