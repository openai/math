import OAI.Computability.VPVNP.RankCursorCheck
import OAI.Computability.VPVNP.RankQueryStackInterpretation

/-! # Executing the outer rank scan

Each request returns one scalar Schur coefficient, the zero test selects
the cursor update, and the updated registers give the next request or the
rank. Only the current field element and binary degree pair survive a step.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

open RAMTape BurstRAM Dispatch

variable {K : Type} [DecidableEq K] {w v b p e n m : ℕ}
variable [Fact p.Prime] [NeZero e] {c : SliceArithmetic.Vector p e}

/-- The control, including its loop, is independent of every size parameter. -/
def rankMachine (query : FiniteRoutine (ScanPort K)) : FiniteRoutine (ScanPort K) :=
  scan (.cursor .flag) (query.followedBy check)

theorem initial_schur_answer [Fact (Irreducible (SliceArithmetic.modulus c))]
    (M : Matrix (Fin n) (Fin m) (Scalar c)) :
    let Z := (n+m)*n
    answer (fun u z => decide (SchurKey.compute (weightedGramEntryCoeff M) u z = 0))
      Z (.running n Z) = (M.map (Scalar.interpretation c)).rank := by
  let Z := (n+m)*n
  let q (u z : ℕ) := decide (SchurKey.compute (weightedGramEntryCoeff M) u z = 0)
  change max (below q Z n) (row q n (Z+1)) = _
  rw [below, ← peak_succ (fun u => row q u (Z+1)) n, ← Scalar.rank_correct c M]
  simp [SchurKey.computeRank, scanRank, peak, row, q, Z]

/-- The root-query contract uses the actual binary indices, field scalar
encoding and live auxiliary matrix bank. -/
def RootRead (query : FiniteRoutine (ScanPort K)) (Z w v n B : ℕ)
    (value : ℕ → ℕ → Scalar c) (ready : Stacks K → Prop) : Prop :=
  ∀ (u z : ℕ), u ≤ n → z ≤ Z → ∀ (persist : Word w) (rs : Regs Registers.R w) aux,
    Registers.Stores rs Z u z → ready aux →
    ∃ k ≤ B, ∃ aux', ready aux' ∧ query.Runs k (scanBank n persist rs [] (idle aux))
      (scanBank n persist rs [] (yielded aux' (Engine.scalar v (value u z))))

theorem advance_bounds (Z n u z : ℕ) (hu : u ≤ n) (hz : z ≤ Z) (zero : Bool) :
    (advance Z u z zero).words 1 ≤ n ∧ (advance Z u z zero).words 2 ≤ Z := by
  cases zero <;> by_cases h₁ : u=0 <;> by_cases h₂ : z=0 <;>
    simp [advance, State.words, h₁, h₂] <;> omega

theorem clear_flag (n : ℕ) (persist : Word w) (rs : Regs Registers.R w) (aux : Stacks K) (bit : Bool) :
    Function.update (scanBank n persist rs [bit] (idle aux)) (.cursor .flag) [] =
      scanBank n persist rs [] (idle aux) := by
  funext k
  cases k with | cursor k => cases k <;> rfl | _ => rfl

/-- The physical run returns the rank in cursor register one. The input field
is the irreducible polynomial-basis extension in which the matrix was encoded. -/
theorem rankMachine_runs [Fact (Irreducible (SliceArithmetic.modulus c))]
    (query : FiniteRoutine (ScanPort K)) (M : Matrix (Fin n) (Fin m) (Scalar c))
    (ready : Stacks K → Prop) (B : ℕ)
    (hq : RootRead query ((n+m)*n) w v n B (SchurKey.compute (weightedGramEntryCoeff M)) ready)
    (hwidth : (b+1)*control.wordFactor ≤ w) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (hsize : max 1 (max n ((n+m)*n)) < 2^b)
    (persist : Word w) (initialRegs : Regs Registers.R w) (aux : Stacks K) (haux : ready aux)
    (hregs : Registers.Stores initialRegs ((n+m)*n) n ((n+m)*n)) :
    let Z := (n+m)*n
    ∃ k ≤ ((n+1)*(Z+1))*(B+checkClock w v e+1)+2, ∃ rs' aux',
      ready aux' ∧ Registers.Stores rs' Z (M.map (Scalar.interpretation c)).rank 0 ∧
      (rankMachine query).Runs k (scanBank n persist initialRegs [true] (idle aux))
        (scanBank n persist rs' [] (idle aux')) := by
  let Z := (n+m)*n
  let val := SchurKey.compute (weightedGramEntryCoeff M)
  let q (u z : ℕ) := decide (val u z = 0)
  let good (st : State) (s : Stacks (ScanPort K)) : Prop :=
    st.words 1 ≤ n ∧ st.words 2 ≤ Z ∧ ∃ rs a, ready a ∧ Registers.Stores rs Z (st.words 1) (st.words 2) ∧
      s = scanBank n persist rs [st.continues] (idle a)
  have flag (st : State) (s : Stacks (ScanPort K)) (hs : good st s) : s (.cursor .flag) = [st.continues] := by
    obtain ⟨_,_,_,_,_,_,rfl⟩ := hs
    rfl
  have one (u z : ℕ) (s : Stacks (ScanPort K)) (hs : good (.running u z) s) :
      ∃ k ≤ B+checkClock w v e, ∃ out,
        (query.followedBy check).Runs k (Function.update s (.cursor .flag) []) out ∧ good (step q Z (.running u z)) out := by
    obtain ⟨hu,hz,rs,a,ha,hreg,rfl⟩ := hs
    change u ≤ n at hu
    change z ≤ Z at hz
    obtain ⟨k, hk, a', ha', hread⟩ := hq u z hu hz persist rs a hreg ha
    have fit (i : Fin 8) : input Z u z (q u z) i < 2^b := by
      have hqv : (q u z).toNat ≤ 1 := by cases q u z <;> decide
      change max 1 (max n Z) < 2^b at hsize
      fin_cases i <;> simp [input] <;> omega
    obtain ⟨d, hd, rs', hcheck, hstore⟩ := check_runs hv n Z u z persist rs a' (val u z)
      hwidth fit hreg
    rw [clear_flag]
    exact ⟨k+d, Nat.add_le_add hk hd, _, hread.followedBy hcheck,
      (advance_bounds Z n u z hu hz (q u z)).1, (advance_bounds Z n u z hu hz (q u z)).2,
      rs', a', ha', hstore, rfl⟩
  have init : good (.running n Z) (scanBank n persist initialRegs [true] (idle aux)) :=
    ⟨le_rfl,le_rfl,initialRegs,aux,haux,hregs,rfl⟩
  obtain ⟨k, hk, out, hout, hrun⟩ := scan_runs (.cursor .flag) (query.followedBy check) q Z
    (B+checkClock w v e) good flag one _ _ init
  have hrank : answer q Z (.running n Z) = (M.map (Scalar.interpretation c)).rank := initial_schur_answer M
  rw [hrank] at hout
  obtain ⟨_,_,outRegs,a,ha,hst,rfl⟩ := hout
  refine ⟨k, ?_, outRegs,a,ha,hst, ?_⟩
  · simpa only [remaining, Nat.succ_mul, Nat.add_assoc] using hk
  · simpa only [rankMachine, clear_flag] using hrun

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI
