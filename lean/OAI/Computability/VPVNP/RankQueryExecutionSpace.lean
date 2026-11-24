import OAI.Computability.VPVNP.RankCursorMachine
import OAI.Computability.VPVNP.RankCursorSpaceLoop

/-! # Peak storage through a full rank scan

The Schur engine releases its traversal stack at every coefficient. The
outer scan reuses one scalar and a fixed register bank. Its space cap
depends on the cap of a single root query and on the short cursor-update
clock, independently of the number or total time of the root queries.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

open RAMTape BurstRAM Dispatch UniversalCountStack

variable {K : Type} [DecidableEq K] {n m w v e p b A B C : ℕ}
  [Fact p.Prime] [NeZero e] {c : SliceArithmetic.Vector p e}

/-- A root may take `B` instructions while its intermediate stacks fit `C` bits each. -/
def RootBoundedRead (query : FiniteRoutine (ScanPort K)) (Z w v n B C : ℕ)
    (value : ℕ → ℕ → Scalar c) (ready : Stacks K → Prop) : Prop :=
  ∀ (u z : ℕ), u ≤ n → z ≤ Z → ∀ (persist : Word w) (rs : Regs Registers.R w) aux,
    Registers.Stores rs Z u z → ready aux → ∃ k ≤ B, ∃ aux', ready aux' ∧
      query.BoundedRun C k (scanBank n persist rs [] (idle aux))
        (scanBank n persist rs [] (yielded aux' (Engine.scalar v (value u z))))

/-- Per-stack cap for the entire rank loop, taking the maximum of the root-query peak `C` and
the space for the returned scalar and cursor check above auxiliary height `A`. -/
def outerRankSpace (C A w v e : ℕ) := max C (A+w+e*v+1+checkClock w v e)

omit [DecidableEq K] in
private theorem readBank_length (n : ℕ) (persist : Word w) (rs : Regs Registers.R w) (aux : Stacks K)
    (haux : ∀ k, (aux k).length ≤ A) (bits flags : List Bool) (k : ScanPort K) :
    (scanBank n persist rs flags (yielded aux bits) [] k).length ≤ A+w+bits.length+flags.length := by
  cases k with
  | cursor j =>
    have h := Registers.bank_length persist rs flags j
    change (Registers.bank persist rs flags j).length ≤ _
    omega
  | engine j =>
    cases j with
    | frame f => cases f <;> exact Nat.zero_le _
    | aux i => exact (haux i).trans (by omega : A ≤ A+w+bits.length+flags.length)
    | result => change bits.length ≤ _; omega
    | condition => exact Nat.zero_le _
  | rows | depth => simp only [scanBank, length_digits]; omega
  | scratch => exact Nat.zero_le _

/-- Every intermediate stack through all coefficient requests fits the same
cap. In particular no part of the exponentially long rank loop is stored
as a list of instructions or scalar outputs. -/
theorem rankMachine_boundedRun [Fact (Irreducible (SliceArithmetic.modulus c))]
    (query : FiniteRoutine (ScanPort K)) (M : Matrix (Fin n) (Fin m) (Scalar c))
    (ready : Stacks K → Prop) (hcap : ∀ a, ready a → ∀ k, (a k).length ≤ A)
    (hq : RootBoundedRead query ((n+m)*n) w v n B C (SchurKey.compute (weightedGramEntryCoeff M)) ready)
    (hwidth : (b+1)*control.wordFactor ≤ w) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (hsize : max 1 (max n ((n+m)*n)) < 2^b)
    (persist : Word w) (initialRegs : Regs Registers.R w) (aux : Stacks K) (haux : ready aux)
    (hregs : Registers.Stores initialRegs ((n+m)*n) n ((n+m)*n)) :
    let Z := (n+m)*n
    ∃ k ≤ ((n+1)*(Z+1))*(B+checkClock w v e+1)+2, ∃ rs' aux',
      ready aux' ∧ Registers.Stores rs' Z (M.map (Scalar.interpretation c)).rank 0 ∧
      (rankMachine query).BoundedRun (outerRankSpace C A w v e) k
        (scanBank n persist initialRegs [true] (idle aux)) (scanBank n persist rs' [] (idle aux')) := by
  let Z := (n+m)*n
  let cap := outerRankSpace C A w v e
  let val := SchurKey.compute (weightedGramEntryCoeff M)
  let q (u z : ℕ) := decide (val u z = 0)
  let good (st : State) (s : Stacks (ScanPort K)) : Prop :=
    st.words 1 ≤ n ∧ st.words 2 ≤ Z ∧ ∃ rs a, ready a ∧ Registers.Stores rs Z (st.words 1) (st.words 2) ∧
      s = scanBank n persist rs [st.continues] (idle a)
  have flag (st : State) (s : Stacks (ScanPort K)) (hs : good st s) : s (.cursor .flag) = [st.continues] := by
    obtain ⟨_,_,_,_,_,_,rfl⟩ := hs; rfl
  have fits (st : State) (s : Stacks (ScanPort K)) (hs : good st s) (k : ScanPort K) : (s k).length ≤ cap := by
    obtain ⟨_,_,rs,a,ha,_,rfl⟩ := hs
    have h := readBank_length n persist rs a (hcap a ha) [] [st.continues] k
    simp only [List.length_nil, List.length_singleton, Nat.add_zero] at h
    apply h.trans
    dsimp only [cap, outerRankSpace]
    exact (by omega : A+w+1 ≤ A+w+e*v+1+checkClock w v e).trans (le_max_right ..)
  have one (u z : ℕ) (s : Stacks (ScanPort K)) (hs : good (.running u z) s) :
      ∃ k ≤ B+checkClock w v e, ∃ out, (query.followedBy check).BoundedRun cap k (Function.update s (.cursor .flag) []) out ∧
        good (step q Z (.running u z)) out := by
    obtain ⟨hu,hz,rs,a,ha,hreg,rfl⟩ := hs
    change u ≤ n at hu
    change z ≤ Z at hz
    obtain ⟨k, hk, a', ha', hread⟩ := hq u z hu hz persist rs a hreg ha
    have fit (i : Fin 8) : input Z u z (q u z) i < 2^b := by
      have hqv : (q u z).toNat ≤ 1 := by cases q u z <;> decide
      change max 1 (max n Z) < 2^b at hsize
      fin_cases i <;> simp [input] <;> omega
    obtain ⟨d, hd, rs', hcheck, hstore⟩ := check_runs hv n Z u z persist rs a' (val u z) hwidth fit hreg
    have hc := spaceRun_of_steps (cap := cap) hcheck (fun k => by
      have h := readBank_length n persist rs a' (hcap a' ha') (Engine.scalar v (val u z)) [] k
      rw [Engine.scalar_length, List.length_nil, Nat.add_zero] at h
      apply (Nat.add_le_add h hd).trans
      exact (by omega : A+w+e*v+checkClock w v e ≤ A+w+e*v+1+checkClock w v e).trans (le_max_right ..))
    rw [clear_flag]
    exact ⟨k+d, Nat.add_le_add hk hd, _, FiniteRoutine.BoundedRun.followedBy (a := query) (b := check) (hread.mono_cap (le_max_left ..)) hc,
      (advance_bounds Z n u z hu hz (q u z)).1, (advance_bounds Z n u z hu hz (q u z)).2,
      rs', a', ha', hstore, rfl⟩
  have init : good (.running n Z) (scanBank n persist initialRegs [true] (idle aux)) :=
    ⟨le_rfl,le_rfl,initialRegs,aux,haux,hregs,rfl⟩
  obtain ⟨k,hk,out,hout,hrun⟩ := scan_boundedRun (.cursor .flag) (query.followedBy check) q Z
    (B+checkClock w v e) cap good flag fits one _ _ init
  rw [show answer q Z (.running n Z) = (M.map (Scalar.interpretation c)).rank from initial_schur_answer M] at hout
  obtain ⟨_,_,outRegs,a,ha,hst,rfl⟩ := hout
  exact ⟨k, by simpa only [remaining, Nat.succ_mul, Nat.add_assoc] using hk,
    outRegs,a,ha,hst, by simpa only [rankMachine, clear_flag] using hrun⟩

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI
