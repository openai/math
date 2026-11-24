import OAI.Computability.VPVNP.RankCoordinatePrefix
import OAI.Computability.VPVNP.RankQueryStackRegister
import OAI.Computability.VPVNP.RegisterTable
import OAI.Computability.VPVNP.RoutineSpace

/-!
# Finite register routines for slice dimension and basis-index queries

The dimension in Appendix D is the difference between the rank of the full
matrix and the rank of its equation prefix. To locate a basis monomial, add the
prefix rank to its ordinal, scan the original matrix for that greedy row, then
remove the equation-row offset. The arithmetic runs on binary registers.
The rank and prefix scans are returning calls in the same physical stack bank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate

open Dispatch RAMTape UniversalCountStack BurstRAM

variable {K : Type} [DecidableEq K] {r width : ℕ}

/-- The binary ISA ports inside a larger bank. The other ports can hold the
caller's query or advice and have the same contents after register writeback. -/
structure RegisterBank (ports : ISA.Port r 0 → K) (bank : Regs r width → Stacks K)
    (persistent : Word width) : Prop where
  injective : Function.Injective ports
  inside (rs : Regs r width) (i : ISA.Port r 0) :
    bank rs (ports i) = ISA.bank Fin.elim0 persistent rs [] i
  outside (a b : Regs r width) (j : K) (hj : ∀ i, ports i ≠ j) :
    bank a j = bank b j

/-- Install a fixed instruction sequence at the caller's actual register ports. -/
def registerCall (ports : ISA.Port r 0 → K) (c : RegCode r) : FiniteRoutine K :=
  c.compile.onPorts ports

/-- Bound the cost of a binary-register program by its instruction count and the word-width
arithmetic cost. -/
def registerClock (width : ℕ) (c : RegCode r) : ℕ := c.length * (100*(width+1)^2)

theorem registerCall_runs {ports : ISA.Port r 0 → K} {bank : Regs r width → Stacks K}
    {persistent : Word width} (hb : RegisterBank ports bank persistent)
    (c : RegCode r) (rs : Regs r width) (cap : ℕ)
    (room : width + registerClock width c ≤ cap)
    (hout : ∀ j, (∀ i, ports i ≠ j) → (bank rs j).length ≤ cap) :
    ∃ t ≤ registerClock width c,
      (registerCall ports c).BoundedRun cap t (bank rs) (bank (c.exec rs)) := by
  obtain ⟨t, ht, hr⟩ := c.compile_runs Fin.elim0 persistent rs
  have hbr : c.compile.BoundedRun cap t (ISA.bank Fin.elim0 persistent rs [])
      (ISA.bank Fin.elim0 persistent (c.exec rs) []) := by
    apply spaceRun_of_steps hr
    exact fun i ↦ (Nat.add_le_add (RegisterTable.bank_length_le Fin.elim0 persistent rs i) ht).trans room
  have h := FiniteRoutine.BoundedRun.onPorts hb.injective (bank rs) hbr hout
  rw [installStacks_frame hb.injective (hb.inside rs) (fun _ _ ↦ rfl),
    installStacks_frame hb.injective (hb.inside (c.exec rs)) (hb.outside (c.exec rs) rs)] at h
  exact ⟨t, ht, h⟩

/-- A binary operation stages its two operands before changing the destination.
Both instructions of the subtraction implementation are covered by this bound. -/
def arithmeticClock (width : ℕ) : ℕ := 2 * (100*(width+1)^2)

/-- The caller provides the two matrix rank routines. Their selected result
registers remain available until the final subtraction. -/
def dimensionMachine (ports : ISA.Port r 0 → K) (equations full : FiniteRoutine K)
    (prefixRank fullRank dst : Fin r) : FiniteRoutine K :=
  (equations.followedBy full).followedBy (registerCall ports (.op dst .sub fullRank prefixRank))

variable {F : Type*} [Field F] [DecidableEq F] {w n m : ℕ}
variable {ports : ISA.Port r 0 → K} {bank : Regs r width → Stacks K} {persistent : Word width}
variable (W : Matrix (Fin w) (Fin m) F) (M : Matrix (Fin n) (Fin m) F)

/-- The two completed rank calls and the compiled word operation compute the
dimension. All other registers after the final operation equal their values
at the return of the full-rank call. -/
theorem dimensionMachine_runs (hb : RegisterBank ports bank persistent) (equations full : FiniteRoutine K) (prefixRank fullRank dst : Fin r)
    {cap a b : ℕ} {rs middle last : Regs r width}
    (he : equations.BoundedRun cap a (bank rs) (bank middle))
    (hf : full.BoundedRun cap b (bank middle) (bank last))
    (hp : (last prefixRank).val = rankQuery W)
    (ht : (last fullRank).val = rankQuery (appendRows W M))
    (room : width + arithmeticClock width ≤ cap) :
    ∃ t ≤ a+b+arithmeticClock width, ∃ out : Regs r width,
      (dimensionMachine ports equations full prefixRank fullRank dst).BoundedRun cap t (bank rs) (bank out) ∧
      (out dst).val = suffixDimension W M ∧ ∀ j ≠ dst, out j = last j := by
  let c : RegCode r := .op dst .sub fullRank prefixRank
  obtain ⟨t, hclock, h⟩ := registerCall_runs hb c last cap room (fun j _ ↦ hf.final_cap j)
  refine ⟨a+b+t, Nat.add_le_add_left hclock _, c.exec last, (he.followedBy hf).followedBy h, ?_, ?_⟩
  · have hs : Arith.sub.eval (last fullRank).val (last prefixRank).val < 2^width :=
      (Nat.sub_le ..).trans_lt (last fullRank).isLt
    simp only [c, RegCode.exec, Function.update_self, Arith.word_val _ _ _ hs, Arith.eval,
      hp, ht, suffixDimension]
    rfl
  · exact fun j hj ↦ Function.update_of_ne hj ..

/-- Ordinal of the same selected monomial among all independent rows. -/
def combinedOrdinal (i : Fin (suffixDimension W M)) : Fin (rankQuery (appendRows W M)) :=
  ⟨rankQuery W+i.val, by have := i.isLt; unfold suffixDimension at this; omega⟩

theorem suffixBasisIndex_val (i : Fin (suffixDimension W M)) :
    (suffixBasisIndex W M i).val = (greedyRowIndex (appendRows W M) (combinedOrdinal W M i)).val - w :=
  rfl

/-- The scan reads `offset` and returns the original zero-based row in `found`.
The prefix length lives in a register, so the same finite control serves every length. -/
def suffixMachine (ports : ISA.Port r 0 → K) (equations scan : FiniteRoutine K)
    (prefixRank ordinal offset found prefixRows dst : Fin r) : FiniteRoutine K :=
  let withOffset := equations.followedBy (registerCall ports (.op offset .add prefixRank ordinal))
  (withOffset.followedBy scan).followedBy (registerCall ports (.op dst .sub found prefixRows))

/-- Correctness for an actual returning prefix scan. Its row result is the
greedy index of the offset ordinal in the combined matrix. Rank and scan
scratch registers may change inside their calls. -/
theorem suffixMachine_runs (hb : RegisterBank ports bank persistent) (equations scan : FiniteRoutine K)
    (prefixRank ordinal offset found prefixRows dst : Fin r) (i : Fin (suffixDimension W M))
    {cap a B : ℕ} {rs middle : Regs r width}
    (he : equations.BoundedRun cap a (bank rs) (bank middle))
    (hp : (middle prefixRank).val = rankQuery W) (hi : (middle ordinal).val = i.val)
    (fits : (combinedOrdinal W M i).val < 2^width)
    (room : width + arithmeticClock width ≤ cap)
    (hscan : let before := (RegCode.op offset .add prefixRank ordinal).exec middle
      (before offset).val = (combinedOrdinal W M i).val → ∃ b ≤ B, ∃ after : Regs r width,
        scan.BoundedRun cap b (bank before) (bank after) ∧
        (after found).val = (greedyRowIndex (appendRows W M) (combinedOrdinal W M i)).val ∧
        (after prefixRows).val = w) :
    ∃ t ≤ a+arithmeticClock width+B+arithmeticClock width, ∃ out : Regs r width,
      (suffixMachine ports equations scan prefixRank ordinal offset found prefixRows dst).BoundedRun
        cap t (bank rs) (bank out) ∧ (out dst).val = (suffixBasisIndex W M i).val := by
  let add : RegCode r := .op offset .add prefixRank ordinal
  obtain ⟨s, hs, ha⟩ := registerCall_runs hb add middle cap room (fun j _ ↦ he.final_cap j)
  have haFit : Arith.add.eval (middle prefixRank).val (middle ordinal).val < 2^width := by
    change (middle prefixRank).val + (middle ordinal).val < 2^width
    rw [hp, hi]
    exact fits
  have hval : (add.exec middle offset).val = (combinedOrdinal W M i).val := by
    simp only [add, RegCode.exec, Function.update_self, Arith.word_val _ _ _ haFit, Arith.eval,
      hp, hi, combinedOrdinal]
    rfl
  obtain ⟨b, hB, after, hcall, hfound, hrows⟩ := hscan hval
  let sub : RegCode r := .op dst .sub found prefixRows
  obtain ⟨u, hu, hsub⟩ := registerCall_runs hb sub after cap room (fun j _ ↦ hcall.final_cap j)
  have hs' : s ≤ arithmeticClock width := hs
  have hu' : u ≤ arithmeticClock width := hu
  refine ⟨a+s+b+u, by omega, sub.exec after, ((he.followedBy ha).followedBy hcall).followedBy hsub, ?_⟩
  have hsubFit : Arith.sub.eval (after found).val (after prefixRows).val < 2^width :=
    (Nat.sub_le ..).trans_lt (after found).isLt
  simp only [sub, RegCode.exec, Function.update_self, Arith.word_val _ _ _ hsubFit, Arith.eval,
    hfound, hrows, suffixBasisIndex_val]
  rfl

/-- Instantiate the suffix query with the finite prefix-scan controller. The
test and increment subroutines run on the current candidate. No call to select
an earlier basis index occurs in the scan. -/
theorem suffixGreedy_runs (hb : RegisterBank ports bank persistent)
    (equations test bump : FiniteRoutine K) (flag : K)
    (prefixRank ordinal offset found prefixSize dst : Fin r) (i : Fin (suffixDimension W M))
    {cap a T B : ℕ} {rs middle : Regs r width}
    (he : equations.BoundedRun cap a (bank rs) (bank middle))
    (hp : (middle prefixRank).val = rankQuery W) (hi : (middle ordinal).val = i.val)
    (fits : (combinedOrdinal W M i).val < 2^width)
    (room : width + arithmeticClock width ≤ cap)
    (input checked : ℕ → Regs r width)
    (start : input 0 = (RegCode.op offset .add prefixRank ordinal).exec middle)
    (hflag : ∀ j < w+n, bank (checked j) flag = [])
    (htest : ∀ j (hj : j < w+n), ∃ t ≤ T, test.BoundedRun cap t (bank (input j))
      (Function.update (bank (checked j)) flag [decide ((input 0 offset).val <
        rankQuery (prefixRows (appendRows W M) (j+1) hj))]))
    (hbump : ∀ j, j+1 < w+n → ∃ t ≤ B, bump.BoundedRun cap t (bank (checked j)) (bank (input (j+1))))
    (hcursor : ∀ j < w+n, (checked j found).val = j ∧ (checked j prefixSize).val = w) :
    ∃ t ≤ a+arithmeticClock width+(w+n)*(T+1+B)+arithmeticClock width, ∃ out : Regs r width,
      (suffixMachine ports equations (greedyPrefix flag test bump)
        prefixRank ordinal offset found prefixSize dst).BoundedRun cap t (bank rs) (bank out) ∧
      (out dst).val = (suffixBasisIndex W M i).val := by
  apply suffixMachine_runs W M hb equations (greedyPrefix flag test bump) _ _ _ _ _ _ i
    he hp hi fits room
  dsimp only
  intro hOrdinal
  have hO : (input 0 offset).val = (combinedOrdinal W M i).val := start ▸ hOrdinal
  obtain ⟨b, hbnd, hscan⟩ := greedyPrefix_runs (appendRows W M) (combinedOrdinal W M i)
    flag test bump (bank ∘ input) (bank ∘ checked) hflag (by
      intro j hj
      simpa only [Function.comp_apply, ← hO] using htest j hj) hbump
  let j := greedyRowIndex (appendRows W M) (combinedOrdinal W M i)
  exact ⟨b, hbnd, checked j.val, start ▸ hscan, hcursor j.val j.isLt⟩

end RankQuery.Stack.Coordinate

end VPVNP
end Computability
end OAI
