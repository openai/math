import OAI.Computability.BorderVNP.DiagonalNativeSignedWindow
import OAI.Computability.BorderVNP.DiagonalJointCellProducts

/-! # Joint weighted preparations of the real positive signed evaluator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction CellDispatch CompactMachine CellMacro.Generator BorderVNP.Cube

open scoped BigOperators Classical

variable {dim box lanes selectors symbols w : ℕ} (id : TableEntry dim box lanes selectors symbols → ℕ)
    (gen : Fragment IO) (n : ℕ)

/-- Concrete returning state after the packet boot on a team of the
positive branch, with the private-call and total budgets on that state. -/
structure PositiveTeam (w : ℕ) where
  /-- Public word registers fixed in the genuine processor header. -/
  pub : Arg → Word w
  /-- The fixed private routine table; slot zero executes the cell generator. -/
  routines : TeamOpcode.Macros w 8
  /-- Post-boot register file and the physically initialized shared memory. -/
  bank : Bank w
  /-- Shared memory at entry to the positive branch. -/
  memory : Memory w
  /-- Number of independent substituted bits on this team (zero off the lead team). -/
  guessWidth : ℕ
  /-- All and only genuine returns from the signed machine's pin preparation. -/
  pins : (Fin guessWidth → Bool) ≃ Pins.Return pub (install gen n routines) bank memory
  /-- Ticks already charged by the actual startup. -/
  used : ℕ
  /-- Initial native cutoff from the physical packet. -/
  limit : ℕ
  /-- Native burst allowance. -/
  burst : ℕ
  /-- Room for each actual bounded cell burst. -/
  burstFit : TeamScales.width n (1/2) ≤ burst
  /-- Addressability of the native cell-dispatch prefix. -/
  frameFit : (pub 0).val+15 < 2^w
  /-- Directory extent for every returning preparation. -/
  room : ∀ b (p : SignedPreps id pub routines gen n bank memory pins b),
    let f := Frame.ofMemory pub p.val.2.2
    f.base+3*f.count ≤ 2^w
  /-- Physically addressed sparse cell inputs and their genuine generator receipts. -/
  cells : ∀ b (p : SignedPreps id pub routines gen n bank memory pins b),
    GeneratedCells gen n pub p.val.2.2
  /-- Bounds for the actual preparation, private calls, deterministic tally and residue reader. -/
  window : SignedStageWindow id pub routines gen n bank memory pins used limit

namespace PositiveTeam

variable {id gen n} (S : PositiveTeam id gen n w)

/-- The substituted local pin guess and actual physical preparation return. -/
abbrev Prefix := Σ b : Fin S.guessWidth → Bool,
  SignedPreps id S.pub S.routines gen n S.bank S.memory S.pins b

/-- Finiteness follows from the charged public-stage runs, also on rejected
continuations, so the sum retains the whole true prefix domain. -/
noncomputable instance prefixFinite : Fintype S.Prefix := by
  letI (b : Fin S.guessWidth → Bool) := @Fintype.ofFinite _ (S.window.preparationFinite id S.pub S.routines
    gen n S.bank S.memory S.pins b)
  unfold Prefix
  infer_instance

/-- Memory produced by this actual prefix, including its materialized cell directory. -/
abbrev postMemory (p : S.Prefix) := p.2.val.2.2

/-- Genuine sparse private input contract for that preparation's own frame. -/
noncomputable abbrev generated (p : S.Prefix) := S.cells p.1 p.2

/-- Signed contribution of the exact native events preceding the private call. -/
def prefixWeight (p : S.Prefix) := pathWeight p.2.val.1

private theorem native_positive (c : Code) (native : c.nativeOnly = true) : c.positive = true := by
  induction c <;> simp_all [Code.nativeOnly,Code.positive,Bool.and_eq_true]

/-- The true preparation uses only ordinary bit choices and unsigned RAM
operations, so its entire chronological prefix contributes one. -/
theorem prefixWeight_one (p : S.Prefix) : S.prefixWeight p = 1 := by
  apply List.prod_eq_one
  intro v hv
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
  change TeamRAM.Sign.value a.sign = 1
  rw [(p.2.property.positive (native_positive _ (signedPrepare_nativeOnly id))) a ha]
  rfl

/-- Actual deterministic subtotal check followed by the lead-team matrix
entry count, or the other team's unit check. -/
noncomputable def readerWeight (p : S.Prefix) :=
  let mac := install gen n S.routines
  tallyValue S.pub mac (cellBank S.pub mac p.2.val.2.1 p.2.val.2.2) p.2.val.2.2
    signedOccurrences signedOccurrences_deterministic

/-- The bounded positive body factors through its actual local prefix,
independent owned cell calls and deterministic subtotal continuation. -/
theorem local_sum (hn : 1 ≤ n) :
    boundedValue (signedBody id) S.pub (install gen n S.routines) S.bank S.memory
      (S.limit-S.used) S.burst (n^25) =
      ∑ p : S.Prefix, S.prefixWeight p * ((S.generated p).product * S.readerWeight p) := by
  let (b : Fin S.guessWidth → Bool) := @Fintype.ofFinite _ (S.window.preparationFinite id S.pub S.routines
    gen n S.bank S.memory S.pins b)
  have source := signedBody_bounded_product id S.pub S.routines gen n S.bank S.memory S.pins S.window hn S.burst
    S.burstFit S.frameFit S.room S.cells
  refine source.trans ?_
  exact (Fintype.sum_sigma (fun p : S.Prefix => S.prefixWeight p * ((S.generated p).product * S.readerWeight p))).symm

end PositiveTeam

/-- Complete product on all agreeing positive-branch teams. The remaining
indices are true joint native prefixes and one independently guessed private
bit vector per actually owned cell. -/
theorem joint_positive_program {teams : ℕ} (hn : 1 ≤ n) (S : Fin teams → PositiveTeam id gen n w)
    (joint : ∀ a : (u : Fin teams) → (S u).Prefix,
      JoinedCells (fun u => (S u).pub) (fun u => (S u).postMemory) (fun u => (S u).generated) a) :
    (∏ u, boundedValue (signedBody id) (S u).pub (install gen n (S u).routines)
      (S u).bank (S u).memory ((S u).limit-(S u).used) (S u).burst (n^25)) =
      ∑ a : (u : Fin teams) → (S u).Prefix, ∑ z : (joint a).Private,
        (∏ u, (S u).prefixWeight (a u)) * (joint a).privateWeight z * (∏ u, (S u).readerWeight (a u)) := by
  refine (Finset.prod_congr rfl fun u _ => (S u).local_sum hn).trans ?_
  exact joint_private_sum (fun u => (S u).pub) (fun u => (S u).postMemory) (fun u => (S u).generated)
    (fun u => (S u).prefixWeight) (fun u => (S u).readerWeight) joint

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
