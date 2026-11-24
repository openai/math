import OAI.Computability.VPVNP.PairSimulationKernels
import OAI.Computability.VPVNP.PairSimulationPrivateLabels
import OAI.Computability.VPVNP.CompressionTemplates

/-!
# Work of a recorded map occurrence

At a shrink or refresh site, the descriptor records the number of repeated
base lookups as the map's degree. The fixed selector and base-entry tables
therefore give a bound in terms of that individual degree on every input,
including a syntactic zero. Successful lists additionally cost seven native
counter instructions per label and the loop's final test.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open Compression MotifGrid MotifBlocks MotifConversion MotifDemandPadding MotifSelector

universe u
variable {k : Type u} [Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')

/-- Complete arguments of a recorded template lookup, including arbitrary
incident coordinates in their declared half-wire widths. -/
structure EntryInput where
  /-- Number of input bits requested on each demand edge. -/
  demand : D → ℕ
  /-- Number of payload bits requested on each supply edge. -/
  payload : S → ℕ
  /-- Party at which the interpreter looks up the local tensor entry. -/
  party : J
  /-- Input coordinates on the demand half-wires incident to the party. -/
  demandBits : HalfBits a b demand party
  /-- Input coordinates on the supply half-wires at the template's computed widths. -/
  supplyBits : Half P (fun e ↦ Word (supplyWidths B demand payload e)) party

open scoped Classical in
/-- The actual metered template interpreter and the length of the native
label-counter prefix when the input is accepted. -/
noncomputable def EntryInput.work (hp : ∀ i, 0 < p i) (x : EntryInput B) : ℕ :=
  let res := runEntry B hp x.demand x.payload x.party
    (MotifEntry.demandBits a b x.party x.demandBits)
    (mapHalf P (fun _ ↦ MotifEntry.inputBits) x.supplyBits)
  res.2 + res.1.elim 0 (fun names ↦ 7 * names.length + 1)

/-- The constant depends only on the fixed template and precedes the input
widths, outer index, party and every supplied bit. -/
theorem entry_work_le_degree (hp : ∀ i, 0 < p i) :
    ∃ K : ℕ, ∀ x : EntryInput B, x.work B hp ≤ K * (repetitions B x.demand + 1) ^ 2 := by
  classical
  let A := ∑ z : B.grid.demands, ∑ i, baseDemand B z i
  let W := ∑ s : Selector B, ∑ e, basePayload B s e
  let K := Fintype.card S * (12 * B.selectorBits + 12 * W + 48) +
    Fintype.card D * (12 * A + 7) + 2 * (selectorTable B).length + 18
  have ha (z : B.grid.demands) (i : D) : baseDemand B z i ≤ A :=
    (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (baseDemand B z j)) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (fun z _ ↦ Nat.zero_le (∑ j, baseDemand B z j)) (Finset.mem_univ z))
  have hw (s : Selector B) (e : S) : basePayload B s e ≤ W :=
    (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (basePayload B s j)) (Finset.mem_univ e)).trans
      (Finset.single_le_sum (fun s _ ↦ Nat.zero_le (∑ j, basePayload B s j)) (Finset.mem_univ s))
  refine ⟨K + 8, fun x ↦ ?_⟩
  let z := demandGrid B hp x.demand
  let n := repetitions B x.demand
  let run := runEntry B hp x.demand x.payload x.party
    (MotifEntry.demandBits a b x.party x.demandBits)
    (mapHalf P (fun _ ↦ MotifEntry.inputBits) x.supplyBits)
  have hr : run.2 ≤ K * (n+1)^2 :=
    MotifEntry.run_le a b (baseDemand B z) _ P _ (lookup B z) _ _ _ _ _ _ (ha z) hw
  have hl : run.1.elim 0 (fun names ↦ 7 * names.length + 1) ≤ 7*n + 1 := by
    dsimp only [run]
    rw [runEntry_list]
    cases entry B hp x.demand x.payload x.party x.demandBits x.supplyBits <;> simp [n]
  change run.2 + _ ≤ _
  rw [Nat.add_mul]
  apply Nat.add_le_add hr
  exact hl.trans (by change 7*n+1 ≤ 8*(n+1)^2; nlinarith)

variable {T : BlockSchedule k}

/-- The two actual map interpreters at a block schedule's sites. The recorded
degree of a map bounds its base copies. A diagonal test can emit no labels. -/
inductive MapInvocation (F : T.Templates) (d : ℕ)
  | shrink (input : EntryInput F.shrink) (degree : repetitions F.shrink input.demand ≤ d)
  | refresh (input : EntryInput F.refresh) (degree : repetitions F.refresh input.demand ≤ d)
  | noLookup

/-- Interpreter and label-counter work of the selected lookup, or zero when no lookup runs. -/
noncomputable def MapInvocation.work {F : T.Templates} {d : ℕ} : MapInvocation F d → ℕ
  | .shrink x _ => x.work _ ShrinkMotif.demandMass_pos
  | .refresh x _ => x.work _ (fun _ ↦ zero_lt_one)
  | .noLookup => 0

/-- One constant controls both template tables at every level. -/
theorem mapInvocation_bound (F : T.Templates) :
    ∃ K : ℕ, ∀ d (m : MapInvocation F d), m.work ≤ K * (d + 1)^2 := by
  obtain ⟨A, hA⟩ := entry_work_le_degree F.shrink ShrinkMotif.demandMass_pos
  obtain ⟨B, hB⟩ := entry_work_le_degree F.refresh (fun _ ↦ zero_lt_one)
  refine ⟨max A B, fun d m ↦ ?_⟩
  cases m with
  | noLookup => exact Nat.zero_le _
  | shrink x hx =>
    exact (hA x).trans (Nat.mul_le_mul (le_max_left ..)
      (Nat.pow_le_pow_left (Nat.succ_le_succ hx) 2))
  | refresh x hx =>
    exact (hB x).trans (Nat.mul_le_mul (le_max_right ..)
      (Nat.pow_le_pow_left (Nat.succ_le_succ hx) 2))

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
