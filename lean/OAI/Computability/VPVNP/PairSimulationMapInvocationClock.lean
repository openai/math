import OAI.Computability.VPVNP.PairSimulationMapInline

/-!
# Uniform clocks for the actual shrink and refresh map code

Each grid row and party uses a fixed allocation of registers, public constants
and instructions. The descriptor and private fields vary with the selected
vertex. Both catalogue ordinals share the enclosing histogram.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapInline

open MotifSelector MotifGrid MotifBlocks MotifConversion
open MapCallTable LocalHistory
open scoped Fin.CommRing

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  (B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H') {t : ℕ}

/-- A concrete descriptor and register layout for each member of the fixed family. -/
noncomputable def layout (z : B.grid.demands) (j : J) :=
  MapCallTable.allocate B z j (MapEntryTable.allocation B z j)
    (Fintype.equivFin _) (Fintype.equivFin _)

variable (ordinal : (parameterData B).Entry → Fin t)

/-- The instruction bound of the fixed, physically lowered layout at a given copy count. -/
noncomputable def cap (z : B.grid.demands) (j : J) (u : ℕ) : ℕ :=
  let L := layout B z j
  factor L ordinal * (L.lines.length +
    (1 + 3 * (MapPortAgreement.ports G j L.core.edgeOrder).length) + MapNativeClock.cap B z j u)

theorem cap_uniform : ∃ C : ℕ, ∀ z j u, cap B ordinal z j u ≤ C * (u + 1) :=
  uniform ordinal (layout B)

/-- All numerical table entries fit exactly in every sufficiently wide host word,
simultaneously over all parties and grid points. -/
theorem eventually_exact :
    ∀ᶠ w : ℕ in Filter.atTop, ∀ z j i,
      ((MapConstants.rawBank (layout B z j).core ordinal i : BurstRAM.Word w)).val =
        MapConstants.rawBank (layout B z j).core ordinal i := by
  let bank := fun z j ↦ MapConstants.rawBank (layout B z j).core ordinal
  let bound := ∑ z : B.grid.demands, ∑ j, ∑ i, bank z j i
  filter_upwards [Filter.eventually_ge_atTop bound] with w hw
  intro z j i
  have hi := Finset.single_le_sum (fun a _ ↦ Nat.zero_le (bank z j a)) (Finset.mem_univ i)
  have hj := Finset.single_le_sum (fun b _ ↦ Nat.zero_le (∑ a, bank z b a)) (Finset.mem_univ j)
  have hz := Finset.single_le_sum (fun c _ ↦ Nat.zero_le (∑ b, ∑ a, bank c b a)) (Finset.mem_univ z)
  exact Nat.mod_eq_of_lt ((((hi.trans hj).trans hz).trans hw).trans_lt Nat.lt_two_pow_self)

/-- Initialization and literal expansion cost a fixed factor relative to the
five-phase map clock, including a possibly empty row. -/
theorem cap_relative :
    ∃ C : ℕ, ∀ z j u, cap B ordinal z j u ≤ C * (MapNativeClock.cap B z j u + 1) := by
  let start := fun z j ↦ (layout B z j).lines.length +
    (1 + 3 * (MapPortAgreement.ports G j (layout B z j).core.edgeOrder).length)
  let weight := fun z j ↦ factor (layout B z j) ordinal * (start z j + 1)
  refine ⟨∑ z : B.grid.demands, ∑ j, weight z j, fun z j u ↦ ?_⟩
  have hweight := (Finset.single_le_sum (fun i _ ↦ Nat.zero_le (weight z i))
    (Finset.mem_univ j)).trans (Finset.single_le_sum (fun a _ ↦ Nat.zero_le (∑ i, weight a i))
      (Finset.mem_univ z))
  let n := MapNativeClock.cap B z j u
  calc
    _ ≤ factor (layout B z j) ordinal * ((start z j + 1) * (n + 1)) := by
      apply Nat.mul_le_mul_left
      change start z j + n ≤ _
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
      omega
    _ = weight z j * (n + 1) := (Nat.mul_assoc ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hweight

open Compression

variable {S : BlockSchedule K} (T : S.Templates) (ord : T.Entry → Fin t)

open scoped Classical in
/-- The clock of the actual map call selected by the compressor. -/
noncomputable def invocationCap {d : ℕ} : MapInvocation T d → ℕ
  | .shrink x _ => cap T.shrink (ord ∘ Sum.inl)
      (demandGrid T.shrink ShrinkMotif.demandMass_pos x.demand) x.party
      (repetitions T.shrink x.demand)
  | .refresh x _ => cap T.refresh (ord ∘ Sum.inr)
      (demandGrid T.refresh (fun _ ↦ zero_lt_one) x.demand) x.party (repetitions T.refresh x.demand)
  | .noLookup => 0

/-- One linear bound includes every initializer, inlined table constant and local
histogram increment across both map templates. -/
theorem invocation_uniform :
    ∃ C : ℕ, ∀ d (m : MapInvocation T d), invocationCap T ord m ≤ C * (d + 1) := by
  classical
  obtain ⟨A, hA⟩ := cap_uniform T.shrink (ord ∘ Sum.inl)
  obtain ⟨A', hA'⟩ := cap_uniform T.refresh (ord ∘ Sum.inr)
  refine ⟨max A A', fun d m ↦ ?_⟩
  cases m with
  | shrink x hx => exact (hA ..).trans (Nat.mul_le_mul (le_max_left ..) (Nat.succ_le_succ hx))
  | refresh x hx => exact (hA' ..).trans (Nat.mul_le_mul (le_max_right ..) (Nat.succ_le_succ hx))
  | noLookup => exact Nat.zero_le _

/-- This is the constant used by the selected-vertex clock on the concrete lowered map. -/
theorem invocation_relative :
    ∃ A : ℕ, ∀ d (m : MapInvocation T d), invocationCap T ord m ≤
      (A + 1) * (m.nativeCap T + 1) := by
  classical
  obtain ⟨A, hA⟩ := cap_relative T.shrink (ord ∘ Sum.inl)
  obtain ⟨A', hA'⟩ := cap_relative T.refresh (ord ∘ Sum.inr)
  refine ⟨max A A', fun d m ↦ ?_⟩
  cases m with
  | shrink x _ =>
    exact (hA ..).trans (Nat.mul_le_mul_right _ ((le_max_left ..).trans (Nat.le_succ _)))
  | refresh x _ =>
    exact (hA' ..).trans (Nat.mul_le_mul_right _ ((le_max_right ..).trans (Nat.le_succ _)))
  | noLookup => exact Nat.zero_le _

end PairSimulation.MapInline

end VPVNP
end Computability
end OAI
