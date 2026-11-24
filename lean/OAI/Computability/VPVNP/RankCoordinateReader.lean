import OAI.Computability.VPVNP.EvaluatorReadInterface
import OAI.Computability.VPVNP.RoutineSpace

/-! # Installing a scalar coordinate query in the weighted evaluator

The reader uses the live little-endian basis ordinals and the unary label without
copying. Its returned scalar is already on the next field multiplier's operand
port. The caller's product, field coefficients and remaining index registers are
outside the installed bank and survive every step of the query.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.Reader

open RAMTape UniversalCountStack Evaluator Evaluator.MatrixCallbacks SliceArithmetic

/-- Public input and scalar output ports of the coordinate reader together with its auxiliary
stack labels. -/
inductive Port (P : Type) where
  | label | current | next | result | aux (k : P)
  deriving DecidableEq, Fintype

variable {P : Type}

/-- Wire the coordinate callback into the weighted evaluator's label, ordinal,
arithmetic-result, and auxiliary ports. -/
def mount : Port P → ReadPort P
  | .label => .inl ()
  | .current => .inr (.indices .current)
  | .next => .inr (.indices .next)
  | .result => .inr (.arithmetic (.inr .query))
  | .aux k => .inr (.aux k)

theorem mount_injective : Function.Injective (mount (P := P)) := by
  intro x y eq
  cases x <;> cases y <;> simp_all [mount]

/-- Assemble the label, current and next basis indices, result bits, and auxiliary stacks as a
reader configuration. -/
def bank (label current next result : List Bool) (extra : Stacks P) : Stacks (Port P)
  | .label => label | .current => current | .next => next | .result => result | .aux k => extra k

/-- Install the coordinate reader on the weighted evaluator's physical ports. -/
def install (core : FiniteRoutine (Port P)) : FiniteRoutine (ReadPort P) := core.onPorts mount

variable [DecidableEq P] {p e w v : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Algebra (ZMod p) F] {c : Vector p e}
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F) (dim : BurstRAM.Word v) (extra : Stacks P)

/-- Encode the zero-based basis index, without changing its value, as a
least-significant-bit-first word of the evaluator’s index width. -/
abbrev ordinal (j : Fin dim.val) := BurstRAM.wordBits (Fin.castLE dim.isLt.le j : BurstRAM.Word v)

/-- A returning native scalar query suffices for the evaluator's exact reader
contract. Current and next are in transition order, so a column-vector matrix is
queried at the transpose position. -/
theorem readsEntry (core : FiniteRoutine (Port P)) (matrix : Matrix (Fin dim.val) (Fin dim.val) F)
    (label time : ℕ) (query : ∀ i j : Fin dim.val, ∃ d ≤ time, core.Runs d
      (bank (List.replicate label true) (ordinal dim i) (ordinal dim j) [] extra)
      (bank (List.replicate label true) (ordinal dim i) (ordinal dim j) (WeightedStep.bits φ w (matrix i j)) extra)) :
    ReadsEntry φ dim extra (install core) w label time matrix := by
  intro s j
  obtain ⟨d, hd, run⟩ := query s.1 j
  refine ⟨d, hd, FiniteRoutine.runs_onPorts_framed core mount_injective run ?_ ?_ ?_⟩
  · intro a; cases a <;> rfl
  · intro a; cases a <;> rfl
  · intro a outside
    cases a with
    | inl => rfl
    | inr a =>
      cases a with
      | indices | width | aux => rfl
      | arithmetic a =>
        cases a with
        | inl => rfl
        | inr a =>
          cases a with
          | query => exact (outside .result rfl).elim
          | prime | zeroWord | degree | coeff | acc => rfl

/-- The physical core may leave its finite scratch bank occupied. A fixed
cleanup pass discharges those ports while retaining advice and output. -/
noncomputable def reclaim {A H : Type} [Fintype H] : FiniteRoutine (Port (A ⊕ H)) :=
  CallClear.cleanup (Finset.univ.toList.map (fun h : H ↦ Port.aux (Sum.inr h)))

theorem reclaim_runs {A H : Type} [Fintype H] [DecidableEq A] [DecidableEq H]
    (label current next result : List Bool) (advice : Stacks A) (work : Stacks H) (cap : ℕ)
    (fits : ∀ h, (work h).length ≤ cap) :
    ∃ t ≤ Fintype.card H * (cap+1)+1, reclaim.Runs t
      (bank label current next result (Sum.elim advice work))
      (bank label current next result (Sum.elim advice (fun _ : H ↦ []))) := by
  let ks := Finset.univ.toList.map (fun h : H ↦ Port.aux (Sum.inr h : A ⊕ H))
  let s := bank label current next result (Sum.elim advice work)
  have hlen : ks.length = Fintype.card H := by simp [ks]
  obtain ⟨t, ht, h⟩ := CallClear.cleanup_runs ks s cap (fun k hk ↦ by
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp hk
    exact fits h)
  have endBank : CallClear.erased ks s = bank label current next result (Sum.elim advice (fun _ : H ↦ [])) := by
    funext k
    cases k with
    | label | current | next | result => simp [CallClear.erased, ks, s, bank]
    | aux a => cases a <;> simp [CallClear.erased, ks, s, bank]
  exact ⟨t, hlen ▸ ht, endBank ▸ h⟩

end RankQuery.Stack.Coordinate.Reader

end VPVNP
end Computability
end OAI
