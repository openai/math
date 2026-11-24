import OAI.Computability.VPVNP.RankCoordinatePreparePorts

/-!
# Static advice for the Cramer coordinate reader

Each slice supplies the two determinant roots, the greedy selector, the equation
rank and row count, and one scale for each operation. Live basis indices and
the label are supplied by the caller. All private work stacks start empty.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.FullAdvice

open RAMTape UniversalCountStack SliceArithmetic

variable {D K T : Type} {p e : ℕ}

/-- The persistent image shared by the label and Frobenius readers. -/
def advice (c : Vector p e) (r addr width rankW eqRows : ℕ) (den : Stacks D)
    (num : Stacks (ArgumentStage.Num K)) (side : Stacks T) (powers : Bool → ℕ) :
    Stacks (Prepare.Advice D K T) :=
  Prepare.advice (RootInit.template c r addr width den num)
    (Dynamic.bank side (Dynamic.regs (w := addr) 0 0 rankW eqRows 0 0 0 0))
    (UnaryWord.store [] [] (digits addr 0) [] []) (fun b ↦ digits addr (powers b))

/-- Advice and initially empty work stacks, mounted on the evaluator's extra ports. -/
def extra (c : Vector p e) (r addr width rankW eqRows : ℕ) (den : Stacks D)
    (num : Stacks (ArgumentStage.Num K)) (side : Stacks T) (powers : Bool → ℕ) :
    Stacks (Prepare.Advice D K T ⊕ Prepare.Work D K T) :=
  Sum.elim (advice c r addr width rankW eqRows den num side powers) (fun _ ↦ [])

/-- Width of the largest advised stack, including the two nested readers and
the selector's side bank. -/
def portBound (addr width e readerBound sideBound : ℕ) :=
  max (RootInit.templateCap addr width e readerBound) (max addr sideBound)

variable [Fact p.Prime]
variable (c : Vector p e) (r addr width rankW eqRows : ℕ) (den : Stacks D)
  (num : Stacks (ArgumentStage.Num K)) (side : Stacks T) (powers : Bool → ℕ)
  (readerBound sideBound : ℕ) (hr : r < 2^addr) (hw : Word.workingWidth p ≤ width)
  (hd : ∀ i, (den i).length ≤ readerBound) (hn : ∀ i, (num i).length ≤ readerBound)
  (hs : ∀ i, (side i).length ≤ sideBound)

include hr hw hd hn hs

theorem advice_length (i : Prepare.Advice D K T) :
    (advice c r addr width rankW eqRows den num side powers i).length ≤
      portBound addr width e readerBound sideBound := by
  have addr_le : addr ≤ portBound addr width e readerBound sideBound :=
    (le_max_left addr sideBound).trans (le_max_right ..)
  rcases i with (j | (j | j) | j) | b
  · exact (RootInit.template_length c r addr width readerBound hr hw den num hd hn j).trans
      (le_max_left ..)
  · exact (RegisterTable.bank_length_le Fin.elim0 0 _ j).trans addr_le
  · exact (hs j).trans ((le_max_right addr sideBound).trans (le_max_right ..))
  · cases j <;> simp [advice, Prepare.advice, UnaryWord.store, addr_le]
  · simpa [advice, Prepare.advice] using addr_le

theorem extra_length (i : Prepare.Advice D K T ⊕ Prepare.Work D K T) :
    (extra c r addr width rankW eqRows den num side powers i).length ≤
      portBound addr width e readerBound sideBound := by
  cases i with
  | inl i =>
    exact advice_length c r addr width rankW eqRows den num side powers readerBound sideBound
      hr hw hd hn hs i
  | inr i => exact Nat.zero_le _

/-- The bounds consumed by the preparation routine. Only the live unary label
can exceed the maximum advised word length. -/
theorem fit (label cur next : ℕ) :
    let M := portBound addr width e readerBound sideBound
    let rootData := RootInit.template c r addr width den num
    let dynamicData := Dynamic.bank side (Dynamic.regs (w := addr) 0 0 rankW eqRows 0 0 0 0)
    let unaryData := UnaryWord.store [] [] (digits addr 0) [] []
    (∀ i, (rootData i).length ≤ M) ∧ (∀ i, (dynamicData i).length ≤ M) ∧
      (∀ i, (unaryData i).length ≤ M) ∧
      (∀ k, (NativeReader.state (List.replicate label true) (digits addr cur) (digits addr next) []
        (advice c r addr width rankW eqRows den num side powers) (fun _ : Prepare.Work D K T ↦ []) k).length
        ≤ max label M) := by
  intro M rootData dynamicData unaryData
  have bound := advice_length c r addr width rankW eqRows den num side powers readerBound sideBound hr hw hd hn hs
  refine ⟨fun i ↦ bound (.inl (.inl i)), fun i ↦ bound (.inl (.inr (.inl i))),
    fun i ↦ bound (.inl (.inr (.inr i))), ?_⟩
  have addr_le : addr ≤ M := (le_max_left addr sideBound).trans (le_max_right ..)
  intro k
  cases k with
  | label => exact List.length_replicate.trans_le (le_max_left ..)
  | current | next => exact (length_digits ..).le.trans (addr_le.trans (le_max_right ..))
  | result => exact Nat.zero_le _
  | aux k => rcases k with i | i
             · exact (bound i).trans (le_max_right ..)
             · exact Nat.zero_le _

theorem advice_total_length [Fintype (Prepare.Advice D K T)] :
    ∑ i, (advice c r addr width rankW eqRows den num side powers i).length ≤
      Fintype.card (Prepare.Advice D K T) * portBound addr width e readerBound sideBound := by
  calc
    _ ≤ ∑ _ : Prepare.Advice D K T, portBound addr width e readerBound sideBound :=
      Finset.sum_le_sum fun i _ ↦ advice_length c r addr width rankW eqRows den num side powers
        readerBound sideBound hr hw hd hn hs i
    _ = _ := by simp

/-- Empty work ports add no bits to the total advice length. -/
theorem extra_total_length [Fintype (Prepare.Advice D K T)] [Fintype (Prepare.Work D K T)] :
    ∑ i, (extra c r addr width rankW eqRows den num side powers i).length ≤
      Fintype.card (Prepare.Advice D K T) * portBound addr width e readerBound sideBound := by
  simpa [Fintype.sum_sum_type, extra] using
    advice_total_length c r addr width rankW eqRows den num side powers readerBound sideBound
      hr hw hd hn hs

end RankQuery.Stack.Coordinate.FullAdvice

end VPVNP
end Computability
end OAI
