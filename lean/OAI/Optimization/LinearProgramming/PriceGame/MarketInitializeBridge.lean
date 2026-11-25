import OAI.Optimization.LinearProgramming.PriceGame.MarketInitializeMachine
import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineModel

/-! Agreement of serialized rational preparation with the initial state used
by the typed capacitated augmentation algorithm, including its exact cost grid. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace InitializeMachine
open FlowMachine

variable {m g : ℕ}

def typed (I : Augment.Input m g) (Q : ℕ) (L : Fin m → ℚ) : Input :=
  ((Q,List.ofFn L),g+1,List.ofFn I.positive,
    packedCells (fun e o => o.elim true (I.available e)),
    packedCells (bid I.intercept))

private theorem mem_packed {α : Type*} (f : Fin m → Option (Fin g) → α) (a : α) :
    a ∈ packedCells f ↔ ∃ e o, f e o = a := by
  rw [packedCells, List.mem_ofFn]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨_,_,hi⟩
  · rintro ⟨e,o,rfl⟩
    exact ⟨cellEquiv m g (e,o),by simp⟩

private theorem upper_max {xs : List ℚ} {b a : ℚ} (ha : a ≤ b) (hb : ∀ q ∈ xs, q ≤ b) :
    xs.foldl (fun best q => max q best) a ≤ b := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    exact ih (max_le (hb x (by simp)) ha) (fun q hq => hb q (by simp [hq]))

private theorem lower_max (xs : List ℚ) (a : ℚ) :
    a ≤ xs.foldl (fun best q => max q best) a ∧
      ∀ q ∈ xs, q ≤ xs.foldl (fun best q => max q best) a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hle,hall⟩ := ih (max x a)
    refine ⟨(le_max_right _ _).trans hle, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | h
    · exact (le_max_left _ _).trans hle
    · exact hall q h

theorem maxAbsolute_agrees (c : Fin m → Fin g → ℚ) :
    maxAbsolute (packedCells (bid c)) = OptimumDual.costBound c := by
  unfold maxAbsolute
  let xs := (packedCells (bid c)).map (fun q => |q|)
  change xs.foldl (fun best q => max q best) 0 = _
  obtain ⟨hzero,hl⟩ := lower_max xs 0
  apply le_antisymm
  · apply upper_max (OptimumDual.costBound_nonneg c)
    rintro q hq
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
    obtain ⟨e,o,rfl⟩ := (mem_packed (bid c) b).mp hb
    cases o with
    | none => simpa [bid] using OptimumDual.costBound_nonneg c
    | some i => exact OptimumDual.abs_le_costBound c e i
  · apply Finset.max'_le
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hzero
    · obtain ⟨⟨e,i⟩,_,rfl⟩ := Finset.mem_image.mp hy
      apply hl
      apply List.mem_map.mpr
      exact ⟨c e i,(mem_packed (bid c) _).mpr ⟨e,some i,rfl⟩,rfl⟩

private theorem product_eq (xs : List ℚ) (a : ℕ) :
    xs.foldl (fun n q => n*q.den) a = a*(xs.map Rat.den).prod := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_assoc]

theorem grid_pos (xs : List ℚ) : 0 < grid xs := by
  rw [grid, product_eq, one_mul]
  apply List.prod_pos
  intro a h
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp h
  exact q.den_pos

theorem on_grid_of_mem {xs : List ℚ} {q : ℚ} (h : q ∈ xs) :
    NumberBounds.OnGrid (grid xs) q := by
  rw [NumberBounds.grid_iff_den_dvd (grid_pos xs), grid, product_eq, one_mul]
  exact List.dvd_prod (List.mem_map.mpr ⟨q,h,rfl⟩)

theorem intercept_grid (I : Augment.Input m g) (e : Fin m) (i : Fin g) :
    NumberBounds.OnGrid (grid (packedCells (bid I.intercept))) (I.intercept e i) :=
  on_grid_of_mem ((mem_packed (bid I.intercept) _).mpr ⟨e,some i,rfl⟩)

private theorem map_packed {α β : Type*} (f : Fin m → Option (Fin g) → α) (t : α → β) :
    (packedCells f).map t = packedCells (fun e o => t (f e o)) := by
  simp [packedCells, List.map_ofFn, Function.comp_def]

theorem initial_agrees (I : Augment.Input m g) (Q : ℕ) (L : Fin m → ℚ) :
    let D := grid (packedCells (bid I.intercept))
    let n := I.network I.initial
    let raw := Rows.encodeRaw n (I.decideAcceptance I.initial) D
      (Augment.combine n I.initial.pe I.initial.po)
    initialWord (typed I Q L) =
      (List.ofFn (fun e => Denominator.qty Q (L e)),(((D:ℤ),raw.1),raw.2)) := by
  let D := grid (packedCells (bid I.intercept))
  let n := I.network I.initial
  have accept : (fun (e : Fin m) (o : Option (Fin g)) => o.elim true (I.available e)) =
      Rows.eligibleBit n (I.decideAcceptance I.initial) := by
    funext e o
    cases o with
    | none => rfl
    | some i => cases h : I.available e i <;> simp [Rows.eligibleBit, n, Augment.Input.network, Augment.Input.accepts, h]
  have pe (e : Fin m) :
      (if I.positive e then Grid.scaleInput D (OptimumDual.costBound I.intercept)
      else -Grid.scaleInput D (OptimumDual.costBound I.intercept)) =
        Grid.scaleInput D (I.initial.pe e) := by
    change _ = Grid.scaleInput D ((Augment.State.pack _ _ _).pe e)
    rw [Augment.State.pe_pack]
    cases h : I.positive e <;> simp [side, h, Grid.scaleInput]
  simp only [initialWord, typed, Rows.encodeRaw, List.map_ofFn, Function.comp_def, map_packed,
    maxAbsolute_agrees, accept, n, Augment.combine, Augment.Input.network]
  congr 1
  congr 1
  congr 1
  · congr 1
    funext e
    simp [Augment.Input.initial]
  · apply Prod.ext
    · apply congrArg List.ofFn
      funext e
      exact pe e
    · simp [Augment.Input.initial, Grid.scaleInput, List.replicate_succ]

end InitializeMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
