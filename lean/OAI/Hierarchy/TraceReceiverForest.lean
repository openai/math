import OAI.ThreeFlat.Diagonal.HistoryAssembly
import OAI.ThreeFlat.Diagonal.HistoryStageCharges
import OAI.ThreeFlat.Diagonal.TickSlotForest
import OAI.ThreeFlat.BitNetwork.PinMap

namespace OAI
/-! # The factor list consumed by a physical receiver slot -/

noncomputable section
namespace Hierarchy.TraceFactorReceiver

open ThreeFlat Diagonal
open scoped BigOperators Classical

variable {F : Type*} [Field F] {p : ℕ}

/-- Numerically recorded rows of the actual selected roots. Here the pin map
is the location of each selected root's original or terminal boundary bit on
this tick's own exposed tape. -/
def forest {n : ℕ} {arity : Fin n → ℕ} (nets : ∀ i, BitNetwork F (arity i))
    (wires : ∀ i, Fin (arity i) → Fin p) : BitNetwork F p :=
  TickSlotForest.network (fun i => (nets i).restrictPins (some ∘ wires i))

theorem forest_eval {n : ℕ} {arity : Fin n → ℕ} (nets : ∀ i, BitNetwork F (arity i))
    (wires : ∀ i, Fin (arity i) → Fin p) (pin : Fin p → Bool) :
    (forest nets wires).eval pin = ∏ i, (nets i).eval (pin ∘ wires i) := by
  rw [forest,TickSlotForest.eval]
  apply Finset.prod_congr rfl
  intro i _
  rw [BitNetwork.restrictPins_eval]
  rfl

open Diagonal.HistoryContraction in
/-- The selected list is retained in its supplied order, including repeated
owners. The only input data used by each root are its actual local pin reads. -/
theorem selected_product {S : Shape} {Pins α : Type*} (P : Plan F S) (h : P.History)
    {V : Form S Pins} (A : P.Assembly V) (seed : Forest F V) (x : Pins)
    (boundary : (P.finish h).Boundary) (items : List α) (site : α → (P.finish h).Site)
    (pin : Fin p → Bool)
    (wires : ∀ i : Fin items.length, Fin ((P.assemble h A seed).1.width (site items[i])) → Fin p)
    (reads : ∀ i j, pin (wires i j) = (P.assemble h A seed).1.read (site items[i]) x
      ((P.finish h).graph.atVertex boundary (site items[i])) j) :
    (forest (fun i : Fin items.length => ((P.assemble h A seed).2 (site items[i])).compile)
      wires).eval pin =
      (items.map (fun v => P.cells h (V.values seed x) (site v)
        ((P.finish h).graph.atVertex boundary (site v)))).prod := by
  rw [forest_eval]
  let scalar := fun v => P.cells h (V.values seed x) (site v) ((P.finish h).graph.atVertex boundary (site v))
  calc
    _ = ∏ i : Fin items.length, scalar items[i] := by
      apply Finset.prod_congr rfl
      intro i _
      have atPins : pin ∘ wires i = (P.assemble h A seed).1.read (site items[i]) x
          ((P.finish h).graph.atVertex boundary (site items[i])) := funext (reads i)
      rw [atPins]
      exact congrFun (congrFun (P.assemble_values h V A seed x) (site items[i]))
        ((P.finish h).graph.atVertex boundary (site items[i]))
    _ = _ := by
      rw [← List.prod_ofFn,List.ofFn_comp' (fun i : Fin items.length => items[i]) scalar]
      exact congrArg (fun l => (l.map scalar).prod) (List.ofFn_getElem (xs:=items))

omit [Field F] in
/-- The real dimensions of a selected forest fit the common padded dimensions
as soon as its assigned local work fits the slot. -/
theorem forest_fits {m n : ℕ} {arity : Fin n → ℕ} (nets : ∀ i, BitNetwork F (arity i))
    (wires : ∀ i, Fin (arity i) → Fin p) (cost : Fin n → ℕ)
    (paid : ∀ i, 10000*((nets i).cells+(nets i).internal) ≤ cost i)
    (budget : ∑ i, cost i ≤ m/4) :
    let N := forest nets wires
    N.internal ≤ m/40000 ∧ N.cells+(m/40000-N.internal) ≤ 2*(m/40000) :=
  TickSlotForest.padding_fits (fun i => (nets i).restrictPins (some ∘ wires i)) m
    ((Finset.sum_le_sum (fun i _ => paid i)).trans budget)

namespace Gather
open Diagonal.HistoryContraction in
/-- The same site tariff pays for the history replay, input maps, seven-word
command generation, extra copy into the receiving forest, and native root
field scan. Each constant is charged even when a selected tree has zero rows. -/
theorem tree_tariff {G : Type*} {k depth : ℕ} (T : Tree G k) (level : Tree.Within depth T)
    (setup maps : ℕ) :
    T.replayWork setup + (7224+19+1016*T.compile.cells + (9+5*T.compile.internal+22*T.compile.cells)) +
      maps*T.footprint.pins ≤ (10025+1016*depth+setup+maps)*T.resources := by
  have reserve : 7224+19+1016*T.compile.cells+(9+5*T.compile.internal+22*T.compile.cells) ≤
      10000*(T.nodes+T.rows+T.bits) := by
    rw [Tree.compiled_rows,Tree.compiled_bits]
    have := T.nodes_pos
    omega
  have generated := Nat.add_le_add (Tree.replay_le level setup) reserve
  have total := (Tree.native_cost T depth setup maps)
  apply le_trans _ total
  apply Nat.add_le_add_right
  unfold Tree.scheduledWork
  rw [show 10000+25+1016*depth+setup = (25+1016*depth+setup)+10000 by omega,Nat.add_mul]
  exact generated

/-- The earlier selected-stage procedure pays a fixed block instruction rate
for each visited ancestor. Its terminal pin-map scan has a fixed ROM cost
per half-port and per emitted word. -/
def setupPrice (stages stageRate : ℕ) := 10*(stages+2)^2*stageRate
def mapPrice (degree rootRate : ℕ) := rootRate*(degree+7)

/-- The actual stage-join and terminal-map prices fit within the two extra
coefficients of the archive tariff, leaving the per-tree replay and scan
reserve available for the terminal gather. -/
theorem archive_price (stages degree stageRate rootRate K : ℕ) (positive : 0<K) :
    let rows := (2*stages+1)*K
    10*(stages+2)^2*stageRate*K + rootRate*(degree+4*rows+3) ≤
      (setupPrice stages stageRate+mapPrice degree rootRate)*rows := by
  intro rows
  have units : K≤rows := by
    dsimp only [rows]
    exact Nat.le_mul_of_pos_left K (by omega)
  have d := Nat.le_mul_of_pos_right degree (positive.trans_le units)
  have terminal : degree+4*rows+3≤(degree+7)*rows := by
    rw [Nat.add_mul]
    omega
  rw [Nat.add_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ units)
    ((Nat.mul_le_mul_left rootRate terminal).trans_eq (Nat.mul_assoc ..).symm)

theorem prices_polynomial (w b a stages degree stageRate rootRate : ℕ)
    (height : stages≤a*(w+1)^b) (ports : degree≤a*(w+1)^b) :
    setupPrice stages stageRate ≤ (10*(a+2)^2*stageRate)*(w+1)^(b+b) ∧
    mapPrice degree rootRate ≤ (rootRate*(a+7))*(w+1)^b := by
  let x := (w+1)^b
  have positive : 1≤x := Nat.pow_pos (Nat.succ_pos _)
  change stages≤a*x at height
  change degree≤a*x at ports
  have bound : stages+2≤(a+2)*x := by rw [Nat.add_mul]; omega
  have port : degree+7≤(a+7)*x := by rw [Nat.add_mul]; omega
  have sq := Nat.mul_le_mul_right stageRate (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left bound 2))
  refine ⟨sq.trans_eq ?_,(Nat.mul_le_mul_left rootRate port).trans_eq ?_⟩
  · dsimp only [x]; rw [pow_add]; ring
  · exact (Nat.mul_assoc ..).symm

end Gather

end Hierarchy.TraceFactorReceiver
end

end OAI
