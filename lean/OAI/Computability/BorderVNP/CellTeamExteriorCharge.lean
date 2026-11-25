import OAI.Computability.BorderVNP.CellTeamBitDelivery

/-! # The total exterior-bank width of the cells on one native team

Only crossing cables and attached ports enter the canonical supplied bank.
A crossing cable contributes its width to each owned endpoint. Each directed
label bin has its actual rounded slot capacity. Port fields form a subset of
the scheduled deliveries, so their true widths use the same checked team limit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRowClock

open Physical Crossing Packing.CellAddresses
open private twoEnds ends_le_raw from OAI.Computability.BorderVNP.CubeHostScatterIncidence
open scoped Classical

private theorem fiber_eq {I : Type*} [Fintype I] (p : I → Prop) [DecidablePred p] (size : I → ℕ) :
    (∑ i : {i // p i}, size i.val) = ∑ i, if p i then size i else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun _ => by simp) _).symm

private theorem assigned_add {I : Type*} [Fintype I] (owner : I → ℕ) (team : ℕ) (x y : I → ℕ) :
    assignedSum owner team (fun i => x i+y i)=assignedSum owner team x + assignedSum owner team y := by
  unfold assignedSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all

private theorem assigned_congr {I : Type*} [Fintype I] (owner : I → ℕ) (team : ℕ) (x y : I → ℕ)
    (eq : ∀ i, x i=y i) : assignedSum owner team x=assignedSum owner team y := by rw [funext eq]

/-- Split every owned cell's actual bank into its two endpoint roles and its supplied ports. -/
theorem supplied_eq {z : ℕ} {P : Type*} {C : Type} [Fintype P] [Fintype C] {bits : P → ℕ}
    (N : Network z P bits) (cell : N.Site → C) (owner : C → ℕ) (team : ℕ) :
    assignedSum owner team (fun c => suppliedSize N cell c) =
      assignedSum (owner ∘ crossSrc N cell) team (crossWidth N cell) +
      assignedSum (owner ∘ crossDst N cell) team (crossWidth N cell) +
      assignedSum (owner ∘ cell ∘ N.attach) team bits := by
  classical
  let src := crossSrc N cell
  let dst := crossDst N cell
  let w := crossWidth N cell
  let port := cell ∘ N.attach
  let S (c : C) := ∑ e : {e // src e=c}, w e.val
  let T (c : C) := ∑ e : {e // dst e=c}, w e.val
  let B (c : C) := ∑ p : {p // port p=c}, bits p.val
  have per (c : C) : suppliedSize N cell c = S c+T c+B c := by
    rw [suppliedSize,Fintype.sum_sum_type]
    apply congrArg (·+B c)
    change (∑ e : {e // src e=c ∨ dst e=c}, w e.val) = _+_
    dsimp only [S,T]
    rw [fiber_eq,fiber_eq,fiber_eq,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    have diff : src e ≠ dst e := e.property
    by_cases hs : src e=c <;> by_cases hd : dst e=c <;> simp_all
  rw [assigned_congr owner team _ _ per,assigned_add,assigned_add]
  exact congrArg₂ Nat.add (congrArg₂ Nat.add (assignedSum_fibers src owner team w) (assignedSum_fibers dst owner team w))
    (assignedSum_fibers port owner team bits)

private theorem incidence {n d m : ℕ} (S : ℕ) (axis : Fin (n+1))
    (pair : Fin m → Label (n+1) d × Label (n+1) d) (w : Fin m → ℕ) (owner : Fin d → ℕ) (team : ℕ)
    (cap : ∀ p, load pair w p ≤ S) :
    assignedSum (fun e => owner ((pair e).1 axis)) team w + assignedSum (fun e => owner ((pair e).2 axis)) team w ≤
      2 * ownedRaw owner team S axis := by
  classical
  let left (e : Fin m) := (pair e).1 axis
  let right (e : Fin m) := (pair e).2 axis
  change assignedSum (owner ∘ left) team w + assignedSum (owner ∘ right) team w ≤ _
  rw [← assignedSum_fibers left owner team w,← assignedSum_fibers right owner team w,← assigned_add,
    assignedSum,ownedRaw,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  by_cases yes : owner u=team
  · simp only [yes,ite_true,fiber_eq,← Finset.sum_add_distrib]
    apply le_trans _ (ends_le_raw axis u pair w S cap)
    apply Finset.sum_le_sum
    intro e _
    by_cases hl : (pair e).1 axis = u <;> by_cases hr : (pair e).2 axis = u <;>
      (simp [left,right,twoEnds,hl,hr]; try omega)
  · simp [yes]

variable {g : GroupWeights.Layout} {teams : TeamNative.Layout} {orig mem : ℕ → ℕ}
variable {n blocks b K h : ℕ} {D : LengthDeclaration n g.groups}
variable {A : Type*} [Fintype A] {label : Fin g.cells → Label (n+1) g.groups}
variable {recv : A → Fin g.cells} {incoming : A → ℕ}

/-- Canonical supplied words over all assigned cells fit the per-team exterior
bound, directly from the actual checked loads, packed bin capacities and real
port-delivery intervals. -/
theorem supplied_le {z m : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    (N : Network z P bits) (cell : N.Site → Fin g.cells) (ord : N.CrossingEdge cell ≃ Fin m)
    (result : GroupWeights.ScheduleResult g teams orig mem)
    (image : GroupWeights.PhysicalImage g orig blocks b K h D label recv incoming)
    (team : Fin (teams.r+1)) (X : ℕ) (pass : TeamNative.unscale (mem (teams.totals+team.val)) ≤ (X:ℚ)/256)
    (capacity : ∀ pair, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
      (crossWidth N cell ∘ ord.symm) pair ≤ blocks*(h*b))
    (portDelivery : BitDelivery (cell ∘ N.attach) bits recv incoming) :
    let owner := fun u : Fin g.groups => mem (teams.owners+u.val)
    assignedSum (fun c => owner (label c D.1)) team.val (fun c => suppliedSize N cell c) ≤ 2*(1000000*X/256)+X := by
  intro owner
  let who (c : Fin g.cells) := owner (label c D.1)
  let pair := cablePair ord (crossSrc N cell) (crossDst N cell) label
  let w := crossWidth N cell
  have edge (ft : Fintype (N.CrossingEdge cell)) (endPoint : N.CrossingEdge cell → Fin g.cells) :
      @assignedSum (N.CrossingEdge cell) ft (who ∘ endPoint) team.val w = assignedSum (who ∘ endPoint ∘ ord.symm) team.val (w ∘ ord.symm) := by
    let : Fintype (N.CrossingEdge cell) := ft
    exact (ord.symm.sum_comp (fun e => if who (endPoint e)=team.val then w e else 0)).symm
  have inc := incidence (blocks*(h*b)) D.1 pair (w ∘ ord.symm) owner team.val capacity
  change assignedSum who team.val (fun c => suppliedSize N cell c) ≤ _
  rw [supplied_eq]
  rw [edge _ (crossSrc N cell),edge _ (crossDst N cell)]
  have ⟨del,raw⟩ := assigned_input_bounds result image team X pass
  exact Nat.add_le_add (inc.trans (Nat.mul_le_mul_left 2 raw))
    ((portDelivery.load_le who team.val).trans del)

end Cube.TeamRowClock

end BorderVNP
end Computability
end OAI
