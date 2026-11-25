import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepBankLedger
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepLinear

/-! # Uniform volume bounds for the two check-bank sweeps -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.SweepBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  CommonRegisters Space InterchangeROM InterchangeROMAddress InterchangeAddress InterchangeBatch
open Physical (Positions Allowance Bank)

variable {A J : Type} {D : A → Type}

private theorem list_limits (l : List A) (f : A → ℕ) (k : ℕ) (h : ∀ x ∈ l, f x ≤ k) :
    (l.map f).sum ≤ l.length*k ∧ (l.map f).foldr max 0 ≤ k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have u := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have v := h a (List.mem_cons_self ..)
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,List.foldr_cons]
    omega

/-- Only the clock repeats its scan allowance at each field. The space of a
previous pass is available to the next one. -/
theorem field_limits (s : Series A) (h : Tree) (enc : (a : A) → D a → Tree)
    (op : J → (a : A) → D a → D a) (cost : J → (a : A) → D a → Allowance) (V K : ℕ)
    (volume : ∀ x : (a : A) → D a, (packet h (s.tab fun a => enc a (x a))).count+1 ≤ V)
    (price : ∀ j a d, (cost j a d).time ≤ K ∧ (cost j a d).cap ≤ K ∧ (cost j a d).depth ≤ K)
    (js : List J) (x : (a : A) → D a) :
    let z := fieldCost s h enc op cost js x
    z.time ≤ 1+js.length*((s.count+2)*(160*V)+s.count*K+2) ∧
    z.cap ≤ 172*V+K ∧ z.depth ≤ 172*V+K := by
  induction js generalizing x with
  | nil => have := volume x; simp only [fieldCost,List.length_nil,Nat.zero_mul,Nat.add_zero]; omega
  | cons j js ih =>
    let y a := op j a (x a)
    have rest := ih y
    dsimp only [y] at rest
    have vx := volume x
    have vy := volume y
    dsimp only [y] at vy
    have time := (list_limits s.explore (fun a => (cost j a (x a)).time) K
      (fun a _ => (price j a _).1)).1
    have cap := (list_limits s.explore (fun a => (cost j a (x a)).cap) K
      (fun a _ => (price j a _).2.1)).2
    have depth := (list_limits s.explore (fun a => (cost j a (x a)).depth) K
      (fun a _ => (price j a _).2.2)).2
    have v := Nat.mul_le_mul_left (s.count+2) (Nat.mul_le_mul_left 160 vx)
    simp only [fieldCost,packetCost,Series.tab,List.map_map,Function.comp_def,List.length_map,
      List.length_cons]
    rw [Nat.succ_mul js.length]
    dsimp only [Series.count,Series.tab] at rest v vx vy ⊢
    omega

private theorem forest_limit (s : Series A) (r : A → Tree) (Q : ℕ) (hr : ∀ a, (r a).count+1 ≤ Q) :
    (Task.forest id (s.tab r)).count ≤ s.count*Q+1 := by
  suffices g : ∀ xs : List A, (Task.forest id (xs.map r)).count ≤ xs.length*Q+1 from g s.explore
  intro xs
  induction xs with
  | nil => simp [Task.forest,Tree.count]
  | cons a xs ih =>
    have hb := hr a
    simp only [List.map_cons,Task.forest_cons,Tree.count,id_eq,List.length_cons,Nat.succ_mul]
    omega

def packetRate (n p H : ℕ) := H+n*(2*p+12)+3
def clockRate (m n k v : ℕ) := 1+m*((n+2)*(160*v)+n*k+2)
def spaceRate (k v : ℕ) := 172*v+k

variable {P G S : Dims.Tape} {p a m l s b f w : ℕ} {E : Type}
local notation "X" => Positions P G S a m b f
local notation "R" => ZMod (p+1)
local notation "F" => Fin (a+m+a)

theorem local_limits (hb : 2 ≤ b) (ok : ∀ k ∈ P++G++S, 2 ≤ k ∧ k ≤ b) (H : ℕ)
    (hh : (send (header f P G S)).count ≤ H*((layout P G S a m b f).count*(w+1)+1))
    (pay : Series E) (hw : pay.count ≤ w) (half : ℕ) (inv : Bool) (x y : Bank R (Fin l) (X × E) (Fin s)) :
    let C := (layout P G S a m b f).count*(w+1)+1
    let n := 2*(l*s)
    let v := packetRate n p H
    let k := Sweep.rate b (a+m+a) p half inv
    let z := charge w half inv pay (fun _ => noneCost) x y
    z.time ≤ clockRate m n k v*C ∧ z.cap ≤ spaceRate k v*C ∧ z.depth ≤ spaceRate k v*C := by
  let rows := layout P G S a m b f
  let h := send (header f P G S)
  let C := rows.count*(w+1)+1
  let n := 2*(l*s)
  let v := packetRate n p H
  let k := Sweep.rate b (a+m+a) p half inv
  have pos : 1 ≤ C := by dsimp [C]; omega
  have bounded (x : Bool × Fin (l*s) → X → E → R) :
      (packet h ((banks l s).tab fun i => Sweep.row rows pay (x i))).count+1 ≤ v*C := by
    have hg (i) : (Sweep.row rows pay (x i)).count+1 ≤ (2*p+12)*C := by
      have hrow := (Sweep.packed_trees rows pay w p hw (fun _ => .eq) (x i)).2.2.2
      change _ ≤ (2*p+11)*C at hrow
      simpa only [show 2*p+12 = (2*p+11)+1 by omega,Nat.add_mul,Nat.one_mul] using Nat.add_le_add hrow pos
    have hf := forest_limit (banks l s) _ _ hg
    rw [banks_count] at hf
    change (Task.forest id _).count ≤ n*((2*p+12)*C)+1 at hf
    change h.count ≤ H*C at hh
    change (Tree.fork h _).count+1 ≤ (H+n*(2*p+12)+3)*C
    rw [show (H+n*(2*p+12)+3)*C = H*C + n*((2*p+12)*C) + 3*C by ring, Tree.count]
    omega
  have hcost (j : F) (_i : Bool × Fin (l*s)) (g : X → E → R) :
      let c := rowCost w half inv pay (fun _ => noneCost) j g
      c.time ≤ k*C ∧ c.cap ≤ k*C ∧ c.depth ≤ k*C := by
    simpa only [rowCost,C,k,rows,layout,noneCost,Nat.zero_add] using Sweep.native_linear_cost (Equiv.refl F) (fun _ : Unit => P) (fun _ => G) (fun _ => S)
      (fun _ => f) (fun _ => w) (fun _ => pay) j p half inv (fun _ => g) () noneCost hb ok hw
  have out := field_limits (banks l s) h (fun _ => Sweep.row rows pay) (fun j _ => update inv (half:R) j)
    (fun j _ => rowCost w half inv pay (fun _ => noneCost) j) (v*C) (k*C) bounded hcost
    (order a m inv) (streams x y)
  rw [banks_count,order_length] at out
  have clk : 1+m*((n+2)*(160*(v*C))+n*(k*C)+2) ≤ clockRate m n k v*C := by
    have m2 : 2 ≤ 2*C := by omega
    have v1 := Nat.add_le_add_left m2 ((n+2)*(160*(v*C))+n*(k*C))
    have v2 : (n+2)*(160*(v*C))+n*(k*C)+2*C = ((n+2)*(160*v)+n*k+2)*C := by ring
    calc
      _ ≤ C+m*(((n+2)*(160*v)+n*k+2)*C) := Nat.add_le_add pos (Nat.mul_le_mul_left _ (v1.trans_eq v2))
      _ = _ := by unfold clockRate; ring
  have sp : 172*(v*C)+k*C=spaceRate k v*C := by dsimp [spaceRate]; ring
  exact ⟨out.1.trans clk,out.2.1.trans_eq sp,out.2.2.trans_eq sp⟩

end InterchangeROMRepair.SweepBank

end NearSquareRoot
end Computability
end OAI
