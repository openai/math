import OAI.Computability.VPVNP.BooleanTranscript
import OAI.ThreeFlat.BitNetwork
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Trivalent cells checking an addressed Boolean circuit

Each deterministic gate has one hidden output and one check. Free choices
are distinct additional hidden bits. The remaining cells may read arbitrary
circuit wires and give scalar weights over the coefficient field.
-/

namespace ThreeFlat.Diagonal.TraceCircuit

open Computability.VPVNP (Ref)
open Computability.VPVNP.BooleanTranscript

variable {F σ : Type*} {n p k b c : ℕ}

/-- One addressed table in a trace. -/
structure Cell (F : Type*) (n p : ℕ) where
  source : Fin 3 → BitSource n p
  table : (Fin 3 → Bool) → F

def Cell.eval (z : Cell F n p) (pins : Fin p → Bool) (hidden : Fin n → Bool) : F :=
  z.table fun j => (z.source j).read hidden pins

/-- Resolve a Boolean reference to its pin, hidden bit, or constant. -/
def address (input : σ → BitSource n p) (slot : Fin k → Fin n) :
    Ref Bool σ k → BitSource n p
  | .var x => input x
  | .const b => .constant b
  | .gate i => .hidden (slot i)

theorem address_read (input : σ → BitSource n p) (slot : Fin k → Fin n)
    (r : Ref Bool σ k) (pins : Fin p → Bool) (hidden : Fin n → Bool) :
    (address input slot r).read hidden pins =
      r.read id (fun x => (input x).read hidden pins) (hidden ∘ slot) := by
  cases r <;> rfl

/-- The third port stores the output, and unused ports of a NOT gate are
constant. The test returns zero on a false gate equation. -/
def gateCell [Zero F] [One F] (input : σ → BitSource n p) (slot : Fin k → Fin n)
    (dest : Fin n) : Gate σ k → Cell F n p
  | .and a b => ⟨![address input slot a, address input slot b, .hidden dest],
      fun z => if (z 0 && z 1) = z 2 then 1 else 0⟩
  | .not a => ⟨![address input slot a, .constant false, .hidden dest],
      fun z => if (!(z 0)) = z 2 then 1 else 0⟩

theorem gateCell_eval [Zero F] [One F] (input : σ → BitSource n p) (slot : Fin k → Fin n)
    (dest : Fin n) (g : Gate σ k) (pins : Fin p → Bool) (hidden : Fin n → Bool) :
    (gateCell (F := F) input slot dest g).eval pins hidden =
      if g.eval (fun x => (input x).read hidden pins) (hidden ∘ slot) = hidden dest
        then 1 else 0 := by
  cases g with
  | and a b =>
    change (if ((address input slot a).read hidden pins && (address input slot b).read hidden pins)
        = hidden dest then _ else _) = _
    rw [address_read, address_read]
    rfl
  | not a =>
    change (if (!((address input slot a).read hidden pins)) = hidden dest then _ else _) = _
    rw [address_read]
    rfl

/-- The table array is in the circuit's original topological order. -/
def gateRows [Zero F] [One F] (input : σ → BitSource n p) :
    {k : ℕ} → Program σ k → (Fin k → Fin n) → Fin k → Cell F n p
  | _, .nil, _ => Fin.elim0
  | k + 1, .snoc prog g, slot =>
    Fin.snoc (gateRows input prog (slot ∘ Fin.castSucc))
      (gateCell input (slot ∘ Fin.castSucc) (slot (Fin.last k)) g)

private theorem rows_check [CommRing F] (input : σ → BitSource n p)
    (prog : Program σ k) (slot : Fin k → Fin n) (pins : Fin p → Bool) (hidden : Fin n → Bool) :
    (∏ i, (gateRows (F := F) input prog slot i).eval pins hidden) =
      prog.check (bit ∘ fun x => (input x).read hidden pins) (bit ∘ hidden ∘ slot) := by
  induction prog with
  | nil => simp [Program.check]
  | @snoc k prog g ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [gateRows, Fin.snoc_castSucc, Fin.snoc_last, gateCell_eval, ih, Program.check]
    have hi : Fin.init (bit (R := F) ∘ hidden ∘ slot) = bit ∘ hidden ∘ (slot ∘ Fin.castSucc) := rfl
    rw [hi, Gate.arith_bits]
    simp only [Function.comp_apply, equalBit_bits]

/-- Deterministic gate checks admit exactly one assignment to all gate wires
after the public pins and the free witness bits have been fixed. -/
theorem gateRows_weight [CommRing F] (input : σ → BitSource n p)
    (prog : Program σ k) (slot : Fin k → Fin n) (pins : Fin p → Bool) (hidden : Fin n → Bool) :
    (∏ i, (gateRows (F := F) input prog slot i).eval pins hidden) =
      if hidden ∘ slot = prog.run (fun x => (input x).read hidden pins) then 1 else 0 := by
  classical
  rw [rows_check, Program.check_bits]

/-- Public inputs use fixed pins and witness inputs use the first `b`
hidden bits. The following `k` hidden bits are the deterministic gates. -/
def witnessInput : Fin p ⊕ Fin b → BitSource (b + k) p :=
  Sum.elim BitSource.pin (fun i => .hidden (i.castAdd k))

/-- One hidden variable and one cell per gate, with the requested extra
scalar weight cells addressed at the output of the circuit. -/
def compile [Zero F] [One F] (prog : Program (Fin p ⊕ Fin b) k)
    (port : Fin c → Fin 3 → Ref Bool (Fin p ⊕ Fin b) k)
    (weight : Fin c → (Fin 3 → Bool) → F) : BitNetwork F p :=
  let rows : Fin (k + c) → Cell F (b + k) p := Fin.addCases (gateRows (F := F) (witnessInput (k := k)) prog (Fin.natAdd b))
    (fun i => (⟨address witnessInput (Fin.natAdd b) ∘ port i, weight i⟩ : Cell F (b + k) p))
  ⟨b + k, k + c, fun i => (rows i).source, fun i => (rows i).table⟩

private theorem witnessInput_read (pin : Fin p → Bool) (guess : Fin b → Bool)
    (ws : Fin k → Bool) :
    (fun i => (witnessInput (k := k) i).read (Fin.append guess ws) pin) = Sum.elim pin guess := by
  funext i
  cases i <;> simp [witnessInput, BitSource.read]

/-- Weight of one trace assignment. An inconsistent deterministic wire kills
the term. Otherwise the remaining factors evaluate at the actual outputs. -/
theorem compile_weight [CommRing F] (prog : Program (Fin p ⊕ Fin b) k)
    (port : Fin c → Fin 3 → Ref Bool (Fin p ⊕ Fin b) k)
    (weight : Fin c → (Fin 3 → Bool) → F)
    (pin : Fin p → Bool) (guess : Fin b → Bool) (ws : Fin k → Bool) :
    (compile prog port weight).weight pin (Fin.append guess ws) =
      if ws = prog.run (Sum.elim pin guess) then
        ∏ i, weight i (fun j => (port i j).read id (Sum.elim pin guess) ws) else 0 := by
  classical
  let v := Fin.append guess ws
  have hv : v ∘ Fin.natAdd b = ws := funext (Fin.append_right guess ws)
  let checks := gateRows (F := F) (witnessInput (k := k)) prog (Fin.natAdd b)
  let tail := fun i => (⟨address witnessInput (Fin.natAdd b) ∘ port i, weight i⟩ : Cell F (b + k) p)
  change (∏ i : Fin (k + c), ((Fin.addCases (motive := fun _ => Cell F (b+k) p) checks tail) i).eval pin v) = _
  rw [Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, checks]
  rw [gateRows_weight]
  simp only [hv, v, witnessInput_read, tail, Cell.eval, Function.comp_apply, address_read]
  by_cases h : ws = prog.run (Sum.elim pin guess) <;> simp [h]

/-- Summing the compiled network gives the sum of the scalar verifier weights
over precisely the free witness bits. The local checks introduce no extra
paths, in any characteristic. -/
theorem compile_eval [CommRing F] (prog : Program (Fin p ⊕ Fin b) k)
    (port : Fin c → Fin 3 → Ref Bool (Fin p ⊕ Fin b) k)
    (weight : Fin c → (Fin 3 → Bool) → F) (pin : Fin p → Bool) :
    (compile prog port weight).eval pin =
      ∑ guess : Fin b → Bool, ∏ i, weight i (fun j =>
        (port i j).read id (Sum.elim pin guess) (prog.run (Sum.elim pin guess))) := by
  classical
  change (∑ v : Fin (b + k) → Bool, (compile prog port weight).weight pin v) = _
  rw [← (Fin.appendEquiv (α := Bool) b k).sum_comp ((compile prog port weight).weight pin),
    Fintype.sum_prod_type]
  simp [Fin.appendEquiv, compile_weight]

end ThreeFlat.Diagonal.TraceCircuit

end OAI
