import OAI.ThreeFlat.Diagonal.TraceRowPackets
import OAI.ThreeFlat.Diagonal.TraceCircuitPad
import OAI.ThreeFlat.Diagonal.TracePacketArray

namespace OAI
/-! # Assembling the paired-row RAM verifier into an addressed trivalent network -/

namespace ThreeFlat.Diagonal.TracePhysical

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM
open TraceRows TraceCircuit TraceRowPackets TraceCompose

variable {F : Type*} [Fintype F] [CommRing F] {w p r k d f S : ℕ}

private abbrev Factors (F : Type*) [Fintype F] := Fintype.card (Factor F)
private abbrev Pins (w r d : ℕ) := Fintype.card (Port w r d)

/-- Padded gates and factors occupying a single row of the universal array. -/
noncomputable def rowCells (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (M : Machine w p r k) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) {d : ℕ} :=
  TracePacketArray.sites (fun v : Fin (2^d) => packet hF hw hp M st hs hf v) scalar

noncomputable def operands (hw : 2 ≤ w+1) (S f : ℕ) (v : Fin (2^d)) (j : Fin (Pins w r d)) :=
  address hw S f v ((Fintype.equivFin (Port w r d)).symm j)

/-- The trivalent tensor network on all open initial-header bits. -/
noncomputable def network (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (M : Machine w p r k) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (d : ℕ) :
    BitNetwork F (S*w) :=
  TracePacketArray.network (fun v : Fin (2^d) => packet hF hw hp M st hs hf v) scalar (address (by omega) S f)

/-- All deterministic gates are eliminated and every shared Boolean
register or sorting wire remains summed exactly once. -/
theorem network_eval_packets (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (M : Machine w p r k) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (d : ℕ)
    (h : Fin S → Word w) :
    (network hF hw hp M st hs hf d).eval (headerPins h) =
      ∑ cpu : CpuBits w r f, ∑ z : SortBits d (w+1), ∏ v : Fin (2^d), ∏ a : Factor F,
        scalar a ((packet hF hw hp M st hs hf v a).2.eval (valuation (by omega) v h cpu z)) := by
  classical
  rw [network,TracePacketArray.eval]
  let e := ordinalBits w r f d
  let weights := fun g : Fin (Fintype.card (Shared w r f d)) → Bool =>
    ∏ v : Fin (2^d), ∏ a : Factor F, scalar a ((packet hF hw hp M st hs hf v a).2.eval
      (fun k => (address (by omega) S f v k).read g (headerPins h)))
  change (∑ g, weights g) = _
  rw [← e.sum_comp weights, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro cpu _
  apply Finset.sum_congr rfl; intro z _
  simp only [weights,e,address_read]

end ThreeFlat.Diagonal.TracePhysical

end OAI
