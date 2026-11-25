import OAI.ThreeFlat.RAM.TickSelectedPins
import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # Physical pair-bit sources at original trace buckets -/

namespace ThreeFlat.RAM.HistoryPairSeeds

open Computability.VPVNP.BurstRAM DescriptorExpr PhysicalPinsExpr BitLayout
open scoped Fin.CommRing

/-- A four-word interval row in S5 provides its packed offset in the last
column. The two absolute source bases in S2 are loaded once per output word.
Selector zero accesses an old bit and selector one accesses a new bit. -/
def formula : Formula 3 :=
  let bit : Formula 3 := .reg 0; let row : Formula 3 := .reg 1; let bounds : Formula 3 := .reg 2
  let base := .load (add (add bounds (L 2)) (rem bit (L 2)))
  add base (add (.load (add row (L 3))) (div bit (L 2)))

def program (w k : ℕ) := formula.compile (w:=w) (k:=k+1) (fun _ => 0)

theorem numeric (w : ℕ) (mem : ℕ→ℕ) (data : Param→ℕ) (bit row bounds : ℕ) :
    formula.natural w data mem ![bit,row,bounds] = mem (bounds+2+bit%2)+(mem (row+3)+bit/2) := by
  simp [formula,Formula.natural,natOp]

theorem yields {w k a cap n q nt ns np u teams hidden : ℕ} (fit : 1+cap+2*n≤a)
    (base row : ℕ) (data : Fin (k+1) → ℕ) (mem : ℕ → ℕ) (start i side : ℕ) (sideBound : side<2)
    (live : start+i<n) (paired : mem (row+3)=start)
    (old : mem (base+2)=(TickPhysicalABI.mounted u a teams cap q nt ns np).oldAux+1+cap)
    (newer : mem (base+3)=(TickPhysicalABI.mounted u a teams cap q nt ns np).oldAux+1+cap+n)
    (room : formula.Fits w (fun _ => data 0) mem ![2*i+side,row,base]) :
    (program w k).eval (fun j => (data j : Word w)) (fun j => (mem j : Word w))
      (fun j => ((![2*i+side,row,base] j : ℕ) : Word w)) =
      ((sourceAddress (n:=hidden) (.pin (TickSelectedPins.pair fit q nt ns np (decide (side=1)) ⟨start+i,live⟩)) : ℕ) : Word w) := by
  rw [program, Formula.eval_compile]
  simp only [Function.comp_def]
  rw [Formula.value_eq_natural formula (fun _ => data 0) mem _ room, numeric]
  rw [TickSelectedPins.pair_address (u:=u) (teams:=teams) fit]
  have div : (2*i+side)/2=i := by omega
  have md : (2*i+side)%2=side := by omega
  rw [div,md,paired]
  interval_cases side <;> simp [old,newer,Nat.add_assoc]

end ThreeFlat.RAM.HistoryPairSeeds

end OAI
