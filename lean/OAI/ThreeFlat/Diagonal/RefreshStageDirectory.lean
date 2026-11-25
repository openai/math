import OAI.ThreeFlat.Diagonal.RefreshStageNav

namespace OAI
/-! # Refresh directory reads and materialized row descriptors -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM Computability.VPVNP.Compression RAM RAM.PhysicalPinsExpr RAM.MotifRows RefreshDemandRows
open RefreshTies CompressorPacking.Native MotifIntegerChoice
open scoped Classical
noncomputable section

variable {W a v t k : ℕ} (current : Word W)
variable (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin 1 → ℕ)
local notation "V" => Formula.natural W data mem vs

abbrev info (mem : ℕ → ℕ) (current : Word W) (off : ℕ) := mem (mem current.val+off)

theorem field_read (off : ℕ) : V (field current off) = info mem current off := rfl

/-- Concrete shift-column arithmetic for every valid old base-slot row. -/
theorem split_read (m len : ℕ) (p : Fin len) (col : Fin 3)
    (hlen : info mem current 11 = len) (addr : vs 0 = info mem current 12 + col.val*len+p.val) :
    V (splitShifts m current) =
      let old := info mem current 10+(if col.val=0 then 2 else 5)*len+p.val
      if col.val=2 then mem old % m else mem old / m := by
  have pos : V (index current 12) = col.val*len+p.val := by
    change vs 0-info mem current 12=_
    rw [addr]; omega
  have q : (col.val*len+p.val)/len=col.val := by
    rw [Nat.mul_comm col.val,Nat.mul_add_div (Nat.zero_lt_of_lt p.isLt),Nat.div_eq_of_lt p.isLt,Nat.add_zero]
  have r : (col.val*len+p.val)%len=p.val := by
    rw [Nat.mul_comm col.val,Nat.mul_add_mod,Nat.mod_eq_of_lt p.isLt]
  let idx := V (index current 12)
  let span := info mem current 11
  let src := info mem current 10
  let read (column row length : ℕ) :=
    if decide (column=0) then mem (src+length*2+row)/m
    else if decide (column=1) then mem (src+length*5+row)/m
    else mem (src+length*5+row)%m
  change read (idx/span) (idx%span) span = _
  have digit : idx/span=col.val := by dsimp only [idx,span]; rw [pos,hlen,q]
  have offset : idx%span=p.val := by dsimp only [idx,span]; rw [pos,hlen,r]
  have length : span=len := hlen
  calc
    read (idx/span) (idx%span) span = read col.val p.val len := by
      exact (congrArg (fun x => read x (idx%span) span) digit).trans
        ((congrArg (fun x => read col.val x span) offset).trans (congrArg (read col.val p.val) length))
    _ = _ := by fin_cases col <;> simp [read,src,Nat.mul_comm]

/-- Physical meanings of the three fields passed to the universal histogram
parser for one block. These expressions do not read the proposed counts. -/
theorem choice_read (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ) (size : Fin (k+1) → ℕ)
    (w : Address' v a t → ℕ) (z : Block v t) (f : Fin 3)
    (stored : Stored G ((input current).map V) mem w)
    (radix : info mem current 8 = 2^t) (start : vs 0 = info mem current 2 + blockId z*3+f.val) :
    let s := fun e => w (addr (arrival G (tagOrdinal a).symm) z e)
    let j := tileNumber s base
    V (choiceWords current base size) =
      if f.val=0 then score s base j else if f.val=1 then j.val else size j := by
  let rel := index current 2
  let row := Formula.op .div rel (.lit 3)
  let member := Formula.op .mod rel (.lit 3)
  have pos : V rel=blockId z*3+f.val := by
    change vs 0-info mem current 2=_
    rw [start]; omega
  have q : V row = blockId z := by
    change V rel/3=_
    rw [pos,Nat.mul_comm (blockId z),Nat.mul_add_div (by decide),Nat.div_eq_of_lt f.isLt,Nat.add_zero]
  have r : V member = f.val := by
    change V rel%3=_
    rw [pos,Nat.mul_comm (blockId z),Nat.mul_add_mod,Nat.mod_eq_of_lt f.isLt]
  let s := fun e => w (addr (arrival G (tagOrdinal a).symm) z e)
  let j := tileNumber s base
  let code := refreshChoice (input current) (field current 8) row base
  have hv := refreshChoice_value G W data mem vs (input current) (field current 8) row z w stored radix q base
  have u₀ : V code.1 = score s base j := congrArg Prod.fst hv
  have u₁ : V code.2 = j.val := congrArg Prod.snd hv
  dsimp only
  change (if decide (V member=0) then V code.1 else if decide (V member=1) then V code.2
    else V (rowAt (k+1) (fun i => .lit (size i)) code.2)) = _
  rw [rowAt_hit W data mem vs _ _ j u₁]
  simp only [r,decide_eq_true_eq,Formula.natural,u₀,u₁,j,s]

end
end ThreeFlat.Diagonal.RefreshStageNav

end OAI
