import OAI.ThreeFlat.Diagonal.RefreshDemandFits
import OAI.ThreeFlat.Diagonal.RefreshChoiceFits

namespace OAI
/-! # Values and schedule of the two native refresh selector expressions -/

namespace ThreeFlat.Diagonal.RefreshDemandRows

open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.DescriptorExpr RAM.PhysicalPinsExpr RAM.MotifRows
open MotifIntegerChoice RefreshTies CompressorPacking.Native
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {a t v k W n : ℕ}
variable (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
variable (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
local notation "V" => Formula.natural W data mem vs
local notation "Fit" => Formula.Fits W data mem vs
local notation "EV" => Formula.value (fun p => (data p : Word W)) (fun j => (mem j : Word W)) (fun i => (vs i : Word W))

theorem native_choice (C : Columns (Formula n)) (remaining block : Formula n) (z : Block v t)
    (d : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (w : Address' v a t → ℕ) (stored : Stored G (C.map V) mem w)
    (hrem : V remaining = 2^t) (hblock : V block = blockId z)
    (hbr : Fit block) (hrr : Fit remaining) (hbc : V block < 2^W)
    (hpc : mPort a ≤ 2^W) (hrc : 2^t < 2^W)
    (hf : Fit C.widths ∧ Fit C.sourceBase ∧ Fit C.sourceSlot ∧ Fit C.portShift ∧ Fit C.laneShift)
    (hw : V C.widths+(v*mPort a)*(mPort a*2^t) ≤ 2^W)
    (hc : ∀ c ∈ [C.sourceBase,C.sourceSlot,C.portShift,C.laneShift], V c + v*mPort a ≤ 2^W)
    (hs : sentinel (fun e => w (addr (arrival G (tagOrdinal a).symm) z e)) < 2^W)
    (hd : ∀ j e, sentinel (fun e => w (addr (arrival G (tagOrdinal a).symm) z e)) + d j e < 2^W)
    (hk : k < 2^W) :
    let result := refreshChoice C remaining block d
    let demandWidths := fun e => w (addr (arrival G (tagOrdinal a).symm) z e)
    let j := tileNumber demandWidths d
    ((EV result.1).val,(EV result.2).val) = (score demandWidths d j,j.val) := by
  let b := fun e : Bool × Fin (mPort a) × Fin (mPort a) =>
    demand (mPort a) C remaining block e.1 e.2.1.val e.2.2.val
  let x := fun e => w (addr (arrival G (tagOrdinal a).symm) z e)
  have hx : (fun e => V (b e)) = x := by
    funext e
    simp only [b,x,demand_value,hrem,hblock,demand_read G stored]
  have fits := chooseFields_fits data mem vs b d
    (fun e => demand_fits data mem vs G C remaining block z e.1 e.2.1 e.2.2 w stored
      hrem hblock hbr hrr hbc hpc hrc hf hw hc) (by rw [hx]; exact hs) (by rw [hx]; exact hd)
  have h := refreshChoice_value G W data mem vs C remaining block z w stored hrem hblock d
  let j := tileNumber x d
  have fst : V (chooseFields b d).1 = score x d j := congrArg Prod.fst h
  have snd : V (chooseFields b d).2 = j.val := congrArg Prod.snd h
  have cv : score x d j ≤ sentinel x := by
    apply Finset.sup_le
    intro e _
    by_cases hd0 : d j e = 0
    · simp only [need,hd0,ite_true]
      split <;> omega
    · have one : x e ≤ ∑ i, x i :=
        Finset.single_le_sum (f := x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
      have lt : x e < sentinel x := by dsimp only [sentinel]; omega
      exact ((need_le_iff lt).mpr (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hd0))).trans lt.le
  change ((EV (chooseFields b d).1).val,(EV (chooseFields b d).2).val) = _
  rw [Formula.value_eq_natural _ data mem vs fits.1,Formula.value_eq_natural _ data mem vs fits.2,
    fst,snd,Fin.val_cast_of_lt (cv.trans_lt hs),Fin.val_cast_of_lt (by omega : j.val<2^W)]

/-- An exact constant bound for the two fixed ROM fragments, uniform in word
width and every field of the particular opening. -/
theorem choice_steps {r : ℕ} (registers : Param → Fin r) (C : Columns (Formula n))
    (remaining block : Formula n) (d : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ) :
    let out := refreshChoice C remaining block d
    ((out.1.compile registers : Term W r n)).steps + ((out.2.compile registers : Term W r n)).steps =
      2*(out.1.work+out.2.work)+2 := by
  dsimp only
  rw [steps,steps]
  omega

end
end ThreeFlat.Diagonal.RefreshDemandRows

end OAI
