import OAI.ThreeFlat.Diagonal.RefreshInputBounds
import OAI.ThreeFlat.Diagonal.RefreshWidthFits

namespace OAI
/-! # The native refresh descriptor publishes the canonical choice triple -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.PhysicalPinsExpr RAM.MotifRows
open RefreshDemandRows RefreshTies CompressorPacking.Native MotifIntegerChoice
open scoped Fin.CommRing BigOperators Classical
noncomputable section

variable {W v a t k : ℕ} (current : Word W) (m : Memory W) (vs : Fin 1 → Word W)
set_option quotPrecheck false
local notation "N" => fun i => (m i).val
local notation "U" => fun (i : Fin 1) => (vs i).val
local notation "V" => Formula.natural W (fun _ => 0) N U
local notation "Fit" => Formula.Fits W (fun _ => 0) N U

theorem choice_native
    (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (C : SlotImage.Columns) (split : ℕ) (w : SlotImage.RefreshInput v a t → ℕ)
    (s : Source current m G C split w) (z : Block v t) (f : Fin 3)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ) (size : Fin (k+1) → ℕ)
    (start : (vs 0).val = info N current 2+blockId z*3+f.val)
    (laneFit : 2^t<2^W) (portFit : mPort a≤2^W) (rowsFit : k+1≤2^W)
    (tileFit : ∀ j i, sentinel (fun i => SlotImage.demandWidth w
      (addr (arrival G (tagOrdinal a).symm) z i))+base j i<2^W) :
    let d := fun i => SlotImage.demandWidth w (addr (arrival G (tagOrdinal a).symm) z i)
    let j := tileNumber d base
    (closed (choiceWords current base size)).eval Fin.elim0 m vs =
      ((if f.val=0 then score d base j else if f.val=1 then j.val else size j : ℕ) : Word W) := by
  let idx := index current 2
  let row := Formula.op .div idx (.lit 3)
  let member := Formula.op .mod idx (.lit 3)
  have head := s.headerBound
  have fi : Fit idx := index_fit current m vs 2 (by omega)
  have bound : V idx<2^W := (Nat.sub_le _ _).trans_lt (vs 0).isLt
  have three : 3<2^W := by omega
  have fr : Fit row := ⟨fi,trivial,bound,three⟩
  have fm : Fit member := ⟨fi,trivial,bound,three⟩
  have br : V row<2^W := (Nat.div_le_self ..).trans_lt bound
  have bm : V member<2^W := (Nat.mod_le ..).trans_lt bound
  have index_eq : V idx = blockId z*3+f.val := by change (vs 0).val-info N current 2=_; omega
  have q : V row=blockId z := by
    change V idx/3=_
    rw [index_eq,Nat.mul_comm (blockId z),Nat.mul_add_div (by decide),Nat.div_eq_of_lt f.isLt,Nat.add_zero]
  let d := fun i => SlotImage.demandWidth w (addr (arrival G (tagOrdinal a).symm) z i)
  let b := fun i : Bool × Fin (mPort a) × Fin (mPort a) =>
    demand (mPort a) (input current) (field current 8) row i.1 i.2.1.val i.2.2.val
  have fb (i) : Fit (b i) :=
    demand_fits (fun _=>0) N U G _ _ _ z i.1 i.2.1 i.2.2 _ (s.demand vs) s.remaining q fr
      (field_fit current m vs _ (by omega)) br portFit laneFit (s.formulas vs) (s.widthRegion vs) (s.columnRegions vs)
  have remWord : V (field current 8) = 2^t := s.remaining
  have bv : (fun i => V (b i))=d := by
    funext i
    simp only [b,d,demand_value,remWord,q]
    exact demand_read G (s.demand vs) z i.1 i.2.1 i.2.2
  have sd : sentinel d<2^W :=
    (Nat.le_add_right (sentinel d) (base 0 (false,0,0))).trans_lt (tileFit 0 (false,0,0))
  have fields := chooseFields_fits (fun _=>0) N U b base fb (bv ▸ sd) (bv ▸ tileFit)
  let j := tileNumber d base
  let code := refreshChoice (input current) (field current 8) row base
  have key : V code.2=j.val :=
    congrArg Prod.snd (refreshChoice_value G W (fun _=>0) N U (input current) (field current 8)
      row z (SlotImage.demandWidth w) (s.demand vs) remWord q base)
  dsimp only
  apply closed_read m vs
  · refine ⟨fm,trivial,bm,Nat.two_pow_pos _,?_⟩
    split
    · exact fields.1
    · refine ⟨fm,trivial,bm,(by change 1<2^W; omega),?_⟩
      split
      · exact fields.2
      · exact rowAt_fit (fun _=>0) N U _ code.2 fields.2 (key ▸ j.isLt.trans_le rowsFit) rowsFit (fun _=>trivial)
  · exact choice_read current (fun _=>0) N U G base size _ z f (s.demand vs) s.remaining start


end
end ThreeFlat.Diagonal.RefreshStageNav

end OAI
