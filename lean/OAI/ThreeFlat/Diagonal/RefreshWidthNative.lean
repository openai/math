import OAI.ThreeFlat.Diagonal.RefreshInputBounds
import OAI.ThreeFlat.Diagonal.RefreshWidthPhysical
import OAI.ThreeFlat.Diagonal.RefreshWidthFits

namespace OAI
/-! # Exact outgoing widths of the native refresh commit procedure -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.PhysicalPinsExpr
open RAM.MotifRows RefreshDemandRows RefreshTies CompressorPacking.Native MotifIntegerChoice Expander
open scoped Fin.CommRing BigOperators Classical
noncomputable section
set_option quotPrecheck false

variable {W v a t h pad : ℕ} {F : Type} [Field F]
    {c : Fin (mPort a) → Fin (mPort a) → ℕ} {H : ℝ}
    (current : Word W) (m : Memory W) (vs : Fin 1 → Word W)
local notation "N" => fun i => (m i).val
local notation "U" => fun (i : Fin 1) => (vs i).val
local notation "V" => Formula.natural W (fun _ => 0) N U

/-- The very row term installed between the adjacency publisher and the
sparse-column copier returns the exact finite-word label width of the
histogram branch, for each source-indexed successor edge. -/
theorem width_native
    (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (C : SlotImage.Columns) (split : ℕ) (w : SlotImage.RefreshInput v a t → ℕ)
    (s : Source current m G C split w) (stride : ℕ)
    (T : RefreshMotif.Table F c (1+h+pad) H) (rows : ∀ p, ∑ j,c p j=h)
    (e : LiveSlot (Fin v) (BitWord t) (mPort a) (1+h+pad))
    (x : T.Branch G (tagOrdinal a).symm (SlotImage.demandWidth w))
    (atEdge : (vs 0).val=info N current 19+nextIndex e)
    (laneFit : 2^t<2^W) (outFit : v*mPort a*(1+h+pad)*2^t≤2^W)
    (portFit : mPort a<2^W) (degreeFit : 1+h+pad<2^W) (rowsFit : T.last+1≤2^W)
    (countSpan : info N current 1+v*2^t*stride≤2^W)
    (alphabet : ∀ j, Fintype.card (T.block j).Alphabet≤ stride)
    (tileFit : ∀ j i, sentinel (fun i => SlotImage.demandWidth w
      (addr (arrival G (tagOrdinal a).symm) (e.1.1.1,e.2) i))+T.base j i<2^W)
    (hist : ∀ (u : Block v t) (i : Fin (Fintype.card (T.entry G (tagOrdinal a).symm
      (SlotImage.demandWidth w) u).Alphabet)),
      (m (info N current 1+blockId u*stride+i.val)).val=((x u).val ((Fintype.equivFin _).symm i)).val) :
    (closed (generateWidth (input current) (field current 8) (index current 19) (field current 1)
      pad stride T.base (fun j => Fintype.card (T.block j).Alphabet)
      (fun j => (T.block j).bits) (poolOf T rows))).eval Fin.elim0 m vs =
      (freshWidth c rows (termWidth c (SlotImage.demandWidth w)
        (T.widths G (tagOrdinal a).symm (SlotImage.demandWidth w) x)) pad e : Word W) := by
  have idv : V (index current 19)=nextIndex e := by
    change (vs 0).val-info N current 19=_
    omega
  let z : Block v t := (e.1.1.1,e.2)
  have blockBound : blockId z < v*2^t := by
    change z.1.val*2^t+(tagOrdinal t z.2).val<v*2^t
    have b := Nat.mul_le_mul_right (2^t) z.1.isLt
    rw [Nat.succ_mul] at b
    omega
  have blockWord : blockId z<2^W := by
    apply blockBound.trans_le
    apply le_trans _ outFit
    have p := Nat.two_pow_pos a
    have d : 0<1+h+pad := by omega
    calc v*2^t ≤ v*((mPort a*(1+h+pad))*2^t) :=
           Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.mul_pos p d))
         _ = _ := by ac_rfl
  have region (j : Fin (T.last+1)) : info N current 1+blockId z*stride+Fintype.card (T.block j).Alphabet≤2^W := by
    have b := Nat.mul_le_mul_right stride blockBound
    rw [Nat.succ_mul] at b
    have := alphabet j
    omega
  have sentinelFit : sentinel (fun i=>SlotImage.demandWidth w (addr (arrival G (tagOrdinal a).symm) z i))<2^W := by
    dsimp only [z]
    exact (Nat.le_add_right _ _).trans_lt (tileFit 0 (false,0,0))
  have head := s.headerBound
  apply closed_read m vs
  · apply generateWidth_fits (fun _=>0) N U G (input current) (field current 8) (index current 19)
      (field current 1) pad stride T.base (fun j => Fintype.card (T.block j).Alphabet)
      (fun j => (T.block j).bits) (poolOf T rows) (SlotImage.demandWidth w) (s.demand vs)
      e s.remaining idv (field_fit current m vs 8 (by omega)) (index_fit current m vs 19 head)
      (field_fit current m vs 1 (by omega)) laneFit outFit portFit degreeFit blockWord rowsFit region
      (s.formulas vs) (s.widthRegion vs) (s.columnRegions vs) sentinelFit tileFit
  · exact generate_physical G (fun _=>0) N U T rows (input current) (field current 8) (index current 19)
      (field current 1) stride (SlotImage.demandWidth w)
      (s.demand vs) e s.remaining idv x hist

end
end ThreeFlat.Diagonal.RefreshStageNav

end OAI
