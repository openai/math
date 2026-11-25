import OAI.ThreeFlat.Diagonal.RefreshPartyAddress
import OAI.ThreeFlat.Diagonal.RefreshDemandFits

namespace OAI
/-! # Word-address bounds for old and bundled refresh-party pin fields -/

namespace ThreeFlat.Diagonal.RefreshParty

open Computability.VPVNP.Compression RAM RAM.PhysicalPinsExpr RAM.MotifRows CompressorPacking.Native RefreshDemandRows
open scoped Classical BigOperators
noncomputable section

variable {W n v a t : ℕ} (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
local notation "V" => Formula.natural W data mem vs
local notation "Fit" => Formula.Fits W data mem vs

private def Same (f g : Formula n) := V f=V g ∧ (Fit f ↔ Fit g)

private theorem reflF (f : Formula n) : Same (W:=W) data mem vs f f := ⟨rfl,Iff.rfl⟩

private theorem binaryF (op : Computability.VPVNP.BurstRAM.PrivateRAM.BinaryOp) {x y x' y' : Formula n}
    (hx : Same (W:=W) data mem vs x x') (hy : Same (W:=W) data mem vs y y') :
    Same (W:=W) data mem vs (.op op x y) (.op op x' y') := by
  simpa only [Same,Formula.Fits,Formula.natural,hx.1,hy.1,hx.2,hy.2] using
    (reflF (W:=W) data mem vs (.op op x' y'))

private theorem loadF {x y : Formula n} (h : Same (W:=W) data mem vs x y) :
    Same (W:=W) data mem vs (.load x) (.load y) := by
  simp [Same,Formula.Fits,Formula.natural,h.1,h.2]

private theorem staticF {x : Formula n} {i : ℕ} (xi : V x=i) (f : Fit x) :
    Same (W:=W) data mem vs x (.lit i) := ⟨xi,iff_of_true f trivial⟩

theorem coordinates_fit (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (C : Columns (Formula n)) (rem block : Formula n) (z : Block v t) (dir : Bool)
    (ix sl : Formula n) (i s : Fin (mPort a)) (w : Address' v a t → ℕ)
    (stored : Stored G (C.map V) mem w) (ir : V ix=i.val) (sr : V sl=s.val)
    (ixFit : Fit ix) (slFit : Fit sl)
    (hrem : V rem=2^t) (hblock : V block=blockId z)
    (hbr : Fit block) (hrr : Fit rem) (hbc : V block<2^W) (hpc : mPort a≤2^W) (hrc : 2^t<2^W)
    (hf : Fit C.widths ∧ Fit C.sourceBase ∧ Fit C.sourceSlot ∧ Fit C.portShift ∧ Fit C.laneShift)
    (hw : V C.widths+v*mPort a*(mPort a*2^t) ≤ 2^W)
    (hc : ∀ c ∈ [C.sourceBase,C.sourceSlot,C.portShift,C.laneShift], V c+v*mPort a≤2^W) :
    Fit (coordinates (mPort a) C rem block dir ix sl) ∧ V (coordinates (mPort a) C rem block dir ix sl)<2^W := by
  have hx := staticF data mem vs ir ixFit
  have hs := staticF data mem vs sr slFit
  let row := coordinates (mPort a) C rem block dir ix sl
  have obs : Same (W:=W) data mem vs (.load row) (demand (mPort a) C rem block dir i.val s.val) := by
    cases dir <;> dsimp only [row,coordinates,demand,readColumn,wordAddress,plus,Bool.false_eq_true,ite_false,ite_true]
    all_goals repeat first | exact hx | exact hs | exact reflF data mem vs _ |
      apply loadF data mem vs | apply binaryF data mem vs
  exact obs.2.mpr (demand_fits data mem vs G C rem block z dir i s w stored
    hrem hblock hbr hrr hbc hpc hrc hf hw hc)

theorem before_fit (m : ℕ) (base address : Formula n) (offset : ℕ) (j : Fin m)
    (hb : Fit base) (ha : Fit address) (bb : V base<2^W) (ab : V address<2^W)
    (mb : m<2^W) (start : V address=V base+offset*m+j.val) (span : V base+offset*m+m≤2^W) :
    Fit (bundleBefore m base address) := by
  let port := Formula.op .mod (.cut address base) (.lit m)
  have fd : Fit (.cut address base) := ⟨ha,hb,ab,bb⟩
  have fp : Fit port := ⟨fd,trivial,(Nat.sub_le _ _).trans_lt ab,mb⟩
  have rank : V port=j.val := by
    change (V address-V base)%m=j.val
    have sub : V address-V base=offset*m+j.val := by omega
    rw [sub,Nat.mul_comm offset,Nat.mul_add_mod,Nat.mod_eq_of_lt j.isLt]
  have bf : Fit (.cut address port) := ⟨ha,fp,ab,rank ▸ j.isLt.trans mb⟩
  let summand := fun q : Fin m => Formula.select .lt (.lit q.val) port
    (.load (plus (.cut address port) (.lit q.val))) (.lit 0)
  have each (q : Fin m) : Fit (summand q) := by
    refine ⟨trivial,fp,q.isLt.trans mb,rank ▸ j.isLt.trans mb,?_⟩
    split
    · refine ⟨⟨bf,trivial,trivial⟩,?_⟩
      change V address-V port+q.val<_
      omega
    · trivial
  have total (l : List (Fin m)) : Fit (totals (l.map summand)) := by
    induction l with
    | nil => trivial
    | cons x l ih => exact ⟨each x,ih,trivial⟩
  exact total _

end
end ThreeFlat.Diagonal.RefreshParty

end OAI
