import OAI.ThreeFlat.Diagonal.RefreshPartyNative

namespace OAI
/-! # Full per-half logical word widths, on the same seven registers as the bit lookup -/

namespace ThreeFlat.Diagonal.RefreshParty

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.PhysicalPinsExpr RAM.MotifRows
open RefreshDemandRows RefreshTies CompressorPacking.Native
open scoped Classical Fin.CommRing
noncomputable section

def denseWidth (m : ℕ) (dir side : Bool) (other : F) : F :=
  .load (coordinates m inputs (stageField 8) (.load (.reg 2)) dir
    (if side then other else .reg 3) (if side then .reg 3 else other))

def sparseWidth (d : ℕ) (side : Bool) (other : F) : F :=
  let half := plus (.lit (1+(if side then d else 0))) other
  let flat := plus (.op .mul (.reg 1) (.lit (2*d))) half
  readColumn (stageField 40) (plus (.op .mul flat (.lit 4)) (.lit 2))

def width (m h pad : ℕ) (supply : Bool) : F :=
  let edge : F := .reg 4
  if supply then
    let j := Formula.op .mod edge (.lit h)
    .select .lt edge (.lit h) (sparseWidth (1+h+pad) false j) (sparseWidth (1+h+pad) true j)
  else
    let j := Formula.op .mod edge (.lit m)
    .select .lt edge (.lit m) (denseWidth m false false j)
      (.select .lt edge (.lit (2*m)) (denseWidth m false true j)
        (.select .lt edge (.lit (3*m)) (denseWidth m true false j) (denseWidth m true true j)))

variable {W v a t h pad : ℕ} (data : Param→ℕ) (mem : ℕ→ℕ) (vs : Fin 7→ℕ)
local notation "V" => Formula.natural W data mem vs

private theorem chooseWidth (m x j : ℕ) (dir side : Bool) (widthAt : Bool→Bool→ℕ)
    (bound : j < m) (position : x=((if dir then 2 else 0)+(if side then 1 else 0))*m+j) :
    (if decide (x < m) then widthAt false false else
      if decide (x<2*m) then widthAt false true else
      if decide (x<3*m) then widthAt true false else widthAt true true) = widthAt dir side := by
  cases dir <;> cases side <;> simp at position
  all_goals
    simp only [decide_eq_true_eq]
    split_ifs <;> first | rfl | omega

theorem dense_width_read (G : LiftedSlots (Fin v) (mPort a) (BitWord a×BitWord t)) (w : Address' v a t→ℕ)
    (st : RefreshDemandRows.Stored G (inputs.map V) mem w) (z : Block v t)
    (remain : V (stageField 8)=2^t) (block : mem (vs 2)=blockId z) (p j : Fin (mPort a)) (dir side : Bool)
    (party : vs 3=p.val) (edge : vs 4=((if dir then 2 else 0)+(if side then 1 else 0))*mPort a+j.val) :
    V (width (mPort a) h pad false)=w (addr (arrival G (tagOrdinal a).symm) z (denseEnds p (dir,side,j)).1.1) := by
  let other := Formula.op .mod (.reg 4 : F) (.lit (mPort a))
  have digit : V other=j.val := by
    change vs 4%mPort a=j.val
    rw [edge,Nat.mul_comm _ (mPort a),Nat.mul_add_mod,Nat.mod_eq_of_lt j.isLt]
  let e := (denseEnds p (dir,side,j)).1.1
  let i := addr (arrival G (tagOrdinal a).symm) z e
  have val : V (denseWidth (mPort a) dir side other)=w i := by
    change mem (V (coordinates _ _ _ _ dir _ _))=_
    rw [coordinates_read,remain]
    change mem (absAddress _ _ _ _ (mem (vs 2)) dir _ _)=_
    rw [block]
    cases side with
    | false =>
      change mem (absAddress _ _ _ _ _ dir (vs 3) (V other)) =
        w (addr (arrival G (tagOrdinal a).symm) z (dir,p,j))
      rw [party,digit,demand_address G st z dir p j,st.width]
    | true =>
      change mem (absAddress _ _ _ _ _ dir (V other) (vs 3)) =
        w (addr (arrival G (tagOrdinal a).symm) z (dir,j,p))
      rw [party,digit,demand_address G st z dir j p,st.width]
  exact (chooseWidth (mPort a) (vs 4) j.val dir side
    (fun d s => V (denseWidth (mPort a) d s other)) j.isLt edge).trans val

theorem sparse_width_read (j : Fin h) (side : Bool)
    (edge : vs 4=(if side then h else 0)+j.val) :
    V (width (mPort a) h pad true)=
      mem (V (stageField 40)+(vs 1*(2*(1+h+pad))+(1+(if side then 1+h+pad else 0)+j.val))*4+2) := by
  cases side <;> simp [width,sparseWidth,readColumn,plus,Formula.natural,natOp,natTest,
    edge,j.isLt,Nat.add_mod_left,Nat.mod_eq_of_lt j.isLt,Nat.add_assoc]


end
end ThreeFlat.Diagonal.RefreshParty

end OAI
