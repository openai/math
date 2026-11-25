import OAI.ThreeFlat.Diagonal.RefreshPartyMeaning

namespace OAI
/-! # Native source scopes for the selected refresh party -/

namespace ThreeFlat.Diagonal.RefreshParty

open Computability.VPVNP.BurstRAM Computability.VPVNP.Compression RAM RAM.PhysicalPinsExpr RAM.MotifRows LinearAlgebra.SpectralBooks
open CompressorPacking.Native RefreshDemandRows RefreshTies MotifIntegerChoice
open scoped Classical BigOperators
noncomputable section

variable {W v a t h pad : ℕ} (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin 7 → ℕ)

def component (a : Location ℕ) (k : ℕ) := if k=0 then a.scope else if k=1 then a.child else if k=2 then a.half else a.bit

theorem member_read (a : Location F) : (Formula.natural W data mem vs) (member a)=component (a.map (Formula.natural W data mem vs)) (vs 6) := by
  by_cases zero : vs 6 = 0
  · simp [member,component,Location.map,Formula.natural,natTest,zero]
  by_cases one : vs 6 = 1
  · simp [member,component,Location.map,Formula.natural,natTest,one]
  by_cases two : vs 6 = 2 <;>
    simp [member,component,Location.map,Formula.natural,natTest,zero,one,two]

private theorem location_read (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (w : Address' v a t → ℕ) (st : Stored G (inputs.map (Formula.natural W data mem vs)) mem w) (z : Block v t)
    (remain : (Formula.natural W data mem vs) (stageField 8)=2^t) (block : mem (vs 2)=blockId z) (p j : Fin (mPort a))
    (dir side : Bool) (other : F) (party : vs 3=p.val) (partner : (Formula.natural W data mem vs) other=j.val) :
    (denseLoc (mPort a) (1+h+pad) dir side other).map (Formula.natural W data mem vs) =
      demandLocation (h:=h) (pad:=pad) (arrival G (tagOrdinal a).symm) w z p (denseEnds p (dir,side,j)) (vs 5) := by
  let e := (denseEnds p (dir,side,j)).1.1
  let id := addr (arrival G (tagOrdinal a).symm) z e
  let r := coordinates (mPort a) inputs (stageField 8) (.load (.reg 2)) dir
    (if side then other else .reg 3) (if side then .reg 3 else other)
  have addrOK : (Formula.natural W data mem vs) r = (Formula.natural W data mem vs) inputs.widths+index id := by
    rw [coordinates_read,remain]
    change absAddress _ _ _ _ (mem (vs 2)) dir _ _=_
    rw [block]
    cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true,Formula.natural,party,partner,
      id,e,denseEnds,Equiv.coe_fn_mk,demand_address G st] <;> rfl
  have width : mem ((Formula.natural W data mem vs) r)=w id := by
    rw [addrOK]
    exact st.width id
  have pre := bundle_read data mem vs inputs G w st id r addrOK
  cases side <;> cases dir <;>
    simp_all [Location.map,denseLoc,demandLocation,denseEnds,Formula.natural,natTest,plus,natOp,e,id,r,addr]

theorem demand_lookup (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (w : Address' v a t → ℕ) (st : Stored G (inputs.map (Formula.natural W data mem vs)) mem w) (z : Block v t)
    (remain : (Formula.natural W data mem vs) (stageField 8)=2^t) (block : mem (vs 2)=blockId z) (p j : Fin (mPort a))
    (dir side : Bool) (party : vs 3=p.val)
    (edge : vs 4=((if dir then 2 else 0)+(if side then 1 else 0))*mPort a+j.val) :
    (Formula.natural W data mem vs) (lookup (mPort a) h pad false)=component (demandLocation (h:=h) (pad:=pad)
      (arrival G (tagOrdinal a).symm) w z p (denseEnds p (dir,side,j)) (vs 5)) (vs 6) := by
  let partner : F := .op .mod (.reg 4) (.lit (mPort a))
  have key : (Formula.natural W data mem vs) partner=j.val := by
    change vs 4%mPort a=j.val
    rw [edge,Nat.mul_comm _ (mPort a),Nat.mul_add_mod,Nat.mod_eq_of_lt j.isLt]
  have meaning := congrArg (fun q => component q (vs 6))
    (location_read (h:=h) (pad:=pad) data mem vs G w st z remain block p j dir side partner party key)
  cases dir <;> cases side <;>
    simp only [lookup,Bool.false_eq_true,ite_false,member_read,Formula.natural,natTest] <;> split_ifs at * <;> first | exact meaning | simp_all <;> omega

theorem supply_lookup (degree : ℕ) (j : Fin h) (side : Bool) (width : ℕ)
    (key : vs 4=(if side then h else 0)+j.val)
    (word : mem ((Formula.natural W data mem vs) (stageField 40)+(vs 1*(2*degree)+(1+(if side then degree else 0)+j.val))*4+2)=width)
    (deg : degree=1+h+pad) :
    (Formula.natural W data mem vs) (lookup (mPort a) h pad true) = component
      ⟨if vs 5<width then 2 else 0,0,1+(if side then degree else 0)+j.val,vs 5⟩ (vs 6) := by
  subst degree
  have mod : vs 4%h=j.val := by
    cases side <;> simp [key,Nat.add_mod_left,Nat.mod_eq_of_lt j.isLt]
  have test : (vs 4<h) ↔ side=false := by cases side <;> simp_all
  cases side <;> simp [lookup,member_read,Location.map,sparseLoc,Formula.natural,natOp,natTest,readColumn,plus,
    key,j.isLt,Nat.not_lt_of_ge (Nat.le_add_right _ _),Nat.add_mod_left,Nat.mod_eq_of_lt j.isLt,Nat.add_assoc] at *
  all_goals rw [word]


end
end ThreeFlat.Diagonal.RefreshParty

end OAI
