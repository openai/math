import OAI.Hierarchy.DescentOriginalEpochSheetCharge
import OAI.Hierarchy.DescentWideSeedCalendarFee
import OAI.Hierarchy.DescentPackedEpochPins

namespace OAI
/-! # Lane-sized word, fixed ROM, and complete physical epoch admission bill -/
namespace Hierarchy.DescentPackedEpochShelves
open DescentTerminalEpochChart DescentPackedProfileTape DescentPackedProfileValidity DescentPackedProfileInstall
open DescentPackedEpochFold DescentTerminalEpochDecoder DescentSIMDLookup
open scoped Classical BigOperators
noncomputable section
variable {A : Type}

theorem phase_rows (head C r : ℕ) (count exterior : ℕ→ℕ) (out : ℕ) (ps : List (Shelf A)) :
    (phases head C r count exterior out ps).map rows=ps.map fun p=>slots p.src.seats r := by
  induction ps generalizing out with | nil=>rfl | cons s ss ih=>simp [phases,rows,ih]

theorem invoice (lo C w seed : ℕ) (ss : List (Source A)) (count exterior : ℕ→ℕ) (wide : 2*unit C ≤ w) :
    let r:=grain w C
    bill seed (final lo C r ss) (controls lo C r ss count exterior)*w ≤
      64*w+578*ss.length*w+680*seatBill ss*unit C := by
  let r:=grain w C
  let ps:=shelves r lo 0 ss
  let ts:=controls lo C r ss count exterior
  change bill seed (final lo C r ss) ts*w ≤ _
  rw [bill_eq]
  have eqn : ts.map rows=ss.map fun s=>slots s.seats r := by
    change (phases (lo+extent r ss) C r count exterior (end_ (lo+extent r ss) C r) ps).map rows=_
    rw [phase_rows]
    have srcs : ps.map Shelf.src = ss := sources r lo 0 ss
    simpa only [List.map_map,Function.comp_def] using
      congrArg (fun xs : List (Source A) => xs.map (fun s => slots s.seats r)) srcs
  have len : ts.length=ss.length:=by simpa only [List.length_map] using congrArg List.length eqn
  change (64+238*ts.length+170*(ts.map rows).sum)*w≤_
  rw [len,eqn]
  have bounds:=chunks_charge w C ss wide
  change (ss.map fun s=>slots s.seats r).sum*w ≤ _ at bounds
  nlinarith only [bounds]

theorem rom (C w : ℕ) : tariff C (grain w C) ≤ 2^(w/2) := by
  apply (tariff_le C (grain w C)).trans
  apply Nat.pow_le_pow_right (by decide)
  change unit C * grain w C ≤ w/2
  rw [Nat.mul_comm]
  exact lanes_fit w (unit C)


theorem output_rows (r lo j : ℕ) (ss : List (Source A)) :
    ((shelves r lo j ss).map (stepRows r)).sum = (ss.map fun s=>slots s.seats r).sum+2*ss.length := by
  induction ss generalizing lo j with
  | nil=>rfl
  | cons s ss ih=>
    simp only [shelves,List.map_cons,List.sum_cons,stepRows,List.length_cons,ih]
    omega

/-- The physical end address includes every dyadic source and index bank, the
one shared literal dictionary, every mutable row scratch word and the verdict. -/
theorem final_address (lo C w : ℕ) (ss : List (Source A)) :
    let r:=grain w C
    final lo C r ss+1 ≤ lo+5*(ss.map fun s=>slots s.seats r).sum+4*ss.length+
      2*(r+1)+2*2^(w/2)+3 := by
  let r:=grain w C
  have high:=DescentPackedProfileInstall.extent (lo+extent r ss) C r
  have shared : 2^(unit C*r) ≤ 2^(w/2) := by
    apply Nat.pow_le_pow_right (by decide)
    rw [Nat.mul_comm (unit C) r]
    exact lanes_fit w (unit C)
  have spans:=extent_le r ss
  change end_ (lo+extent r ss) C r+((shelves r lo 0 ss).map (stepRows r)).sum+1 ≤
    lo+5*(ss.map fun s=>slots s.seats r).sum+4*ss.length+2*(r+1)+2*2^(w/2)+3
  rw [output_rows]
  change end_ (lo+extent r ss) C r ≤ lo+extent r ss+(2*(r+1)+1)+(2*2^(unit C*r)+1) at high
  omega


end
end Hierarchy.DescentPackedEpochShelves

end OAI
