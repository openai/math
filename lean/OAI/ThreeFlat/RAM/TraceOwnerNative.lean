import OAI.ThreeFlat.RAM.TraceOwnerDecode
import OAI.ThreeFlat.Diagonal.TraceSourceCapacity
import Mathlib.Tactic.FinCases

namespace OAI
/-! # Direct native owner and reservation lookup with fixed shape literals -/

namespace ThreeFlat.RAM.TraceOwnerFormula

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr DescriptorExpr
open Diagonal.TraceSourceOwner
open scoped Fin.CommRing BigOperators

def args {W k n : ℕ} (s : Shape) (word : ℕ) (x y : Term W k n) : Fin 18 → Term W k n :=
  ![x,y,.literal s.header,.literal word,.literal s.cpu,.literal s.rows,.literal s.track,
    .literal s.edge,.literal s.copy,.literal s.gates,.literal (s.header*word),.literal (s.ticks*s.cpu),
    .literal (s.layers*(s.rows*s.track)),.literal ((s.rows-1)*s.edge : ℕ),.literal (s.rows*s.copy),
    .literal (s.rows*s.track),.literal (s.layers*s.track),.literal (2*s.cpu)]

/-- No shape-sized public table is needed, only sixteen fixed scalar literals. -/
def direct {W n : ℕ} (q : Output) (s : Shape) (word : ℕ) (x y : Term W 1 n) : Term W 1 n :=
  term q (fun _ => 0) (args s word x y)

theorem direct_binds {W n : ℕ} (q : Output) (s : Shape) (word : ℕ) (x y : Term W 1 n) :
    (direct q s word x y).binds = (formula q).work + (x.binds+y.binds+16) := by
  rw [direct,term_binds]
  apply congrArg ((formula q).work + ·)
  simp [args,Fin.sum_univ_succ,Term.literal,Term.binds]
 ; omega

theorem direct_eval {W n b : ℕ} (q : Output) (s : Shape) (word xv yv : ℕ) (x y : Term W 1 n)
    (data : Fin 1 → Word W) (m : Memory W) (input : Fin n → Word W)
    (hx : x.eval data m input=(xv : Word W)) (hy : y.eval data m input=(yv : Word W))
    (smallArg : ∀ i, vars s word xv yv i < 2^b) (margin : 5*b+128 ≤ W) :
    (direct q s word x y).eval data m input =
      ((formula q).natural W (fun _ => 0) (fun _ => 0) (vars s word xv yv) : Word W) := by
  refine term_eval q (fun _ => 0) (args s word x y) data m input (vars s word xv yv) ?_ smallArg margin
  intro i
  fin_cases i <;> simp [args,vars,hx,hy]

def verifyArgs {W n : ℕ} (s : Shape) (word : ℕ) (v slot : Term W 1 n) : Fin 6 → Term W 1 n :=
  let h := direct .reverse s word v slot
  ![h,.literal s.count,direct .row s word h (.literal 0),v,
    direct .slot s word h (.literal 0),slot]

/-- The success flag for a padded reservation, obtained using the reverse candidate,
its two forward coordinates, and the finite hidden-count check. -/
def validSlot {W n : ℕ} (s : Shape) (word : ℕ) (v slot : Term W 1 n) : Term W 1 n :=
  verify.instantiate (verifyArgs s word v slot)

theorem validSlot_binds {W n : ℕ} (s : Shape) (word : ℕ) (v slot : Term W 1 n) :
    (validSlot s word v slot).binds ≤ 60000+4*(v.binds+slot.binds) := by
  have hr := work_le .reverse
  have ho := work_le .row
  have hs := work_le .slot
  simp [validSlot,verifyArgs,Term.binds_instantiate,Fin.sum_univ_succ,direct_binds,
    verify_binds,Term.literal,Term.binds]
  omega

set_option maxHeartbeats 1200000 in
/-- Width checks for the two scalar inputs and the selected candidate suffice
to execute all the native comparisons. -/
theorem validSlot_eval {W n b : ℕ} (s : Shape) (word v j : ℕ) (ve je : Term W 1 n)
    (data : Fin 1 → Word W) (m : Memory W) (input : Fin n → Word W)
    (hv : ve.eval data m input=(v : Word W)) (hj : je.eval data m input=(j : Word W))
    (initial : ∀ i, vars s word v j i < 2^b)
    (forward : ∀ i, vars s word (unplace s v j) 0 i < 2^b)
    (bounds : ∀ i : Fin 6, (![unplace s v j,s.count,(locate s (unplace s v j)).1,
      v,(locate s (unplace s v j)).2,j] i) < 2^W) (margin : 5*b+128 ≤ W) :
    (validSlot s word ve je).eval data m input = ((decode s v j).isSome.toNat : Word W) := by
  let h := direct .reverse s word ve je
  have he : h.eval data m input = (unplace s v j : Word W) := by
    simpa [h,reverse_natural] using direct_eval .reverse s word v j ve je data m input hv hj initial margin
  have rr := direct_eval .row s word (unplace s v j) 0 h (.literal 0) data m input he (by simp) forward margin
  have ss := direct_eval .slot s word (unplace s v j) 0 h (.literal 0) data m input he (by simp) forward margin
  simp only [row_natural] at rr
  simp only [slot_natural] at ss
  rw [validSlot,Term.eval_instantiate]
  apply Eq.trans _ (verify_eval s v j data m bounds)
  apply congrArg
  funext i
  fin_cases i
  · exact he
  · exact Term.eval_literal _ data m input
  · exact rr
  · exact hv
  · exact ss
  · exact hj

/-- A physical row and slot share their width with the reverse candidate.
Both arithmetical passes use the same word margin. -/
theorem validSlot_eval_rect {W n b : ℕ} (s : Shape) (word v j : ℕ) (ve je : Term W 1 n)
    (data : Fin 1 → Word W) (m : Memory W) (input : Fin n → Word W)
    (hv : ve.eval data m input=(v : Word W)) (hj : je.eval data m input=(j : Word W))
    (initial : ∀ i, vars s word v j i < 2^b)
    (row : v<s.rows) (slot : j<s.stride) (capacity : s.count+s.rows*s.stride+1≤2^b)
    (margin : 5*b+128≤W) :
    (validSlot s word ve je).eval data m input = ((decode s v j).isSome.toNat : Word W) := by
  have h := (unplace_lt_capacity s row slot).trans_le capacity
  have forward (i) : vars s word (unplace s v j) 0 i < 2^b := by
    have hi := initial i
    fin_cases i <;> first | exact hi | exact h | exact Nat.two_pow_pos _
  have rr := output_lt .row _ margin forward
  have ss := output_lt .slot _ margin forward
  rw [row_natural] at rr
  rw [slot_natural] at ss
  have powW := Nat.pow_le_pow_right (n:=2) (by decide) margin
  have bw : b≤W := by omega
  have bound := Nat.pow_le_pow_right (n:=2) (by decide) bw
  have count : s.count<2^b := by omega
  refine validSlot_eval s word v j ve je data m input hv hj initial forward ?_ margin
  intro i
  fin_cases i <;> first | exact h.trans_le bound | exact count.trans_le bound | exact rr.trans_le powW |
    exact (initial 0).trans_le bound | exact ss.trans_le powW | exact (initial 1).trans_le bound

/-- It suffices to bound the original public shape and the two inputs. The
fixed arithmetic analyzer supplies bounds on the intermediate reverse candidate. -/
theorem validSlot_eval_bounded {W n b : ℕ} (s : Shape) (word v j : ℕ) (ve je : Term W 1 n)
    (data : Fin 1 → Word W) (m : Memory W) (input : Fin n → Word W)
    (hv : ve.eval data m input=(v : Word W)) (hj : je.eval data m input=(j : Word W))
    (initial : ∀ i, vars s word v j i < 2^b) (count : s.count<2^W)
    (margin : 5*(5*b+128)+128 ≤ W) :
    (validSlot s word ve je).eval data m input = ((decode s v j).isSome.toNat : Word W) := by
  let B := 5*b+128
  have bB : b≤B := by dsimp [B]; omega
  have BW : B≤W := by dsimp [B]; omega
  have h := output_lt .reverse (vars s word v j) BW initial
  rw [reverse_natural] at h
  have initB (i) : vars s word v j i < 2^B :=
    (initial i).trans_le (Nat.pow_le_pow_right (by decide) bB)
  have forward (i) : vars s word (unplace s v j) 0 i < 2^B := by
    have hi := initB i
    fin_cases i <;> first | exact hi | exact h | exact Nat.two_pow_pos _
  have rr := output_lt .row _ margin forward
  have ss := output_lt .slot _ margin forward
  rw [row_natural] at rr
  rw [slot_natural] at ss
  have powW := Nat.pow_le_pow_right (n:=2) (by decide) margin
  have vW := (initB 0).trans_le (Nat.pow_le_pow_right (by decide) BW)
  have jW := (initB 1).trans_le (Nat.pow_le_pow_right (by decide) BW)
  have hW := h.trans_le (Nat.pow_le_pow_right (by decide) BW)
  apply validSlot_eval s word v j ve je data m input hv hj initB forward _ margin
  intro i
  fin_cases i <;> first | exact hW | exact count | exact rr.trans_le powW | exact vW | exact ss.trans_le powW | exact jW

end ThreeFlat.RAM.TraceOwnerFormula

end OAI
