import OAI.Computability.MultitapeWeakETH.SwitchBankReads

/-! # Tape lookup of a switch port and its inverse address -/

namespace OAI.Computability.MultitapeWeakETH.PackedSwitches

open IntegerMultiplication Code NearSquareRoot NearSquareRoot.Benes
open CNFNetwork.SiteCheck VPVNP
noncomputable section

abbrev StageKey := SwitchTables × Bool × Tally
abbrev SwitchQuery := StageKey × Bits.Word

def port (q : SwitchQuery) := switchBit (q.1.1,q.1.2.1,q.1.2.2,q.2)

theorem port_poly : Poly port :=
  (show Poly (fun q : SwitchQuery => (q.1.1,q.1.2.1,q.1.2.2,q.2)) by fun_prop).compose switchBit_poly

private def toggle (q : Tally × Bits.Word) : Bits.Word :=
  let split := cutLists q
  split.1 ++ split.2.modifyHead Bool.not

private theorem toggle_poly : Poly toggle := by
  have head : Easy (fun w : Bits.Word => w.modifyHead Bool.not) := by
    convert Easy.listCase [] (((Easy.fst.compose Iter.negate).pair Easy.snd).compose Easy.cons) using 1
    funext w
    cases w <;> rfl
  have cut : Easy (cutLists (X:=Bool)) := easy_cut Easy.identity
  exact cut.fstCompose.poly.app (cut.sndCompose.compose head).poly

private theorem toggle_eq (j : ℕ) (xs : Bits.Word) :
    toggle (tally j,xs) = xs.modify j Bool.not := by
  change xs.take (tally j).length ++ (xs.drop (tally j).length).modifyHead Bool.not = _
  rw [tally_length]
  induction j generalizing xs with
  | zero => cases xs <;> rfl
  | succ j ih => cases xs with
    | nil => rfl
    | cons x xs => simp [ih]

def move (q : SwitchQuery) : Bits.Word :=
  bif port q then toggle (q.1.2.2,q.2) else q.2

theorem move_poly : Poly move :=
  Poly.choose port_poly ((show Poly (fun q : SwitchQuery => (q.1.2.2,q.2)) by fun_prop).compose toggle_poly) Easy.snd.poly

variable {g l : ℕ} {t : RawTable} {p : Equiv.Perm (Word (g+l))} (repr : RawRepresents p t)
  (side : Bool) (j : ℕ) (hj : j < g+l)

def key (d : ℕ) (t : RawTable) (side : Bool) (j : ℕ) : StageKey := (generateTables (tally d,t),side,tally j)

include repr hj

theorem port_eq (x : Word (g+l)) :
    port (key (g+l) t side j,List.ofFn x) = flips t side j x := by
  simp only [port,key,flips,switchBit_generated repr,ite_eq_left hj]

theorem move_eq (x : Word (g+l)) :
    move (key (g+l) t side j,List.ofFn x) = List.ofFn ((stagePerm t side j).symm x) := by
  rw [stagePerm_selfInverse,ofFn_stagePerm]
  unfold move
  rw [port_eq repr side j hj]
  change (bif flips t side j x then toggle (tally j,List.ofFn x) else List.ofFn x) =
    (List.ofFn x).modify j (fun b => b ^^ flips t side j x)
  cases e : flips t side j x
  · simp
    exact (List.modify_id j _).symm
  · simp [toggle_eq]

end
end OAI.Computability.MultitapeWeakETH.PackedSwitches
