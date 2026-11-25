import OAI.Computability.NearSquareRoot.CRTControlledBenesRun

/-! # Charged switch-bit lookup in the emitted Beneš tables

The program selects a layer by its unary depth, then looks up the current bit
string in that layer. An absent layer or address yields the clear control bit.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes
open IntegerMultiplication.Code

abbrev SwitchTables := List (List (List Bool × Bool × Bool))

/-- The encoded input contains the emitted tables, the side, the depth and the address. -/
def switchBit (q : SwitchTables × Bool × Tally × List Bool) : Bool :=
  let s := (q.1[q.2.2.1.length]?.bind (fun l => l.lookup q.2.2.2)).getD (false,false)
  if q.2.1 then s.2 else s.1

private abbrev Layer := List (List Bool × Bool × Bool)
private abbrev ReadInput := SwitchTables × Bool × Tally × List Bool

/-- Reuse the charged word-key label lookup by placing the selected switch column
in the label's Boolean field. -/
private def asLabels (side : Bool) (rows : Layer) : Labels (List Bool) :=
  rows.map (fun r => (r.1,[],if side then r.2.2 else r.2.1))

private theorem asLabels_poly (side : Bool) : Poly (asLabels side) := by
  apply Poly.maps
  cases side
  · exact Easy.fst.poly.pair ((IntegerMultiplication.Code.Poly.const []).pair (Easy.snd.compose Easy.fst).poly)
  · exact Easy.fst.poly.pair ((IntegerMultiplication.Code.Poly.const []).pair (Easy.snd.compose Easy.snd).poly)

private theorem read_labels (side : Bool) (l : Layer) (x : List Bool) :
    (label (asLabels side l) x).2 =
      let r := (l.lookup x).getD (false,false)
      if side then r.2 else r.1 := by
  induction l with
  | nil => cases side <;> rfl
  | cons r l ih =>
    obtain ⟨k,v⟩ := r
    by_cases hx : x = k
    · simp [asLabels,label,hx]
    · simpa only [label,asLabels,List.map_cons,List.lookup_cons,Bool.beq_eq_decide_eq,decide_eq_false hx]
        using ih

/-- One fixed tape program reads either control bit at arbitrary depth and width. -/
theorem switchBit_poly : Poly switchBit := by
  have layer := (show Poly (fun q : ReadInput => (q.1,q.2.2.1)) by fun_prop).compose
    (Iter.facile ([] : Layer)).poly
  have col (side : Bool) := ((show Poly (fun q : ReadInput => q.2.2.2) by fun_prop).pair
    (layer.compose (asLabels_poly side))).compose (label_poly [] easyWordEq.poly).sndCompose
  convert Poly.choose (show Poly (fun q : ReadInput => q.2.1) by fun_prop) (col true) (col false) using 1
  funext q
  rcases q with ⟨tables,side,j,x⟩
  cases side <;> simp only [switchBit,Bool.cond_false,Bool.cond_true,Bool.false_eq_true,
    ite_true,ite_false,read_labels,Iter.pick,List.headD_eq_head?_getD,List.head?_drop] <;>
    cases tables[j.length]? <;> rfl

private theorem represented_key {d : ℕ} {p : Equiv.Perm (Word d)} {t : RawTable}
    (h : RawRepresents p t) (x : Word d) : List.ofFn x ∈ t.map Prod.fst := by
  obtain ⟨ks,_,ha,rfl⟩ := h
  exact List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨x,ha _,rfl⟩,rfl⟩

/-- A missing depth is the identity stage even for synchronized variable-width blocks. -/
theorem switchBit_generated {d : ℕ} {p : Equiv.Perm (Word d)} {t : RawTable}
    (h : RawRepresents p t) (side : Bool) (j : ℕ) (x : Word d) :
    switchBit (generateTables (tally d,t),side,tally j,List.ofFn x) =
      let c := rawSetting t j (List.ofFn x)
      if j < d then (if side then c.2 else c.1) else false := by
  by_cases hj : j < d
  · simp only [switchBit,rawSetting,tally_length,generated_lookup t hj _ (represented_key h x),Option.getD_some,ite_eq_left hj]
  · have he : (generateTables (tally d,t))[j]? = none := List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hj)
    simp only [switchBit,tally_length,he,Option.bind_none,Option.getD_none,ite_eq_right hj,ite_self]

theorem switchBit_target_independent {d : ℕ} {p : Equiv.Perm (Word d)} {t : RawTable}
    (h : RawRepresents p t) (side : Bool) (j : Fin d) (x : Word d) (b : Bool) :
    switchBit (generateTables (tally d,t),side,tally j,List.ofFn (Function.update x j b)) =
      switchBit (generateTables (tally d,t),side,tally j,List.ofFn x) := by
  simp only [switchBit_generated h,rawSetting_update]

/-- The bit used by the guarded XOR stage is the bit that its tape lookup computes. -/
theorem stagePerm_switchBit {d : ℕ} {p : Equiv.Perm (Word d)} {t : RawTable}
    (h : RawRepresents p t) (side : Bool) (j : ℕ) (x : Word d) (k : Fin d) :
    stagePerm t side j x k =
      if j = k.val then x k ^^ switchBit (generateTables (tally d,t),side,tally j,List.ofFn x)
      else x k := by
  rw [stagePerm_apply,switchBit_generated h]
  by_cases he : j = k.val
  · simp [he,k.isLt]
  · simp [he]

end Benes

end NearSquareRoot
end Computability
end OAI
