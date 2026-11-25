import OAI.Computability.MultitapeWeakETH.SwitchStage

/-! # Physical preparation of the switch column from its traversal ordinal and packet -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.SwitchFactor

open IntegerMultiplication Code Staff Carry Strip NearSquareRoot.Benes VPVNP Compression PairSimulation
open PackedSwitches SyntaxProgram SiteCheck
open private stages from OAI.Computability.MultitapeWeakETH.PackedFormula
noncomputable section

private abbrev reg : Regime (Tally × Tally) := ⟨size,send,Dom.base _⟩

/-- The quotient picks the base stage. The remainder is reversed to recover the logical lane order. -/
def coordinates (q : Tally × Tally) : Tally × Bits.Word :=
  (tally (q.2.length/2^q.1.length),(field (q.1,tally (q.2.length%2^q.1.length))).reverse)

theorem coordinates_poly : Poly coordinates := by
  have g : Realizes reg (fun q => q.1.length) := by
    change Poly (fun q : Tally × Tally => tally q.1.length)
    simpa only [recover_tally] using (Easy.fst (X:=Tally) (Y:=Tally)).poly
  have j : Realizes reg (fun q => q.2.length) := by
    change Poly (fun q : Tally × Tally => tally q.2.length)
    simpa only [recover_tally] using (Easy.snd (X:=Tally) (Y:=Tally)).poly
  have two := (Figure.natural (r:=reg) 2).repeated g
  have div := ((Figure.of_spoken j).quotients two).pay ((diameter _ j).mono (fun q => Nat.div_le_self ..))
  have rem := ((Figure.of_spoken j).modded two).pay ((diameter _ j).mono (fun q => Nat.mod_le ..))
  change Poly (fun q : Tally × Tally => tally (q.2.length/2^q.1.length)) at div
  change Poly (fun q : Tally × Tally => tally (q.2.length%2^q.1.length)) at rem
  exact div.pair ((Easy.fst.poly.pair rem).compose field_poly).rev

theorem coordinates_eq {a g r : ℕ} (v : (inputState a g r).network.Site) :
    coordinates (tally g,tally (((LocalHistory.siteOrder (inputState a g r)).entries.symm v).val)) =
      (tally v.1.val,laneBytes v.2) := by
  let k := bitWordFinEquiv g v.2
  have e : ((LocalHistory.siteOrder (inputState a g r)).entries.symm v).val = k.val+2^g*v.1.val := rfl
  simp only [coordinates,e,tally_length,Nat.add_mul_div_left _ _ (Nat.two_pow_pos g),Nat.div_eq_of_lt k.isLt,
    Nat.zero_add,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt k.isLt]
  exact congrArg (fun w => (tally v.1.val,w)) (laneField_eq v.2)

private def quarter (xs : Bits.Word) := (half (half (ruler xs)).1).1

private theorem quarter_poly : Poly quarter :=
  (((Easy.ruler Easy.identity).compose halfCost.fstCompose).compose halfCost.fstCompose).poly

private theorem quarter_eq {m a g l : ℕ} (ss : Fin (m+2) → Bool × ℕ) (ha : 2 ≤ 2^a)
    (v : site m g) (h : (state ss a g l).network.Half v) :
    quarter (NodeArguments.packed (state ss a g l) v h) = tally (2^l) := by
  rw [quarter,half_v,half_v]
  simp only [tally_length,ruler_length,packet_banks ss ha v h,List.length_append,List.length_ofFn]
  congr 1
  omega

abbrev ColumnArgs := ((Tally × Tally) × SwitchTables) × (Tally × Bits.Word)

def columnAt (q : ColumnArgs) : Bool × Column :=
  let (g,l) := q.1.1
  let d := g++l
  let (i,lane) := coordinates (g,q.2.1)
  let sk (j : Tally) : StageKey := (q.1.2,sideAxis (d,j))
  (Iter.small (i,[()]),((sk i,sk (prevIndex (d,i))),(g,l,lane),splitPacket (quarter q.2.2,q.2.2)))

theorem columnAt_poly : Poly columnAt := by
  have g : Poly (fun q : ColumnArgs => q.1.1.1) := by fun_prop
  have l : Poly (fun q : ColumnArgs => q.1.1.2) := by fun_prop
  have c := (g.pair (show Poly (fun q : ColumnArgs => q.2.1) by fun_prop)).compose coordinates_poly
  have d := g.app l
  have sk (j : ColumnArgs → Tally) (hj : Poly j) := (show Poly (fun q : ColumnArgs => q.1.2) by fun_prop).pair ((d.pair hj).compose sideAxis_poly)
  have p := (d.pair c.fstCompose).compose prevIndex_poly
  have zero := (c.fstCompose.pair (Code.Poly.const [()])).compose Iter.small_easy.poly
  have packet : Poly (fun q : ColumnArgs => q.2.2) := by fun_prop
  exact zero.pair (((sk _ c.fstCompose).pair (sk _ p)).pair ((g.pair (l.pair c.sndCompose)).pair
    (((packet.compose quarter_poly).pair packet).compose splitPacket_poly)))

theorem columnAt_eq {a g r : ℕ} (ha : 2 ≤ 2^a) (t : RawTable)
    (v : (inputState a g r).network.Site) (h : (inputState a g r).network.Half v) :
    let d := g+(r+2)
    let ss := stages d (by omega)
    let idx := ((LocalHistory.siteOrder (inputState a g r)).entries.symm v).val
    columnAt (((tally g,tally (r+2)),generateTables (tally d,t)),tally idx,NodeArguments.packed (inputState a g r) v h) =
      (decide (v.1.val=0),physicalColumn ss t v h) := by
  intro d ss idx
  simp only [columnAt,idx,coordinates_eq (a:=a) (g:=g) (r:=r) v]
  have depth : tally g ++ tally (r+2)=tally d := by
    rw [← recover_tally (tally g ++ tally (r+2))]
    simp [d]
  let s : Fin (2*d-2+2) := v.1
  rw [depth,prevIndex_eq (d:=d) (by omega) s,sideAxis_eq (d:=d) (by omega) s,sideAxis_eq (d:=d) (by omega) ((finRotate _).symm s)]
  have bits : quarter (NodeArguments.packed (inputState a g r) v h) = tally (2^(r+2)) := quarter_eq ss ha v h
  rw [bits]
  simp only [Iter.small,tally_length,List.length_singleton,Nat.lt_one_iff]
  rfl

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork.SwitchFactor
