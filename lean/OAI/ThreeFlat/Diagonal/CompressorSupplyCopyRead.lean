import OAI.ThreeFlat.Diagonal.CompressorSupplyDispatch

namespace OAI
/-! # Resolving an issued bit to its actual balanced copy with native words -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins
open Computability.VPVNP.BurstRAM PrivateRAM RAM.PhysicalPinsExpr RAM.DescriptorExpr Placement
open scoped Fin.NatCast BigOperators

variable {w n : ℕ} (data : Param → Word w) (mem : Memory w) (vs : Fin n → Word w)
local notation "V" => Formula.value data mem vs

theorem locate_word (pre post : List (F n × (F n → Address n))) (len : F n)
    (resolve : F n → Address n) (atBit : F n) (col : Fin 4) (j : ℕ) (answer : Word w)
    (index : (V atBit).val=(pre.map (fun z=>(V z.1).val)).sum+j) (within : j<(V len).val)
    (read : ∀x : F n,(V x).val=j → V (resolve x col)=answer) :
    V (locate (pre++(len,resolve)::post) atBit col)=answer := by
  induction pre generalizing atBit with
  | nil =>
    have atJ : (V atBit).val=j := by simpa using index
    have less : V atBit<V len := Fin.lt_def.mpr (by rw [atJ];exact within)
    simpa [locate,Formula.value,Comparison.test,less] using read atBit atJ
  | cons pair pre ih =>
    rcases pair with ⟨part,body⟩
    simp only [List.map_cons,List.sum_cons] at index
    have le : V part≤V atBit := Fin.le_def.mpr (by omega)
    have sub : (V (.cut atBit part)).val = (V atBit).val-(V part).val := by
      simp [Formula.value,Comparison.test,not_lt.mpr le,BinaryOp.eval,Fin.sub_val_of_le le]
    simp only [List.cons_append,locate,Formula.value,Comparison.test,decide_eq_true_eq,
      ite_eq_right (not_lt.mpr le)]
    apply ih
    rw [sub]
    omega

theorem prefix_piece (b m a : ℕ) (bound : a≤m) :
    (((List.finRange m).take a).map (SlotEnergy.piece b m)).sum =
      a*(b/m)+min a (b%m) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have last : a<(List.finRange m).length := by simpa using bound
    rw [List.take_succ_eq_append_getElem last,List.map_append,List.sum_append,ih (by omega)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,List.getElem_finRange,
      SlotEnergy.piece,Nat.succ_mul]
    change a*(b/m)+min a (b%m)+(b/m+(if a<b%m then 1 else 0)) =
      a*(b/m)+b/m+min (a+1) (b%m)
    by_cases small : a<b%m
    · rw [ite_eq_left small, Nat.min_eq_left (Nat.le_of_lt small), Nat.min_eq_left small]
      omega
    · have past : b%m≤a := Nat.le_of_not_gt small
      rw [ite_eq_right small, Nat.min_eq_right past, Nat.min_eq_right (Nat.le.step past)]
      omega

theorem crossing_bit_congr (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n))
    (party : F n) (t : Fin 4) (copy : Fin (S.pieces t)) (a b : F n) (eqv : V a=V b) (col : Fin 4) :
    V (crossing ptr S lay e party t copy a col)=V (crossing ptr S lay e party t copy b col) := by
  fin_cases col <;> first | rfl | exact eqv

theorem supply_copy_word (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n))
    (party size j : F n) (t : Fin 4) (copy : Fin (S.pieces t)) (b : ℕ)
    (localBit : Fin (SlotEnergy.piece b (S.pieces t) copy)) (hb : b<2^w) (count : S.pieces t<2^w)
    (sized : V size=(b:Word w))
    (bit : (V j).val=(SlotEnergy.pieceIndex b (S.pieces t) (by have:=copy.isLt;omega) ⟨copy,localBit⟩).val)
    (col : Fin 4) : V (locate (supplyCopies ptr S lay e party size t) j col) =
      V (crossing ptr S lay e party t copy (.lit localBit.val) col) := by
  let countT:=S.pieces t
  let indexes:=List.finRange countT
  let block := fun i : Fin countT => (Demand.balanced size countT (.lit i.val),crossing ptr S lay e party t i)
  let pre:=indexes.take copy.val
  let post:=indexes.drop (copy.val+1)
  have nonempty : 0<countT := Nat.zero_lt_of_lt copy.isLt
  have size_le (i : Fin countT) : SlotEnergy.piece b countT i≤b :=
    (Finset.single_le_sum (f:=SlotEnergy.piece b countT) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans
      (le_of_eq (SlotEnergy.sum_piece b countT nonempty))
  have measured (i : Fin countT) : (V (block i).1).val=SlotEnergy.piece b countT i := by
    have eqv := Demand.balanced_value (data:=data) (m:=mem) (vs:=vs)
      size (.lit i.val) b countT i.val hb count i.isLt sized rfl
    exact (congrArg Fin.val eqv).trans (Fin.val_cast_of_lt ((size_le i).trans_lt hb))
  have parts : indexes=pre++copy::post := by
    have existsAt : copy.val< indexes.length := by
      simpa only [indexes,List.length_finRange] using copy.isLt
    have current : indexes[copy.val]'existsAt = copy := by
      apply Fin.ext
      change ((List.finRange countT)[copy.val]'existsAt).val = copy.val
      rw [List.getElem_finRange]; rfl
    have h:=List.take_append_drop copy.val indexes
    rw [List.drop_eq_getElem_cons existsAt,current] at h
    exact h.symm
  change V (locate (indexes.map block) j col)=_
  rw [parts,List.map_append,List.map_cons]
  apply locate_word data mem vs (pre.map block) (post.map block) (block copy).1 (block copy).2 j col localBit.val _
  · simp only [List.map_map,Function.comp_def,measured,pre,indexes,prefix_piece b countT copy.val (Nat.le_of_lt copy.isLt)]
    simpa only [SlotEnergy.pieceIndex_val] using bit
  · rw [measured];exact localBit.isLt
  · intro x atX
    apply crossing_bit_congr
    apply Fin.ext
    exact atX.trans (Fin.val_cast_of_lt ((localBit.isLt.trans_le (size_le copy)).trans hb)).symm


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

end OAI
