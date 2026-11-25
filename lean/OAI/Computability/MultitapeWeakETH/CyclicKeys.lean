import OAI.Computability.MultitapeWeakETH.SyntaxProgram

/-! # Computing the next equality-wire address by a bounded-key scan -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.SyntaxProgram

open Algorithms.SubexponentialSAT IntegerMultiplication.Code FormulaRanks
open scoped Classical
noncomputable section

/-- Keep keys whose predicate holds with the supplied common argument. -/
def selectWith {A : Type} (test : A × Key → Bool) (p : A × Body) : Body :=
  p.2.filter fun x => test (p.1,x)

theorem selectWith_poly {A : Type} [Codec A] (a : A) {test : A × Key → Bool} (h : Poly test) :
    Poly (selectWith test) := by
  have emit : Poly (fun p : A × Key => bif test p then [p.2] else []) :=
    Poly.choose h (by fun_prop) (IntegerMultiplication.Code.Poly.const [])
  convert (Poly.push a [] emit).compose Easy.flatten.poly using 1
  funext ⟨v,cs⟩
  change cs.filter _ = (cs.map _).flatten
  induction cs with
  | nil => rfl
  | cons x cs ih => cases e : test (v,x) <;> simp [e,ih]

private def sameVariable (q : Key × Key) :=
  decide ((q.1.headD []).length = (q.2.headD []).length)

private theorem sameVariable_poly : Poly sameVariable :=
  (((Easy.fst.compose (Iter.leader [])).pair (Easy.snd.compose (Iter.leader []))).compose Iter.linked).poly

def variableSlots := selectWith sameVariable

theorem variableSlots_poly : Poly variableSlots := selectWith_poly [] sameVariable_poly

private theorem head_slot {n} (F : SAT.CNF (Fin n)) (s : Slot F) :
    ((encodeKey (slotKey F s)).headD []).length = s.1.val+1 := by
  change (tally (s.1.val+1)).length = _
  simp

private def fiberList {n} (F : SAT.CNF (Fin n)) (v : Fin n) :=
  (slots n (Encoding.cnfNumbers F)).filter (fun x => decide (x.headD n = v.val))

private theorem slot_head {n} (F : SAT.CNF (Fin n)) (s : Slot F) :
    (slotKey F s).headD n = s.1.val := rfl

private theorem fiber_spec {n} (F : SAT.CNF (Fin n)) (v : Fin n) :
    (fiberList F v).Nodup ∧ ∀ x, x ∈ fiberList F v ↔ ∃ o, variableKey F v o = x := by
  obtain ⟨nd,mem⟩ := slot_list F
  refine ⟨nd.filter _,fun x => ?_⟩
  simp only [fiberList,List.mem_filter,decide_eq_true_eq,mem]
  constructor
  · rintro ⟨⟨⟨w,o⟩,rfl⟩,eq⟩
    obtain rfl : w=v := Fin.ext eq
    exact ⟨o,rfl⟩
  · rintro ⟨o,rfl⟩
    exact ⟨⟨⟨v,o⟩,rfl⟩,rfl⟩

private theorem variableSlots_eq {n} (F : SAT.CNF (Fin n)) (s : Slot F) :
    variableSlots (encodeKey (slotKey F s),(slots n (Encoding.cnfNumbers F)).map encodeKey) =
      (fiberList F s.1).map encodeKey := by
  simp only [variableSlots,selectWith,List.filter_map,fiberList,Function.comp_def]
  congr 1
  apply List.filter_congr
  intro x hx
  obtain ⟨t,rfl⟩ := ((slot_list F).2 x).mp hx
  unfold sameVariable
  dsimp only
  rw [head_slot,head_slot,slot_head]
  simp [eq_comm]

private def nextRank (q : Tally × Body) : Tally :=
  bif Iter.small (()::q.1,q.2) then ()::q.1 else []

private theorem nextRank_poly : Poly nextRank := by
  have inc : Easy (fun q : Tally × Body => ()::q.1) := (Easy.const () |>.pair Easy.fst).compose Easy.cons
  exact Poly.choose ((inc.pair Easy.snd).compose Iter.small_easy).poly inc.poly
    (IntegerMultiplication.Code.Poly.const [])

private def matchesRank (d : ℕ) (q : (Tally × Body) × Key) :=
  decide ((countKeys d (q.2,q.1.2)).length = q.1.1.length)

private theorem matchesRank_poly (d : ℕ) : Poly (matchesRank d) :=
  (((Easy.snd.pair (Easy.fst.compose Easy.snd)).poly.compose (countKeys_poly d)).pair
    (Easy.fst.compose Easy.fst).poly).compose Iter.linked.poly

def advance (q : Key × Body) : Key :=
  let xs := variableSlots q
  let i := nextRank (countKeys 6 (q.1,xs),xs)
  (selectWith (matchesRank 6) ((i,xs),xs)).headD []

theorem advance_poly : Poly advance := by
  have xs := variableSlots_poly
  have r := ((((Easy.fst.poly.pair xs).compose (countKeys_poly 6)).pair xs).compose nextRank_poly)
  exact ((((r.pair xs).pair xs).compose (selectWith_poly (([] : Tally),([] : Body)) (matchesRank_poly 6))).compose
    (Iter.leader ([] : Key)).poly)

/-- On well-formed input the search returns precisely the successor in the
variable's equality cycle, including the self-loop at an unused variable. -/
theorem advance_eq {n} (F : SAT.CNF (Fin n)) (width : SAT.WidthAtMost 3 F) (s : Slot F) :
    advance (encodeKey (slotKey F s),(slots n (Encoding.cnfNumbers F)).map encodeKey) =
      encodeKey (slotKey F (next F s)) := by
  obtain ⟨v,t⟩ := s
  let key := variableKey F v
  let e := slotIndex F v
  let xs := fiberList F v
  let list := xs.map encodeKey
  let target := e.symm (finRotate _ (e t))
  have nd := (fiber_spec F v).1
  have mem : ∀ x, x ∈ xs ↔ ∃ o, key o = x := (fiber_spec F v).2
  have num (o : Option (Fiber F v)) :
      (countKeys 6 (encodeKey (key o),list)).length = (e o).val := by
    change _ = (ordinal key o).val
    rw [ordinal_keys key xs nd mem,countKeys_length]
    · exact slot_length F width ⟨v,o⟩
    · intro x hx
      obtain ⟨b,rfl⟩ := (mem x).mp hx
      exact slot_length F width ⟨v,b⟩
  have size : list.length = Fintype.card (Fiber F v)+1 := by
    change (xs.map _).length = _
    rw [List.length_map,← List.toFinset_card_of_nodup nd]
    have eq : xs.toFinset = Finset.univ.image key := by
      ext x
      simp [mem]
    rw [eq,Finset.card_image_of_injective _ key.injective,Finset.card_univ,Fintype.card_option]
  let r := nextRank (countKeys 6 (encodeKey (key t),list),list)
  have want : r.length = (e target).val := by
    change (nextRank _).length = (e (e.symm _)).val
    rw [Equiv.apply_symm_apply,coe_finRotate]
    simp only [nextRank,Iter.small,List.length_cons,num,size]
    by_cases last : e t = Fin.last _
    · simp [last]
    · have lt := Fin.val_lt_last last
      simp [last,show (e t).val+1 < Fintype.card (Fiber F v)+1 by omega,num]
  let picked := selectWith (matchesRank 6) ((r,list),list)
  have contains (o : Option (Fiber F v)) : encodeKey (key o) ∈ list :=
    List.mem_map.mpr ⟨key o,(mem _).mpr ⟨o,rfl⟩,rfl⟩
  have valid (o : Option (Fiber F v)) :
      matchesRank 6 ((r,list),encodeKey (key o)) = true ↔ o = target := by
    simp only [matchesRank,num,want,decide_eq_true_eq]
    exact ⟨fun h => e.injective (Fin.ext h),fun h => congrArg (fun x => (e x).val) h⟩
  have witness : encodeKey (key target) ∈ picked :=
    List.mem_filter.mpr ⟨contains _,(valid _).mpr rfl⟩
  have atHead : picked.headD [] ∈ picked := by
    cases eq : picked with
    | nil => simp [eq] at witness
    | cons _ _ => simp
  obtain ⟨present,ok⟩ := List.mem_filter.mp atHead
  obtain ⟨x,hx,h⟩ := List.mem_map.mp present
  obtain ⟨o,rfl⟩ := (mem x).mp hx
  rw [← h] at ok
  have same := (valid o).mp ok
  subst o
  unfold advance
  rw [variableSlots_eq]
  exact h.symm

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork.SyntaxProgram
