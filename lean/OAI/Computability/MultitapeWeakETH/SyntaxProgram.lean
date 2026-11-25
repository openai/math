import OAI.Computability.MultitapeWeakETH.SyntaxLists
import OAI.Computability.IntegerMultiplication.Carry.Shrink

/-! # Charged formula-site and signed-end key generation -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.SyntaxProgram

open Algorithms.SubexponentialSAT IntegerMultiplication IntegerMultiplication.Code
open FormulaRanks

abbrev Body := List Key
abbrev Input := Tally × Body

def occurrenceKeys (cs : Body) : Body := cs.flatMap fun c => c.map (· :: c)

theorem occurrenceKeys_poly : Poly occurrenceKeys := by
  have expand : Poly (fun c : Key => c.map (· :: c)) :=
    Easy.clone.poly.compose (Poly.push [] [] (Easy.exchange.poly.compose Easy.cons.poly))
  exact (Poly.maps _ expand).compose Easy.flatten.poly

private def predecessor (w : Tally) : Tally := List.casesOn w [] fun _ t => t

private def variableDigit (x : Key) : Tally :=
  () :: (Carry.half (predecessor (x.headD []))).1

private theorem variable_poly : Poly variableDigit := by
  have pred : Easy predecessor := Easy.listCase [] Easy.snd
  have div := ((Iter.leader ([] : Tally)).compose pred).compose Carry.halfCost.fstCompose
  exact ((Easy.const ()).pair div).compose Easy.cons |>.poly

def asSlot (x : Key) : Key := variableDigit x :: [()] :: x

theorem asSlot_poly : Poly asSlot :=
  (variable_poly.pair (((Easy.const [()]).pair Easy.identity).compose Easy.cons).poly).compose Easy.cons.poly

def slotKeys (q : Input) : Body :=
  ((Iter.lineup q.1).map fun v => [() :: v]) ++ (occurrenceKeys q.2).map asSlot

theorem slotKeys_poly : Poly slotKeys := by
  have sentinel : Poly (fun v : Tally => [() :: v]) := by fun_prop
  exact ((Easy.fst.poly.compose Iter.poly_line).compose (Poly.maps _ sentinel)).app
    ((Easy.snd.poly.compose occurrenceKeys_poly).compose (Poly.maps _ asSlot_poly))

private def join (p : Body × Body) : Body :=
  p.1.map ([()] :: ·) ++ p.2.map ([(),()] :: ·)

private theorem join_poly : Poly join := by
  unfold join
  fun_prop

def sites (q : Input) : Body := join (slotKeys q,q.2)
def wires (q : Input) : Body := join (slotKeys q,occurrenceKeys q.2)
def ends (q : Input) : Body := join (wires q,wires q)

theorem sites_poly : Poly sites := (slotKeys_poly.pair Easy.snd.poly).compose join_poly

theorem ends_poly : Poly ends := by
  have w : Poly wires := (slotKeys_poly.pair (Easy.snd.poly.compose occurrenceKeys_poly)).compose join_poly
  exact (w.pair w).compose join_poly

private theorem occurrence_encode (cs : List (List ℕ)) :
    occurrenceKeys (cs.map encodeKey) = (occurrences cs).map encodeKey := by
  simp [occurrenceKeys,occurrences,List.map_flatMap,List.flatMap_map,Function.comp_def,encodeKey]

theorem asSlot_encode (x : List ℕ) : asSlot (encodeKey x) = encodeKey (realSlot x) := by
  cases x <;> simp [asSlot,variableDigit,realSlot,encodeKey,predecessor,Carry.half_v,tally_succ] <;> rfl

theorem slot_encode (n : ℕ) (cs : List (List ℕ)) :
    slotKeys (tally n,cs.map encodeKey) = (slots n cs).map encodeKey := by
  have line : (Iter.lineup (tally n)).map (fun v => [() :: v]) =
      (List.range n).map (fun v => encodeKey [v]) := by
    apply List.ext_getElem
    · simp
    · intro i h h'
      simp [Iter.lineup,encodeKey,tally_succ]
  simp only [slotKeys,slots,occurrence_encode,List.map_append,List.map_map,Function.comp_def,asSlot_encode,line]

private theorem join_encode (a b : List (List ℕ)) :
    join (a.map encodeKey,b.map encodeKey) = (joinKeys a b).map encodeKey := by
  simp [join,joinKeys,List.map_map,Function.comp_def,encodeKey,tally]

theorem sites_encode (n : ℕ) (cs : List (List ℕ)) :
    sites (tally n,cs.map encodeKey) = (siteKeys n cs).map encodeKey := by
  simpa only [sites,siteKeys,slot_encode] using join_encode (slots n cs) cs

theorem ends_encode (n : ℕ) (cs : List (List ℕ)) :
    ends (tally n,cs.map encodeKey) = (endKeys n cs).map encodeKey := by
  simp only [ends,wires,slot_encode,occurrence_encode,join_encode,endKeys,wireKeys]

/-- The output is the exact site ordinal used by the permutation compiler. -/
theorem number_site {n} (F : SAT.CNF (Fin n)) (width : SAT.WidthAtMost 3 F) (s : Site F) :
    (countKeys 7 (encodeKey (siteKey F s),sites (tally n,(Encoding.cnfNumbers F).map encodeKey))).length =
      (ordinal (siteKey F) s).val := by
  obtain ⟨unique,mem⟩ := site_list F
  rw [sites_encode,countKeys_length _ _ _ (site_length F width s),ordinal_keys _ _ unique mem]
  intro x hx
  obtain ⟨v,rfl⟩ := (mem x).mp hx
  exact site_length F width v

end OAI.Computability.MultitapeWeakETH.CNFNetwork.SyntaxProgram
