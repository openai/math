import OAI.Computability.MultitapeWeakETH.EndpointProgram

/-! # Computing the permuted address of every half-wire from the formula -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.SyntaxProgram

open Algorithms.SubexponentialSAT IntegerMultiplication.Code FormulaRanks NearSquareRoot.Benes
open scoped Classical
noncomputable section

private abbrev Context := Tally × Body × Body × Body

private def atOwner (q : (Body × Key) × Key) := sameKey 7 (owner (q.1.1,q.2),q.1.2)

private theorem atOwner_poly : Poly atOwner := by
  have own := (show Poly (fun q : (Body × Key) × Key => (q.1.1,q.2)) by fun_prop).compose owner_poly
  exact (own.pair (Easy.fst.compose Easy.snd).poly).compose (sameKey_poly 7)

/-- Site and local port ordinals are written into separate binary fields. -/
def address (q : Context × Key) : List Bool :=
  let v := owner (q.1.2.1,q.2)
  let localEnds := selectWith atOwner ((q.1.2.1,v),q.1.2.2.2)
  field (q.1.1,countKeys 7 (v,q.1.2.2.1)) ++ field (tally 2,countKeys 8 (q.2,localEnds))

theorem address_poly : Poly address := by
  have slotsP : Poly (fun q : Context × Key => q.1.2.1) := by fun_prop
  have sitesP : Poly (fun q : Context × Key => q.1.2.2.1) := by fun_prop
  have endsP : Poly (fun q : Context × Key => q.1.2.2.2) := by fun_prop
  have v := (slotsP.pair Easy.snd.poly).compose owner_poly
  have loc := (((slotsP.pair v).pair endsP).compose (selectWith_poly (([] : Body),([] : Key)) atOwner_poly))
  exact (((Easy.fst.compose Easy.fst).poly.pair ((v.pair sitesP).compose (countKeys_poly 7))).compose field_poly).app
    ((((Easy.const (tally 2)).poly).pair ((Easy.snd.poly.pair loc).compose (countKeys_poly 8))).compose field_poly)

def context (q : Tally × Input) : Context := (q.1,slotKeys q.2,sites q.2,ends q.2)

theorem context_poly : Poly context :=
  Easy.fst.poly.pair ((Easy.snd.poly.compose slotKeys_poly).pair
    ((Easy.snd.poly.compose sites_poly).pair (Easy.snd.poly.compose ends_poly)))

variable {n k : ℕ} (F : SAT.CNF (Fin n)) (wd : SAT.WidthAtMost 3 F)

private def formulaContext (k : ℕ) (F : SAT.CNF (Fin n)) := context (tally k,tally n,(Encoding.cnfNumbers F).map encodeKey)

include wd in
private theorem local_ends (v : Site F) :
    let cs := Encoding.cnfNumbers F
    let sl := (slots n cs).map encodeKey
    ∃ xs : List (List ℕ), xs.Nodup ∧ (∀ x, x ∈ xs ↔ ∃ e : {e // host F e = v}, endKey F e.val = x) ∧
      selectWith atOwner ((sl,encodeKey (siteKey F v)),(endKeys n cs).map encodeKey) = xs.map encodeKey := by
  let ks := endKeys n (Encoding.cnfNumbers F)
  obtain ⟨es,unique,all,code⟩ := typed_list (endKey F) ks (end_list F).1 (end_list F).2
  let es' := es.filter fun e => decide (host F e = v)
  refine ⟨es'.map (endKey F),(unique.filter _).map (endKey F).injective,?_,?_⟩
  · intro x
    constructor
    · intro h
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp h
      exact ⟨⟨e,of_decide_eq_true (List.mem_filter.mp he).2⟩,rfl⟩
    · rintro ⟨⟨e,eq⟩,rfl⟩
      exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨all _,decide_eq_true eq⟩,rfl⟩
  · change selectWith _ (_,ks.map encodeKey) = _
    rw [← code]
    simp only [selectWith,List.filter_map,List.map_map,Function.comp_def,es']
    congr 1
    apply List.filter_congr
    intro e _
    simp only [atOwner,owner_eq F wd,sameKey_encode 7 _ _ (site_length F wd _) (site_length F wd _),
      (siteKey F).injective.eq_iff]

theorem address_eq (fit : Fintype.card (Site F) ≤ 2^k) (e : End F) :
    address (formulaContext k F,encodeKey (endKey F e)) = List.ofFn (addresses F fit wd e) := by
  let v := host F e
  let pk := (Function.Embedding.subtype (fun t => host F t = v)).trans (endKey F)
  let site := ordinal (siteKey F) v
  let port := ordinal pk ⟨e,rfl⟩
  let siteNum : Fin (2^k) := site.castLE fit
  let portNum : Fin (2^2) := port.castLE ((ends_per_site F wd v).trans (by decide))
  change _ = List.ofFn (Fin.append (VPVNP.RAMSerialization.wordBits k siteNum)
    (VPVNP.RAMSerialization.wordBits 2 portNum))
  rw [List.ofFn_fin_append,← field_eq,← field_eq]
  unfold address formulaContext context
  dsimp only
  rw [slot_encode,owner_eq F wd,ends_encode]
  obtain ⟨xs,nd,mem,eq⟩ := local_ends F wd v
  rw [eq]
  congr 2
  · rw [← recover_tally (countKeys 7 _),number_site F wd]
    rfl
  · have h : (countKeys 8 (encodeKey (endKey F e),xs.map encodeKey)).length = port.val := by
      rw [countKeys_length 8 _ _ (end_length F wd e),ordinal_keys pk xs nd mem]
      · rfl
      · intro x hx
        obtain ⟨t,rfl⟩ := (mem x).mp hx
        exact end_length F wd t.val
    rw [← recover_tally (countKeys 8 _),h]
    rfl

/-- Compute the full list of active permutation pairs. -/
def rows (q : Tally × Input) : RawTable :=
  let c := context q
  c.2.2.2.map fun e => (address (c,e),address (c,swapEnd e))

theorem rows_poly : Poly rows := by
  have row := address_poly.pair ((Easy.fst.poly.pair (Easy.snd.poly.compose swap_poly)).compose address_poly)
  exact (context_poly.pair (Easy.snd.poly.compose ends_poly)).compose
    (Poly.push (([] : Tally),([] : Body),([] : Body),([] : Body)) [] row)

theorem rows_eq (fit : Fintype.card (Site F) ≤ 2^k) :
    ∃ es : List (End F), (∀ e, e ∈ es) ∧
      rows (tally k,tally n,(Encoding.cnfNumbers F).map encodeKey) = endRows F fit wd es := by
  obtain ⟨es,_,all,code⟩ := typed_list _ _ (end_list F).1 (end_list F).2
  refine ⟨es,all,?_⟩
  change (ends _).map (fun e => (address (formulaContext k F,e),address (formulaContext k F,swapEnd e))) = _
  rw [ends_encode,← code]
  simp only [List.map_map,Function.comp_def,endRows,swap_encode,address_eq F wd fit]

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork.SyntaxProgram
