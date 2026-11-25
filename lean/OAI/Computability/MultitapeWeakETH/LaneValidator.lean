import OAI.Computability.MultitapeWeakETH.LaneClamp

/-! # A polynomial tape computation for the formula layer's local validator -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.SiteCheck

open Algorithms.SubexponentialSAT IntegerMultiplication Code FormulaRanks SyntaxProgram
open NearSquareRoot NearSquareRoot.Benes VPVNP Compression PackedSwitches
open private Context formulaContext from OAI.Computability.MultitapeWeakETH.AddressProgram
open private obs from OAI.Computability.MultitapeWeakETH.SiteRows
open scoped Classical
noncomputable section

abbrev LaneQuery := SiteContext × (Bits.Word × Tally)

private def siteWord (q : Context × Key) :=
  field (q.1.1,countKeys 7 (q.2,q.1.2.2.1))

private theorem siteWord_poly : Poly siteWord := by
  have keys : Poly (fun q : Context × Key => (q.2,q.1.2.2.1)) := by fun_prop
  exact ((Easy.fst.compose Easy.fst).poly.pair (keys.compose (countKeys_poly 7))).compose field_poly

private theorem siteWord_eq {n k : ℕ} (F : SAT.CNF (Fin n)) (wd : SAT.WidthAtMost 3 F)
    (fit : Fintype.card (Site F) ≤ 2^k) (v : Site F) :
    siteWord (formulaContext k F,encodeKey (siteKey F v)) = List.ofFn (siteCode F fit v) := by
  let id := ordinal (siteKey F) v
  let i : Fin (2^k) := id.castLE fit
  change field (tally k,countKeys 7 _) = List.ofFn (RAMSerialization.wordBits k i)
  rw [← field_eq]
  congr 1
  rw [← recover_tally (countKeys 7 _)]
  exact congrArg (fun j => (tally k,tally j)) (number_site F wd v)

private def tested (q : LaneQuery × Key) :=
  let addr := siteWord (q.1.1.1,q.2)
  let lane := (cutLists (q.1.1.2.1,addr)).1
  decide (lane=q.1.2.1) && !(atSite (q.1.1,q.2))

private theorem tested_poly : Poly tested := by
  let X := LaneQuery × Key
  have addr := (show Poly (fun q : X => (q.1.1.1,q.2)) by fun_prop).compose siteWord_poly
  have head := ((show Poly (fun q : X => q.1.1.2.1) by fun_prop).pair addr).compose (easy_cut Easy.identity).fstCompose.poly
  have flag := (head.pair (show Poly (fun q : X => q.1.2.1) by fun_prop)).compose easyWordEq.poly
  have hit := (show Poly (fun q : X => (q.1.1,q.2)) by fun_prop).compose atSite_poly
  exact (flag.pair (hit.compose Iter.negate.poly)).compose (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly

/-- Read the input and output banks of one lane, clamping the unused
input addresses and testing just the sites owned by that lane. -/
def validate (q : LaneQuery) :=
  clamped (q.2,sourceAddresses q.1.1,q.1.2.2.1) && !((q.1.1.2.2.1.map fun key => tested (q,key)).any id)

theorem validate_poly : Poly validate := by
  have sources : Poly (fun q : LaneQuery => sourceAddresses q.1.1) := (Easy.fst.compose Easy.fst).poly.compose sourceAddresses_poly
  have clean := (Easy.snd.poly.pair (sources.pair (show Poly (fun q : LaneQuery => q.1.2.2.1) by fun_prop))).compose clamped_poly
  have keys : Poly (fun q : LaneQuery => q.1.1.2.2.1) := by fun_prop
  have errors := ((Poly.identity.pair keys).compose (Poly.push default [] tested_poly)).compose (any_poly id Poly.identity)
  exact (clean.pair (errors.compose Iter.negate.poly)).compose (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly

variable {n g r : ℕ} (F : SAT.CNF (Fin n)) (fit : Fintype.card (Site F) ≤ 2^(g+r)) (wd : SAT.WidthAtMost 3 F)
    (v : BitWord g) (input output : Fin (2^(r+2)) → Bool)

private def query : LaneQuery :=
  ((formulaContext (g+r) F,obs (g:=g) input output),laneBytes v,tally (r+2))

private theorem rejected (u : Site F) :
    tested (query F v input output,encodeKey (siteKey F u)) = false ↔
    siteLane F fit u = v → localOK F u (halfAt F (portBit F fit wd input output) u) := by
  have addr := address_halves (g:=g) (l:=r) (siteCode F fit u)
  change ((decide ((cutLists (tally g,siteWord (formulaContext (g+r) F,encodeKey (siteKey F u)))).1=laneBytes v))
    && !atSite ((formulaContext (g+r) F,obs (g:=g) input output),encodeKey (siteKey F u)))=false ↔ _
  rw [siteWord_eq F wd fit,addr]
  simp only [laneBytes_injective.eq_iff,Bool.and_eq_false_imp,decide_eq_true_eq,Bool.not_eq_false']
  exact imp_congr_right fun _ => atSite_eq F fit wd input output u

/-- The physical bit on a single lane gives its actual formula tensor
entry over any nontrivial commutative semiring. -/
theorem validate_eq (R : Type) [CommSemiring R] [Nontrivial R] :
    validator F fit wd R v input output = if validate (query F v input output) then 1 else 0 := by
  let src := Function.Embedding.inl.trans (addresses F fit wd)
  let ok := ∀ i, addressAt (g:=g) (l:=r+2) v i ∉ Set.range src → input i=false
  let checks := ∀ u, siteLane F fit u = v → localOK F u (halfAt F (portBit F fit wd input output) u)
  have clamp : clamped ((laneBytes v,tally (r+2)),sourceAddresses (formulaContext (g+r) F),List.ofFn input)=true ↔ ok := by
    rw [clamped_eq]
    have present (i : Fin (2^(r+2))) : List.ofFn (addressAt v i) ∈ sourceAddresses (formulaContext (g+r) F) ↔
        addressAt v i ∈ Set.range src := by
      rw [sourceAddresses_mem F wd fit]
      simp only [List.ofFn_injective.eq_iff]
      rfl
    simp_rw [present]
    rfl
  have sites_ok : ((query F v input output).1.1.2.2.1.map (fun key => tested (query F v input output,key))).any id = false ↔ checks := by
    obtain ⟨vs,_,all,names⟩ := typed_list _ _ (site_list F).1 (site_list F).2
    have keys : (query F v input output).1.1.2.2.1 = vs.map (fun u => encodeKey (siteKey F u)) := by
      simp only [query,formulaContext,context,sites_encode,← names,List.map_map,Function.comp_def]
    simp only [keys,List.any_eq_false,List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,id_eq]
    simp only [all,forall_true_left,Bool.not_eq_true,rejected F fit wd v input output]
    rfl
  have valid : validate (query F v input output)=true ↔ ok ∧ checks := by
    rw [validate,Bool.and_eq_true,Bool.not_eq_true',sites_ok]
    exact and_congr_left fun _ => clamp
  by_cases h : ok
  · rw [validator,ite_eq_left h]
    by_cases c : checks
    · rw [ite_eq_left (valid.mpr ⟨h,c⟩)]
      apply Finset.prod_eq_one
      intro u _
      split <;> rename_i eq
      · exact ite_eq_left (c u eq)
      · rfl
    · rw [ite_eq_right (by simpa only [valid,h,true_and] using c)]
      obtain ⟨u,hu⟩ := not_forall.mp c
      obtain ⟨atLane,fails⟩ := Classical.not_imp.mp hu
      apply Finset.prod_eq_zero (Finset.mem_univ u)
      rw [ite_eq_left atLane]
      exact ite_eq_right fails
  · rw [validator,ite_eq_right h,ite_eq_right (fun hit => h (valid.mp hit).1)]

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork.SiteCheck
