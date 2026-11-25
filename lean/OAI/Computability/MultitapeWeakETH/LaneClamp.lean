import OAI.Computability.MultitapeWeakETH.SiteRows
import OAI.Computability.MultitapeWeakETH.FormulaSwitchProgram

/-! # Checking exactly the unused source bits of a packed formula lane -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.SiteCheck

open Algorithms.SubexponentialSAT IntegerMultiplication Code FormulaRanks SyntaxProgram
open NearSquareRoot NearSquareRoot.Benes VPVNP Compression PackedSwitches
open private Context formulaContext from OAI.Computability.MultitapeWeakETH.AddressProgram
open private left left_poly from OAI.Computability.MultitapeWeakETH.EndpointProgram
noncomputable section

def sourceAddresses (ctx : Context) : List Bits.Word :=
  (ctx.2.2.2.filter left).map fun key => address (ctx,key)

theorem sourceAddresses_poly : Poly sourceAddresses := by
  have keys : Poly (fun ctx : Context => ctx.2.2.2) := by fun_prop
  exact (Poly.identity.pair (keys.compose (Poly.filter left left_poly))).compose (Poly.push default [] address_poly)

theorem sourceAddresses_mem {n k : ℕ} (F : SAT.CNF (Fin n)) (wd : SAT.WidthAtMost 3 F)
    (fit : Fintype.card (Site F) ≤ 2^k) (x : Bits.Word) :
    x ∈ sourceAddresses (formulaContext k F) ↔ ∃ e : Wire F, List.ofFn (addresses F fit wd (.inl e))=x := by
  obtain ⟨es,_,all,ids⟩ := typed_list _ _ (end_list F).1 (end_list F).2
  let ctx := formulaContext k F
  have keys : ctx.2.2.2 = es.map (fun e => encodeKey (endKey F e)) := by
    simp only [ctx,formulaContext,context,ends_encode,← ids,List.map_map,Function.comp_def]
  change x ∈ ((ctx.2.2.2.filter left).map (fun e => address (ctx,e))) ↔ _
  rw [keys]
  constructor
  · rintro h
    obtain ⟨key,hk,eq⟩ := List.mem_map.mp h
    obtain ⟨member,source⟩ := List.mem_filter.mp hk
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp member
    cases e with
    | inr e => contradiction
    | inl e => exact ⟨e,(address_eq F wd fit _).symm.trans eq⟩
  · rintro ⟨e,rfl⟩
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨List.mem_map.mpr ⟨.inl e,all _,rfl⟩,rfl⟩,address_eq F wd fit _⟩

abbrev ClampInput := (Bits.Word × Tally) × List Bits.Word × Bits.Word

/-- The lane prefix and local field width form the address. Each candidate
offset carrying a one must occur in the list of active source addresses. -/
private def bad (q : ClampInput × Tally) :=
  let here := q.1.1.1 ++ field (q.1.1.2,q.2)
  Iter.pick false (q.1.2.2,q.2) && !(q.1.2.1.any (fun key => decide (here=key)))

private theorem contains_poly : Poly (fun p : Bits.Word × List Bits.Word => p.2.any (fun key => decide (p.1=key))) := by
  have run := (Poly.push [] [] easyWordEq.poly).compose (any_poly id Poly.identity)
  simpa [polyPush,List.any_map,Function.comp_def] using run

private theorem bad_poly : Poly bad := by
  let X := ClampInput × Tally
  have lane : Poly (fun q : X => q.1.1.1) := by fun_prop
  have bit := (show Poly (fun q : X => (q.1.2.2,q.2)) by fun_prop).compose (Iter.facile false).poly
  have addr := lane.app ((show Poly (fun q : X => (q.1.1.2,q.2)) by fun_prop).compose field_poly)
  have occurs := (addr.pair (show Poly (fun q : X => q.1.2.1) by fun_prop)).compose contains_poly
  exact (bit.pair (occurs.compose Iter.negate.poly)).compose (Easy.finite (fun t : Bool × Bool => t.1 && t.2)).poly

def clamped (q : ClampInput) :=
  !((Iter.lineup (ruler q.2.2)).map (fun j => bad (q,j))).any id

theorem clamped_poly : Poly clamped := by
  have bank : Easy (fun q : ClampInput => q.2.2) := Easy.snd.compose Easy.snd
  have indices := (Easy.ruler bank).poly.compose Iter.poly_line
  exact ((Poly.identity.pair indices).compose (Poly.push default [] bad_poly)).compose
    ((any_poly id Poly.identity).compose Iter.negate.poly)

theorem clamped_eq {g l : ℕ} (v : BitWord g) (xs : List Bits.Word) (input : Fin (2^l) → Bool) :
    clamped ((laneBytes v,tally l),xs,List.ofFn input) = true ↔
      ∀ i, List.ofFn (addressAt v i) ∉ xs → input i = false := by
  have line : ruler (List.ofFn input) = tally (2^l) := by
    rw [← recover_tally (ruler _),ruler_length,List.length_ofFn]
  simp only [clamped,line,Iter.lined,List.map_ofFn,Function.comp_def,Bool.not_eq_true',List.any_eq_false]
  constructor
  · intro h i hi
    have q := h _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    rw [bytes_addressAt] at hi
    change laneBytes v ++ List.ofFn (RAMSerialization.wordBits l i) ∉ xs at hi
    simpa [bad,Iter.entry,field_eq,hi] using q
  · intro h b hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    by_cases member : List.ofFn (addressAt v i) ∈ xs
    · rw [bytes_addressAt] at member
      change laneBytes v ++ List.ofFn (RAMSerialization.wordBits l i) ∈ xs at member
      exact (by simpa [bad,Iter.entry,field_eq] using (fun _ : input i=true => member))
    · simp [bad,Iter.entry,h i member]

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork.SiteCheck
