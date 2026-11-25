import OAI.Computability.MultitapeWeakETH.LaneLookup

/-! # Compiling the endpoint observations of a formula site -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.SiteCheck

open Algorithms.SubexponentialSAT IntegerMultiplication Code FormulaRanks SyntaxProgram
open VPVNP NearSquareRoot.Benes
open private Context formulaContext atOwner atOwner_poly local_ends from OAI.Computability.MultitapeWeakETH.AddressProgram
open private left left_poly from OAI.Computability.MultitapeWeakETH.EndpointProgram
noncomputable section

abbrev SiteContext := (Tally × Body × Body × Body) × Observations

def row (q : SiteContext × Key) : Row :=
  (observed (q.1.2,(left q.2,address (q.1.1,q.2))),sign q.2)

private theorem row_poly : Poly row := by
  have loc : Poly (fun q : SiteContext × Key => address (q.1.1,q.2)) :=
    ((Easy.fst.compose Easy.fst).pair Easy.snd).poly.compose address_poly
  exact (((Easy.fst.compose Easy.snd).poly.pair ((Easy.snd.poly.compose left_poly).pair loc)).compose observed_poly).pair
    (Easy.snd.poly.compose sign_poly)

def atSite (q : SiteContext × Key) : Bool :=
  let ctx := q.1.1
  let ids := selectWith atOwner ((ctx.2.1,q.2),ctx.2.2.2)
  check (left q.2,ids.map fun e => row (q.1,e))

theorem atSite_poly : Poly atSite := by
  let X := SiteContext × Key
  have gather : Poly (fun q : X => ((q.1.1.2.1,q.2),q.1.1.2.2.2)) := by fun_prop
  have localEnds := gather.compose (selectWith_poly ([],[]) atOwner_poly)
  have rows := (Easy.fst.poly.pair localEnds).compose (Poly.push default [] row_poly)
  exact ((Easy.snd.poly.compose left_poly).pair rows).compose check_poly

variable {n g r : ℕ} (F : SAT.CNF (Fin n)) (fit : Fintype.card (Site F) ≤ 2^(g+r)) (wd : SAT.WidthAtMost 3 F)
    (input output : Fin (2^(r+2)) → Bool)

private def obs : Observations := (tally g,List.ofFn input,List.ofFn output)

def portBit : End F → Bool :=
  Sum.elim (fun e => input (portOffset F fit wd (.inl e))) (fun e => output (portOffset F fit wd (.inr e)))

private theorem row_eq (e : End F) :
    row ((formulaContext (g+r) F,obs (g:=g) input output),encodeKey (endKey F e)) =
      (portBit F fit wd input output e,sign (encodeKey (endKey F e))) := by
  refine Prod.ext ?_ rfl
  simp only [row,address_eq F wd fit]
  cases e with
  | inl e => exact atOffset_eq (g:=g) (l:=r+2) (addresses F fit wd (.inl e)) input
  | inr e => exact atOffset_eq (g:=g) (l:=r+2) (addresses F fit wd (.inr e)) output

/-- Every local row comes from an actual incident end, and all ends
of this site are present, including separate incidences of the same wire. -/
theorem atSite_eq (v : Site F) :
    atSite ((formulaContext (g+r) F,obs (g:=g) input output),encodeKey (siteKey F v)) = true ↔
      localOK F v (halfAt F (portBit F fit wd input output) v) := by
  unfold atSite
  apply check_eq
  intro val
  obtain ⟨xs,_,mem,repr⟩ := local_ends F wd v
  let ctx := formulaContext (g+r) F
  have loc : selectWith atOwner ((ctx.2.1,encodeKey (siteKey F v)),ctx.2.2.2) = xs.map encodeKey := by
    simpa only [ctx,formulaContext,context,slot_encode,ends_encode] using repr
  rw [loc]
  simp only [List.mem_map]
  constructor
  · rintro ⟨key,⟨ns,hn,rfl⟩,eq⟩
    obtain ⟨⟨e,he⟩,rfl⟩ := (mem _).mp hn
    exact ⟨e,he,(row_eq F fit wd input output e).symm.trans eq⟩
  · rintro ⟨e,he,rfl⟩
    exact ⟨_,⟨_,(mem _).mpr ⟨⟨e,he⟩,rfl⟩,rfl⟩,row_eq F fit wd input output e⟩

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork.SiteCheck
