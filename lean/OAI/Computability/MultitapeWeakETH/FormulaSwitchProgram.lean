import OAI.Computability.MultitapeWeakETH.IncidenceRouting
import OAI.Computability.NearSquareRoot.CRTControlledBenesRead

/-! # Physical preparation of the padded permutation and all its switch bits -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork

open Algorithms.SubexponentialSAT NearSquareRoot NearSquareRoot.Benes IntegerMultiplication.Code
open scoped Classical
noncomputable section

private abbrev Key := List Bool

private def withFlag (rows : RawTable) : Labels Key := rows.map fun (x,y) => (x,y,false)

private theorem flag_poly : Poly withFlag :=
  Poly.maps _ (Easy.fst.poly.pair (Easy.snd.poly.pair (IntegerMultiplication.Code.Poly.const false)))

/-- List missing endpoints as fixed points so the Beneš compiler gets a full
permutation table, including every inactive port. -/
def filledTable (q : RawTable × List Key) : RawTable :=
  q.2.map fun x => (x,(label (withFlag q.1) x).1)

theorem filledTable_poly : Poly filledTable := by
  let row : RawTable × Key → Key × Key := fun p => (p.2,(label (withFlag p.1) p.2).1)
  have lookup := (Easy.snd.poly.pair (Easy.fst.poly.compose flag_poly)).compose
    (label_poly [] easyWordEq.poly)
  exact Poly.push [] [] (Easy.snd.poly.pair lookup.fstCompose : Poly row)

private theorem label_rows {A : Type} (items : List A) (key : A ↪ Key) (image : A → Key) (x : Key)
    (next : Key) (hit : ∀ a ∈ items, x = key a → image a = next)
    (miss : (∀ a ∈ items, x ≠ key a) → x = next) :
    (label (withFlag (items.map fun a => (key a,image a))) x).1 = next := by
  induction items with
  | nil => exact miss (by simp)
  | cons a items ih =>
    by_cases h : x = key a
    · subst x
      simpa [withFlag,label] using hit a (List.mem_cons_self) rfl
    · simp only [withFlag,List.map_cons,label,List.lookup_cons,Bool.beq_eq_decide_eq,decide_eq_false h]
      exact ih (fun i hi => hit i (List.mem_cons_of_mem _ hi)) (fun absent =>
        miss (by simpa [h] using absent))

variable {n k : ℕ} (F : SAT.CNF (Fin n)) (fit : Fintype.card (Site F) ≤ 2^k) (width : SAT.WidthAtMost 3 F)

def endRows (ends : List (End F)) : RawTable :=
  ends.map fun e => (List.ofFn (addresses F fit width e),List.ofFn (addresses F fit width e.swap))

/-- The padding program reconstructs exactly the signed-end permutation for
any enumeration of the endpoints and any complete ordering of all addresses. -/
theorem filledTable_represents (ends : List (End F)) (he : ∀ e, e ∈ ends)
    (keys : List (Word (k+2))) (unique : keys.Nodup) (complete : ∀ x, x ∈ keys) :
    RawRepresents (exchange F fit width) (filledTable (endRows F fit width ends,keys.map List.ofFn)) := by
  refine ⟨keys,unique,complete,?_⟩
  simp only [filledTable,List.map_map]
  apply List.map_congr_left
  intro x _
  apply Prod.mk.injEq _ _ _ _ |>.mpr
  refine ⟨rfl,?_⟩
  let addr := addresses F fit width
  let key : End F ↪ Key := addr.trans ⟨List.ofFn,List.ofFn_injective⟩
  apply label_rows ends key (fun e => List.ofFn (addr e.swap))
  · intro e _ eq
    have same : x = addr e := List.ofFn_injective eq
    subst x
    exact congrArg List.ofFn (Equiv.Perm.viaEmbedding_apply (Equiv.sumComm (Wire F) (Wire F)) addr e).symm
  · intro absent
    apply congrArg List.ofFn
    symm
    apply Equiv.Perm.viaEmbedding_apply_of_notMem
    rintro ⟨e,rfl⟩
    exact absent e (he e) rfl

/-- A single fixed polynomial-time program performs endpoint padding and
generates the two columns of every switch layer. -/
theorem prepare_switches_poly : Poly (fun x : Tally × RawTable × List Key =>
    generateTables (x.1,filledTable x.2)) :=
  (Easy.fst.poly.pair (Easy.snd.poly.compose filledTable_poly)).compose generateTables_poly

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork
