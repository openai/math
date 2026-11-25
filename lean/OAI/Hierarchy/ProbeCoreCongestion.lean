import OAI.Hierarchy.ProbeCoreWalks
import OAI.Hierarchy.ProbeFinalRoutes
import OAI.Hierarchy.ProbePayloadAccounts

namespace OAI
/-! # Congestion of the actual fixed-core fallback walks, separately at each physical edge -/

namespace Hierarchy.ProbeStage.CoreBoard
open AdaptiveProbe
open scoped BigOperators Classical
noncomputable section
variable {S : PurchaseSampler} {h d k : ℕ}

private abbrev Owns (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (e : Edges S h d k) :=
  ∃ c : PayloadStrip.Columns (Stages h d),payloadPlace π p c=(ends π e).1.1

private theorem joint_owned (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (j : Fin (Stages h d+1))
    (l : ColumnLayer k) : Owns π p (jointEdge (S:=S) π p j l) := by
  let x := payloadFreeFrom π p j
  let y := payloadFreeTo π p j
  let t : Fin (PayloadStrip.edgeCount (Stages h d)) := ⟨2*j.val,by have:=j.isLt;dsimp [PayloadStrip.edgeCount];omega⟩
  let hw := Strip.horizontal _ t
  have left : payloadPlace π p hw.left=x := (payloadPlace_free π p j).1
  have right : payloadPlace π p hw.right=y := (payloadPlace_free π p j).2.1
  have distinct : x≠y := by rw [←left,←right]; exact (payloadPlace π p).injective.ne hw.apart
  let ord := Fintype.equivFin (Columns h d)
  have adj := payloadFree_fixed π p j
  let key : Fixed h d := if order : ord x<ord y then ⟨(x,y),adj,order⟩ else
    ⟨(y,x),(permutationFabric h d).fixedAll_symm _ _ adj,lt_of_le_of_ne (le_of_not_gt order) (ord.injective.ne distinct.symm)⟩
  change ∃c,payloadPlace π p c=key.val.1
  by_cases order : ord x<ord y
  · exact ⟨hw.left,by simpa [key,order] using left⟩
  · exact ⟨hw.right,by simpa [key,order] using right⟩

private theorem tile_owned (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (t : StageAt h d) (l : ColumnLayer k) :
    Owns π p (tileEdge (S:=S) p t l) := ⟨_,payloadPlace_stage_in π p t⟩

private theorem prefix_owned (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (i : Fin (Stages h d+1)) :
    (prefixWalk (S:=S) (k:=k) π p i).length=2*i.val ∧ ∀e∈prefixWalk (S:=S) (k:=k) π p i,Owns π p e := by
  induction i using Fin.induction with
  | zero => simp [prefixWalk]
  | succ i ih =>
    rw [prefixWalk,Fin.induction_succ]
    change (prefixWalk π p i.castSucc ++ [jointEdge π p i.castSucc none,tileEdge p i none]).length=_ ∧ _
    refine ⟨by simp [ih.1]; omega,?_⟩
    intro e he
    rcases List.mem_append.mp he with old | more
    · exact ih.2 _ old
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at more
      rcases more with rfl | rfl
      · exact joint_owned π p _ _
      · exact tile_owned π p _ _

/-- Every edge used in any core fallback for a payload or signed tile has its
first endpoint inside that payload's global physical strip. -/
theorem commodity_owned (π : Equiv.Perm (Fin (2^h))) (i : Commodity (Fin (2^h)) (Stages h d) k)
    (e : Edges S h d k) (hit : e∈commodityWalk π i) :
    ∃ c : PayloadStrip.Columns (Stages h d),payloadPlace π (Sum.elim id (fun z=>z.1.1) i) c=(ends π e).1.1 := by
  rcases i with p | ⟨⟨p,t⟩,l⟩
  · change e∈prefixWalk π p (Fin.last (Stages h d))++[_] at hit
    rcases List.mem_append.mp hit with prior | endpt
    · exact (prefix_owned π p _).2 _ prior
    · obtain rfl := List.mem_singleton.mp endpt
      exact joint_owned π p _ _
  · simp only [commodityWalk,List.mem_cons,List.not_mem_nil,or_false] at hit
    rcases hit with rfl | rfl
    · exact tile_owned π p t _
    · exact ⟨_,payloadPlace_stage_out π p t⟩

/-- Use the same decidable comparison as the typed `routeLoad` on heterogeneous core IDs. -/
def occurrences {E : Type*} [DecidableEq E] (e : E) (walk : List E) := walk.count e

theorem occurrences_zero {E : Type*} [DecidableEq E] {e : E} {walk : List E} (skip : e∉walk) :
    occurrences e walk=0 := List.count_eq_zero.mpr skip

theorem occurrences_length {E : Type*} [DecidableEq E] (e : E) (walk : List E) :
    occurrences e walk≤walk.length := List.count_le_length

/-- In any one settled or spilled coordinate list, at most one payload row uses
a given physical edge. The row has at most `1+2Nk` commodities, with all repeated
edge occurrences in its actual lists charged at most `2N+2` times each. -/
theorem core_load_bound (π : Equiv.Perm (Fin (2^h))) (e : Edges S h d k)
    (bits : Commodity (Fin (2^h)) (Stages h d) k→ℕ) (B : ℕ) (bounded : ∀i,bits i≤B) :
    routeLoad (commodityWalk π) bits e≤(1+Stages h d*(2*k))*((2*Stages h d+2)*B) := by
  classical
  let N := Stages h d
  let I := PayloadStrip.Quotes N k
  let qty (p : Fin (2^h)) (i : I) := occurrences e (commodityWalk (S:=S) π (PayloadStrip.rowAddress p i))*bits (PayloadStrip.rowAddress p i)
  have sum : routeLoad (commodityWalk π) bits e=∑p,∑i,qty p i := by
    let eval := fun i : Commodity (Fin (2^h)) N k=>occurrences e (commodityWalk (S:=S) π i)*bits i
    exact ((PayloadStrip.allAddresses (P:=Fin (2^h)) (N:=N) (k:=k)).sum_comp eval).symm.trans (Fintype.sum_prod_type _)
  rw [sum]
  by_cases any : ∃p i, e∈commodityWalk π (PayloadStrip.rowAddress (N:=N) (k:=k) p i)
  · obtain ⟨p,i,hit⟩ := any
    have named (b : Fin (2^h)) (j : I) (entered : e∈commodityWalk π (PayloadStrip.rowAddress b j)) :
        ∃c,payloadPlace π b c=(ends π e).1.1 := by
      have pos := commodity_owned π (PayloadStrip.rowAddress b j) e entered
      cases j <;> exact pos
    obtain ⟨c,endpoint⟩ := named p i hit
    rw [Finset.sum_eq_single p]
    · have rate (a : I) : qty p a≤(2*N+2)*B := by
        apply Nat.mul_le_mul _ (bounded _)
        refine (occurrences_length _ _).trans ?_
        rcases a with t | ⟨j,l⟩
        · change (prefixWalk (S:=S) (k:=k) π p (Fin.last N) ++ [_]).length≤2*N+2
          simp [(prefix_owned (S:=S) (k:=k) π p (Fin.last N)).1]
        · simp [PayloadStrip.rowAddress,commodityWalk]
      exact (Finset.sum_le_sum fun j _=>rate j).trans_eq (by simp [I,PayloadStrip.Quotes,Fintype.card_sum,Fintype.card_prod,N,Nat.mul_comm 2 k])
    · intro b _ other
      apply Finset.sum_eq_zero
      intro a _
      have skip : e∉commodityWalk π (PayloadStrip.rowAddress b a) := by
        intro used
        obtain ⟨d,more⟩ := named b a used
        exact other (congrArg Prod.fst ((payloadPlaceAll π).injective (more.trans endpoint.symm)))
      simp [qty,occurrences_zero skip]
    · simp
  · have zero (p : Fin (2^h)) (i : I) : qty p i=0 := by
      have skip : e∉commodityWalk π (PayloadStrip.rowAddress p i) := fun h=>any ⟨p,i,h⟩
      simp [qty,occurrences_zero skip]
    simp [zero]

end
end Hierarchy.ProbeStage.CoreBoard

end OAI
