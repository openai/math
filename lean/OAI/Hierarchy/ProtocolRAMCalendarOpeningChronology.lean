import OAI.Hierarchy.ProtocolRAMCalendarOpeningBill
import OAI.Hierarchy.ProtocolRAMCalendarLiveFee
import OAI.Hierarchy.ProtocolRAMCalendarSignedHistory

namespace OAI
/-! # Opening charges indexed by all dated outer purchases in the executed mesh -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ReportSockets CoreBoard
open scoped BigOperators Classical
private theorem range_sum (xs : ℕ) (f : ℕ→ℝ) :
    ((List.range xs).map f).sum=∑ j : Fin xs,f j.val := by
  rw [Fin.sum_univ_eq_sum_range]
  induction xs with
  | zero => simp
  | succ n ih => simp only [List.range_succ,List.map_append,List.sum_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,ih,Finset.sum_range_succ]

private theorem blocks_sum {α β : Type*} (xs : List α) (emit : α→List β) (price : β→ℝ) :
    ((xs.flatMap emit).map price).sum=(xs.map (fun i=>((emit i).map price).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]

/-- The padded reserve attempt and feed rows contribute zero to opening
charges. Reserve repairs still appear in all the signed install/debit sums. -/
theorem opening_rows (c : Mesh) (opening : Event→ℝ)
    (inner : ∀p a j b,opening (.attempt (.inner p a j b))=0)
    (feed : ∀b,opening (.feed b)=0) :
    ((events c).map opening).sum=
    ∑p : Fin (c.inject+c.cool),∑a : Fin c.outerFuel,opening (.attempt (.outer p.val a.val)) := by
  have reserve (p a j : ℕ) : ((reserveBlock c p a j).map opening).sum=0 := by
    simp [reserveBlock,List.map_map,Function.comp_def,inner,feed]
  have trial (p a : ℕ) : ((trialBlock c p a).map opening).sum=opening (.attempt (.outer p a)) := by
    simp [trialBlock,blocks_sum,reserve]
  have outer (p : ℕ) : ((outerBlock c p).map opening).sum=∑a : Fin c.outerFuel,opening (.attempt (.outer p a.val)) := by
    simp [outerBlock,blocks_sum,trial,feed,range_sum]
  simp [events,blocks_sum,outer,range_sum]

/-- There is one equality per dated gate even when trials share identical
geometric endpoints. The real native completion mask decides which chains
are counted in that gate's marks. -/
theorem openings_from_calendar {z W k : ℕ} (c : Mesh) (S : PurchaseSampler)
    (π : Equiv.Perm (Fin (2^z))) (depth M : ℕ) (p q Q Λ : ℝ)
    (marks : Marks z W k ((c.inject+c.cool)*c.outerFuel)) (report : Event→Charges)
    (inner : ∀u a j b,(report (.attempt (.inner u a j b))).opening=0)
    (feed : ∀b,(report (.feed b)).opening=0)
    (paid : ∀(u : Fin (c.inject+c.cool)) (a : Fin c.outerFuel),
      (report (.attempt (.outer u.val a.val))).opening=
        (Fintype.card (LiveChains S π depth (marks (finProdFinEquiv (u,a)))):ℝ)*(Λ*(dyadicScale W)^p)) :
    (∑e : Catalogue S π depth marks,Λ*capacity p q Q (scaleOf S π depth marks e) (lenCode S π depth marks M e))=
    coreDebit S z (2^W) k p q Q Λ (dyadicScale W) M+((events c).map (fun ev=>(report ev).opening)).sum := by
  rw [catalogue_openings S π depth marks M p q Q Λ,opening_rows c (fun ev=>(report ev).opening) inner feed]
  congr 1
  let fee (i : Fin ((c.inject+c.cool)*c.outerFuel)) :=
    (Fintype.card (LiveChains S π depth (marks i)):ℝ)*(Λ*(dyadicScale W)^p)
  change (∑i,fee i)=_
  rw [←finProdFinEquiv.sum_comp fee,Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun u _=>Finset.sum_congr rfl (fun a _=>(paid u a).symm))

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
