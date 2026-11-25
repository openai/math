import OAI.Hierarchy.ProbeCoreWalkMount
import OAI.Hierarchy.ProbeSiteAddress
import OAI.Hierarchy.ProtocolRAMCatalogueRowFields

namespace OAI
/-! # Original core and purchased edges mounted from the catalogue -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe
open scoped Classical Fin.CommRing

variable {w h W k K : ℕ} {S : PurchaseSampler}

/-- Read a physical row from its own contiguous catalogue interval. -/
def Board.byKind (b : Board) {α : Type*} (core : Fin b.coreRows→α) (bought : Fin b.boughtRows→α)
    (i : Fin b.rows) : α :=
  if inside : i.val<b.coreRows then core ⟨i.val,inside⟩
  else bought ⟨i.val-b.coreRows,by have room:=i.isLt;unfold Board.rows at room;omega⟩

@[simp] theorem Board.byKind_core (b : Board) {α : Type*} (old : Fin b.coreRows→α)
    (newer : Fin b.boughtRows→α) (j : Fin b.coreRows) : b.byKind old newer (b.coreIndex j)=old j := by
  unfold Board.byKind
  rw [dite_eq_left (show (b.coreIndex j).val<b.coreRows from j.isLt)]
  exact congrArg old (Fin.ext rfl)

@[simp] theorem Board.byKind_bought (b : Board) {α : Type*} (old : Fin b.coreRows→α)
    (newer : Fin b.boughtRows→α) (j : Fin b.boughtRows) : b.byKind old newer (b.boughtIndex j)=newer j := by
  have outside : ¬b.coreRows+j.val<b.coreRows := by omega
  simp only [Board.byKind,Board.boughtIndex,dite_eq_right outside,Nat.add_sub_cancel_left]

/-- Decode the fixed physical site numbering. Missing padding records can
contain arbitrary natural addresses, so the total decoder has an idle site. -/
def reportedSite (place : Site h (2^W) k→Fin K) (x : ℕ) : Fin K :=
  let ordinal : Fin (siteLast h (2^W) k+1):=if ok : x<siteLast h (2^W) k+1 then ⟨x,ok⟩ else 0
  place ((siteNumber h (2^W) k).symm ordinal)

@[simp] theorem reportedSite_number (place : Site h (2^W) k→Fin K) (x : Site h (2^W) k) :
    reportedSite place ((siteNumber h (2^W) k) x).val=place x := by
  unfold reportedSite
  rw [dite_eq_left ((siteNumber h (2^W) k) x).isLt]
  exact congrArg place ((siteNumber h (2^W) k).symm_apply_apply x)

/-- Core walks retain their original orientation. A purchased edge takes its
two endpoint words directly from the same acquired row the terminal reads. -/
def Board.coreMount (b : Board) (π : Equiv.Perm (Fin (2^h))) (place : Site h (2^W) k→Fin K)
    (order : Fin b.coreRows≃Edges S h (2^W) k) (m : Memory w) : Mount (S:=S) π place b.rows where
  actual:=⟨b.byKind (fun j=>place (ends π (order j)).1) (fun j=>
    let x:=b.bought.view m (j.val:Word w)
    reportedSite place (min x.left x.right)),
    b.byKind (fun j=>place (ends π (order j)).2) (fun j=>
    let x:=b.bought.view m (j.val:Word w)
    reportedSite place (max x.left x.right))⟩
  row:=⟨fun e=>b.coreIndex (order.symm e),fun _ _ eq=>order.symm.injective
    (Fin.ext (congrArg (fun z : Fin b.rows=>z.val) eq))⟩
  tail:=by
    intro e
    exact (b.byKind_core (fun j=>place (ends π (order j)).1) (fun j=>
      let x:=b.bought.view m (j.val:Word w)
      reportedSite place (min x.left x.right)) (order.symm e)).trans
      (congrArg (fun j : Edges S h (2^W) k=>place (ends π j).1) (order.apply_symm_apply e))
  head:=by
    intro e
    exact (b.byKind_core (fun j=>place (ends π (order j)).2) (fun j=>
      let x:=b.bought.view m (j.val:Word w)
      reportedSite place (max x.left x.right)) (order.symm e)).trans
      (congrArg (fun j : Edges S h (2^W) k=>place (ends π j).2) (order.apply_symm_apply e))

@[simp] theorem Board.coreMount_row (b : Board) (π : Equiv.Perm (Fin (2^h))) (place : Site h (2^W) k→Fin K)
    (order : Fin b.coreRows≃Edges S h (2^W) k) (m : Memory w) (e : Edges S h (2^W) k) :
    (b.coreMount π place order m).row e=b.coreIndex (order.symm e) := rfl

theorem Board.coreMount_ordinary (b : Board) (π : Equiv.Perm (Fin (2^h))) (place : Site h (2^W) k→Fin K)
    (order : Fin b.coreRows≃Edges S h (2^W) k) (m : Memory w)
    (i : Commodity (Fin (2^h)) (Stages h (2^W)) k) :
    (b.coreMount π place order m).ordinary i=
      ((commodityWalk (S:=S) π i).map order.symm).map b.coreIndex := by
  rw [Mount.ordinary,List.map_map]; rfl

theorem Board.coreMount_centers (b : Board) (π : Equiv.Perm (Fin (2^h))) (place : Site h (2^W) k→Fin K)
    (order : Fin b.coreRows≃Edges S h (2^W) k) (m : Memory w) (i : Columns h (2^W) × Fin k) :
    (b.coreMount π place order m).centers i=
      ((catalystWalk (S:=S) i).map order.symm).map b.coreIndex := by
  rw [Mount.centers,List.map_map]; rfl

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
