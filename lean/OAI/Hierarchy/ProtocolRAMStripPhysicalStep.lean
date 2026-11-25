import OAI.Hierarchy.ProtocolRAMStripHorizontal
import OAI.Hierarchy.ProtocolRAMBoughtLocations

namespace OAI
/-! # Every original branch digit resolves the physical edge of its retained strip -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe CoreBoard
open ThreeFlat.RAM
open scoped Classical
variable {n D H h d k : ℕ}

theorem walk_steps (choice : Fin n→Fin D→Option (Fin n)) (start : Fin n) (digits : Fin H→Fin D)
    (tiles : Fin (H+1)→Fin n) (path : PurchaseDFS.walk choice start digits=some (List.ofFn tiles)) :
    start=tiles 0 ∧ ∀ j : Fin H,choice (tiles j.castSucc) (digits j)=some (tiles j.succ) := by
  induction H generalizing start with
  | zero =>
    have eq : [start]=List.ofFn tiles := Option.some.inj path
    exact ⟨by simpa [List.ofFn_succ] using eq,fun j=>j.elim0⟩
  | succ a ih =>
    cases act : choice start (digits 0) with
    | none => simp [PurchaseDFS.walk,act] at path
    | some next =>
      cases sub : PurchaseDFS.walk choice next (Fin.tail digits) with
      | none => simp [PurchaseDFS.walk,act,show (fun i=>digits i.succ)=Fin.tail digits from rfl,sub] at path
      | some rest =>
        have cons : start::rest=tiles 0::List.ofFn (Fin.tail tiles) := by
          simpa only [PurchaseDFS.walk,act,show (fun i=>digits i.succ)=Fin.tail digits from rfl,sub,
            Option.bind_some,Option.map_some,Option.some.injEq,List.ofFn_succ,Fin.tail] using path
        have split:=List.cons.inj cons
        rw [split.2] at sub
        obtain ⟨root,following⟩:=ih next (Fin.tail digits) (Fin.tail tiles) sub
        refine ⟨split.1,?_⟩
        intro j
        induction j using Fin.cases with
        | zero => simpa only [Fin.castSucc_zero,split.1,root,Fin.tail] using act
        | succ j => exact following j

theorem row_walk (choice : Fin n→Fin D→Option (Fin n)) (i : PurchaseDirectory.Index n D H)
    (tiles : Fin (H+1)→Fin n) (observed : ∀j,PurchaseColumns.rowTile choice i j=(tiles j).castSucc) :
    PurchaseDFS.walk choice (PurchaseDirectory.item i).1 (PurchaseDirectory.item i).2=some (List.ofFn tiles) := by
  let item:=PurchaseDirectory.item i
  have live : PurchaseDFS.normalized choice item≠none := by
    intro bad
    exact Fin.castSucc_ne_last _ ((observed 0).symm.trans (PurchaseColumns.rowTile_of_dead choice i bad 0))
  cases hx : PurchaseDFS.walk choice item.1 item.2 with
  | none => exact (live (by simp [PurchaseDFS.normalized,hx])).elim
  | some p =>
    have simple : p.Nodup := by
      by_contra bad
      exact live (by simp [PurchaseDFS.normalized,hx,Option.filter,bad])
    have heads : List.ofFn (PurchaseColumns.rowTile choice i) = PurchaseDFS.filled choice item :=
      PurchaseColumns.rowTile_filled choice i
    have same : List.ofFn (fun j=>(tiles j).castSucc)=p.map Fin.castSucc := by
      rw [funext observed] at heads
      simpa [PurchaseDFS.filled,PurchaseDFS.normalized,hx,simple,PurchaseDFS.fillOption,Option.filter] using heads
    have names : List.ofFn tiles=p := (Fin.castSucc_injective n).list_map (by simpa only [List.map_ofFn,Function.comp_def] using same)
    exact congrArg some names.symm

theorem retained_step (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marks : StageAt h d→(Fin k×Bool)→Finset (Fin (2^h))) (p : LiveChains S π depth marks) (j : Fin depth) :
    let t:=p.1
    let a:=advisedStage h d π t
    let v:=liveRow S π depth marks p
    let digit:=(PurchaseDirectory.item (BoughtLocation.localIndex p)).2 j
    let c:=outputCol t (a.group (v j.castSucc)) (a.output (v j.castSucc))
    ∃ edge : Sample S h d, CoreLookup.neighbor S c digit=some edge ∧
      (freeEnds (S:=S) (k:=k) (.inr (.inr (.inr (edge,none))))).2=
        (inputCol t (a.group (v j.succ)) (a.input (v j.succ)),none) := by
  intro t a v digit c
  let enc:=(Fintype.equivFin (stageAt h d t).Group).toEmbedding
  let successor:=ProtocolRAMPurchaseOwners.successor a enc (D:=S.degree) (portDigits (S.rows (stageAt h d t).span))
  let i:=BoughtLocation.localIndex p
  have rows (l : Fin (depth+1)) : PurchaseColumns.rowTile successor i l=(v l).castSucc :=
    (StripDirectory.retainedRows S π depth marks p).choose_spec.2 l
  have step:=(walk_steps successor _ _ v (row_walk successor i v rows)).2 j
  obtain ⟨group,arc⟩:= (ProtocolRAMPurchaseOwners.successor_eq_some_iff ..).mp step
  obtain ⟨bound,edgeEq⟩:=List.getElem?_eq_some_iff.mp arc
  let actual : Sample S h d := ⟨t,a.group (v j.castSucc),a.output (v j.castSucc),
    ⟨a.input (v j.succ),edgeEq ▸ List.getElem_mem bound⟩⟩
  exact ⟨actual,CoreLookup.neighbor_read S t _ _ _ digit bound edgeEq,by simp [actual,freeEnds,group]⟩

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
