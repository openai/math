import OAI.Hierarchy.HistorySelectedPrograms
import OAI.ThreeFlat.RAM.HistorySelectedInterior

namespace OAI
/-! # The chronological selected-node controller with a receiver-specific leaf -/

namespace Hierarchy.HistorySelectedReceiverLoop
open ThreeFlat RAM RAM.DescriptorExpr RAM.PhysicalPinsExpr
open RAM.PhysicalProcedure RAM.HistoryNodeDirectory RAM.HistoryNodeDirectory.Selected
open RAM.HistoryStageBody.Physical Diagonal.TickWorkspace Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Fin.CommRing
noncomputable section
variable {W n : ℕ} {F : Type*}

theorem body_spec (W u : ℕ) (archive : Archive) (leafProc : Procedure W) (roster : List Family) (m : Memory W)
    (post : Memory W→Memory W→Prop) (initialCost : ℕ) (arm : Family→ℕ)
    (wide : 2<2^W) (cursor : base u 18<2^W) (node : nodeAddress u m+5<2^W)
    (stage : ∀ f∈roster,(m (nodeAddress u m)).val=kind f.mode →
      stageAddress u m+48<2^W ∧ f.oldPorts<2^W)
    (matched : ∀ f,roster.find? (matchesFamily u m)=some f →
      (HistoryStageBody.procedure (layout u archive f) f.childBound W).Spec (·=m) post (arm f))
    (leaf : roster.find? (matchesFamily u m)=none →
      leafProc.Spec (·=m) post initialCost) :
    (body u archive leafProc roster).Spec (·=m) post (bodyCost u m initialCost arm roster) := by
  induction roster with
  | nil => exact leaf rfl
  | cons f fs ih =>
    have gate := ifWord_enabled u m f wide cursor node (stage f (List.mem_cons_self ..))
    have one : (1:Word W)≠0 := by
      intro eq
      have t := congrArg Fin.val eq
      have h : (1:Word W).val=1 := Fin.val_cast_of_lt (by omega : 1<2^W)
      simp only [h,Fin.val_zero] at t
      omega
    change (ifValue (enabled u f) _ (body u archive leafProc fs)).Spec _ _ _
    cases h : matchesFamily u m f with
    | true =>
      simp [h] at gate
      refine ifValue_spec _ _ _ _ post (fun _=>arm f) _ (fun _ _=>by simp [bodyCost,h]) ?_ ?_
      · rintro _ rfl _
        exact matched f (by simp [h])
      · rintro _ rfl hz
        exact (one (gate.symm.trans hz)).elim
    | false =>
      simp [h] at gate
      refine ifValue_spec _ _ _ _ post (fun _=>bodyCost u m initialCost arm fs) _
        (fun _ _=>by simp [bodyCost,h]) ?_ ?_
      · rintro _ rfl nz
        exact (nz gate).elim
      · rintro _ rfl _
        apply ih (fun g hg=> stage g (List.mem_cons_of_mem _ hg))
        · intro g hg
          apply matched g
          simpa only [List.find?_cons,h] using hg
        · intro none
          apply leaf
          simpa only [List.find?_cons,h] using none

theorem visit {u i : ℕ} {D : Directory W n} {id : ((Fin 3→Bool)→F)→ℕ} {v : Fin n→NodeValue F}
    {keep : ℕ→Prop} {initial m : Memory W} (A : Archive) (leafProc : Procedure W) (fs : List Family) (L : Ledger u D id v keep initial i m)
    (hi : i<n) (_picked' : picked D i=true)
    (after : Memory W) (cv : (cur (ownerData W u) after).val=i+1)
    (limit : (after ((ownerData W u) 0+1).val).val=n) (owner : Recorded (ownerData W u) D after)
    (keep' : ∀ a,keep a → after a=m a)
    (old : ∀ j : Fin n,j.val < i → picked D j.val=true → ∀ a,(v j).uses u j.val a → after a=m a)
    (newRecord : (v ⟨i,hi⟩).Cached id u i after)
    (seedCost : ℕ) (stageCost : Family→ℕ)
    (wide : 2<2^W) (cursor : base u 18<2^W)
    (adr : nodeAddress u (bump (ownerData W u) m)+5<2^W)
    (stage : ∀ f∈fs,((bump (ownerData W u) m) (nodeAddress u (bump (ownerData W u) m))).val=kind f.mode →
      stageAddress u (bump (ownerData W u) m)+48<2^W ∧ f.oldPorts<2^W)
    (matched : ∀ f,fs.find? (matchesFamily u (bump (ownerData W u) m))=some f →
      (HistoryStageBody.procedure (layout u A f) f.childBound W).Exec (bump (ownerData W u) m) after (stageCost f))
    (leaf : fs.find? (matchesFamily u (bump (ownerData W u) m))=none →
      leafProc.Exec (bump (ownerData W u) m) after seedCost) :
    (body u A leafProc fs).Spec (·=bump (ownerData W u) m)
      (fun _ out=>Ledger u D id v keep initial (i+1) out)
      (bodyCost u (bump (ownerData W u) m) seedCost stageCost fs) := by
  have finish : Ledger u D id v keep initial (i+1) after :=
    L.next cv limit owner keep' old (fun j e _=> by
      obtain rfl : j=⟨i,hi⟩:=Fin.ext e
      exact newRecord)
  apply body_spec W u A leafProc fs _ _ seedCost stageCost wide cursor adr stage
  · intro f mem
    exact Procedure.Spec.mono (A:=HistoryStageBody.procedure (layout u A f) f.childBound W)
      (post:=fun _ out=>out=after) (matched f mem) (fun _ h=>h)
      (fun _ _ h=>h.symm ▸ finish) le_rfl
  · intro mem
    exact Procedure.Spec.mono (A:=leafProc) (post:=fun _ out=>out=after)
      (leaf mem) (fun _ h=>h) (fun _ _ h=>h.symm ▸ finish) le_rfl


theorem selected_cache (u : ℕ) (A : Archive) (leafProc : Procedure W) (fs : List Family) (input : Memory W)
    (D : Directory W n) (v : Fin n→NodeValue F) (tag : ((Fin 3→Bool)→F)→ℕ)
    (keep : ℕ→Prop) (cost : ℕ→ℕ) (cap : ℕ)
    (owner : Recorded (ownerData W u) D input)
    (len : (input ((ownerData W u) 4).val).val+(input ((ownerData W u) 5).val).val=n)
    (room : n<2^W) (different : ((ownerData W u) 0+1).val≠((ownerData W u) 0).val)
    (counts : ∀ j : Fin 2,((ownerData W u) ⟨4+j.val,by omega⟩).val≠((ownerData W u) 0).val)
    (dirs : ∀ i j,(addresses (ownerData W u) D i j).val≠((ownerData W u) 0).val ∧
      (addresses (ownerData W u) D i j).val≠((ownerData W u) 0+1).val)
    (immutable : ∀ a,keep a → a≠((ownerData W u) 0).val ∧ a≠((ownerData W u) 0+1).val)
    (aside : ∀ j : Fin n,∀ a,(v j).uses u j.val a → a≠((ownerData W u) 0).val)
    (seedCost : Fin n→ℕ) (stageCost : Fin n→Family→ℕ) (wide : 2<2^W) (ctrlRoom : base u 18<2^W)
    (dispatch : ∀ (j : Fin n) (m : Memory W),Ledger u D tag v keep input j.val m → picked D j.val=true →
      let before:=bump (ownerData W u) m
      (nodeAddress u before+5<2^W) ∧
      (∀ f∈fs,(before (nodeAddress u before)).val=kind f.mode →
        stageAddress u before+48<2^W ∧ f.oldPorts<2^W) ∧
      bodyCost u before (seedCost j) (stageCost j) fs ≤ cost j.val)
    (publish : ∀ (j : Fin n) (m : Memory W),Ledger u D tag v keep input j.val m → picked D j.val=true →
      let before:=bump (ownerData W u) m
      ∃ out : Memory W,
        ((∀ f,fs.find? (matchesFamily u before)=some f →
           (HistoryStageBody.procedure (layout u A f) f.childBound W).Exec before out (stageCost j f)) ∧
        (fs.find? (matchesFamily u before)=none →
           leafProc.Exec before out (seedCost j)) ∧
        (cur (ownerData W u) out).val=j.val+1 ∧ (out ((ownerData W u) 0+1).val).val=n ∧
        Recorded (ownerData W u) D out ∧ (∀ a,keep a → out a=m a) ∧
        (∀ t : Fin n,t.val<j.val → picked D t.val=true → ∀ a,(v t).uses u t.val a → out a=m a) ∧
        (v j).Cached tag u j.val out))
    (budget : 17+24*n+∑ root : Word W, (if D.owner root=(D.group,D.slot) then
      ∑ j : {i : Fin n // D.root i=root},cost j.val.val else 0) ≤ cap) :
    (selected u A leafProc fs).Spec (·=input) (fun _ out=>Ledger u D tag v keep input n out) cap := by
  classical
  let d:=ownerData W u
  let inv:=fun (_ : Memory W) i m=>Ledger u D tag v keep input i m
  have apart (i : Fin n) (j : Fin 5) : addresses d D i j≠d 0 :=
    fun eq=>(dirs i j).1 (congrArg Fin.val eq)
  change (HistoryNodeDirectory.Selected.procedure d (body u A leafProc fs)).Spec
    (·=input) (fun m out=>inv m n out) cap
  refine Procedure.Spec.mono (A:=HistoryNodeDirectory.Selected.procedure d (body u A leafProc fs))
    (procedure_owners d (body u A leafProc fs) D cost (·=input) inv ?_ ?_ ?_ apart ?_ ?_)
    (fun _ h=>h) (fun _ _ h=>h) budget
  · intro a eq; subst a
    exact Ledger.start d rfl owner len room different (counts 0) (counts 1) dirs immutable
  · intro _ i m L; exact ⟨L.cursor,L.stop⟩
  · intro _ i m L; exact L.directory
  · intro _ i m L h off
    exact L.skip h off room different apart (fun a h=>(immutable a h).1)
      (fun j _ _ a h=>aside j a h)
  · intro _ i _ hi on P R K M pc reg kd exit inst slots cfg bumped start live
    obtain ⟨m,L,rfl⟩:=live
    let j : Fin n:=⟨i,hi⟩
    obtain ⟨node,stage,enough⟩:=dispatch j m L on
    obtain ⟨out,matched,leaf,cursor,stop,recorded,stable,previous,current⟩:=publish j m L on
    obtain ⟨t,h,c',o,run,pc',post⟩:=
      visit A leafProc fs L hi on out cursor stop recorded stable previous current
        (seedCost j) (stageCost j) wide ctrlRoom node stage matched leaf
        M pc reg kd exit inst slots cfg (bump (ownerData W u) m) start rfl
    exact ⟨t,h.trans enough,c',o,run,pc',post⟩

end
end Hierarchy.HistorySelectedReceiverLoop

end OAI
