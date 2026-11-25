import OAI.ThreeFlat.RAM.HistoryNodeFromSite
import OAI.ThreeFlat.RAM.HistorySelectedLedger
import OAI.ThreeFlat.RAM.HistoryNodeValueRetain
import OAI.ThreeFlat.Diagonal.HistorySelectedChronology
import OAI.ThreeFlat.RAM.HistoryStageBody
import OAI.ThreeFlat.RAM.HistorySelectedCharge
import OAI.ThreeFlat.RAM.HistoryGeneratedStore

namespace OAI
/-! # Chronological publication of the selected factor streams and endpoint words -/
namespace ThreeFlat.RAM.HistoryStageBody.Physical

open Computability.VPVNP.BurstRAM PrivateRAM HistoryNodeDirectory HistoryNodeDirectory.Selected PhysicalProcedure
open Diagonal.HistoryContraction Diagonal.TickWorkspace
open scoped BigOperators Fin.CommRing
noncomputable section

variable {F : Type*} {W n : ℕ}

theorem stage_addresses (u seedCount cap : ℕ) (archive : Archive) (family : Family)
    (raw : ℕ→ℕ) (i : ℕ)
    (idx : (HistoryStageBody.numInput (layout u archive family) cap raw).id=i)
    (later : seedCount≤ i) :
    let T:=HistoryStageBody.numInput (layout u archive family) cap raw
    T.stream=streamAt u seedCount i ∧ T.ext=endsAt u seedCount i := by
  let T:=HistoryStageBody.numInput (layout u archive family) cap raw
  change HistoryScratch.atWord (base u 12) (volume u) family.motifs family.parties T.id
      ⟨0,0,5,0⟩ 0=streamAt u seedCount i ∧
    HistoryScratch.atWord (base u 12) (volume u) family.motifs family.parties T.id
      ⟨0,0,5,1⟩ 0=endsAt u seedCount i
  change T.id=i at idx
  rw [idx]
  simp only [HistoryScratch.atWord,HistoryScratch.sector,Nat.zero_mul,Nat.zero_add,
    Nat.add_zero,endsAt,streamAt,ite_eq_right (Nat.not_lt.mpr later)]
  constructor <;> ring

namespace NodeValue
variable (v : NodeValue F) (id : ((Fin 3→Bool)→F)→ℕ)

/-- Earlier nodes occupy half-open S12 blocks of width V². -/
theorem uses_before {u i j a : ℕ} (earlier : i<j)
    (rows : v.stream+4*v.net.cells≤base u 12+(i+1)*(volume u)^2)
    (ends : v.ext+v.external≤base u 12+(i+1)*(volume u)^2)
    (addr : v.uses u i a) :
    (base u 13≤a ∧ a<base u 13+8*j) ∨ a<base u 12+j*(volume u)^2 := by
  have next : base u 12+(i+1)*(volume u)^2 ≤ base u 12+j*(volume u)^2 :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt earlier)) _
  rcases addr with h|h|h
  · left; omega
  · exact Or.inr (h.2.trans_le (rows.trans next))
  · exact Or.inr (h.2.trans_le (ends.trans next))

end NodeValue

namespace Ledger
variable {u : ℕ} {D : Directory W n} {id : ((Fin 3→Bool)→F)→ℕ} {v : Fin n→NodeValue F}
  {keep : ℕ→Prop} {input m out : Memory W} {i : ℕ}

theorem next (L : Ledger u D id v keep input i m) (cur' : (cur (ownerData W u) out).val=i+1)
    (stop' : (out ((ownerData W u) 0+1).val).val=n) (directory : Recorded (ownerData W u) D out)
    (safe : ∀ a,keep a → out a=m a)
    (prior : ∀ j : Fin n,j.val< i → picked D j.val=true → ∀ a,(v j).uses u j.val a → out a=m a)
    (current : ∀ j : Fin n,j.val=i → picked D j.val=true → (v j).Cached id u j.val out) :
    Ledger u D id v keep input (i+1) out := by
  refine ⟨cur',stop',directory,fun a ha=>(safe a ha).trans (L.durable a ha),?_⟩
  intro j before live
  by_cases eq : j.val=i
  · exact current j eq live
  · have less : j.val< i := by omega
    exact NodeValue.Cached.retain (v j) id (L.published j less live) (prior j less live)

theorem start (data : HistoryNodeDirectory.Selected.Data W) (shape : data=ownerData W u)
    (preOwner : Recorded data D input)
    (bounds : (input (data 4).val).val+(input (data 5).val).val=n)
    (room : n<2^W) (different : (data 0+1).val≠(data 0).val)
    (root : (data 4).val≠(data 0).val) (len : (data 5).val≠(data 0).val)
    (dirs : ∀ i j,(addresses data D i j).val≠(data 0).val ∧
      (addresses data D i j).val≠(data 0+1).val)
    (safe : ∀ a,keep a → a≠(data 0).val ∧ a≠(data 0+1).val) :
    Ledger u D id v keep input 0 («initialize» data input) := by
  subst data
  let d:=ownerData W u
  have value : (input (d 4).val+input (d 5).val).val=n := by
    change ((input (d 4).val).val+(input (d 5).val).val)%(2^W)=n
    rw [bounds,Nat.mod_eq_of_lt room]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [cur,«initialize»,writeMemory,Ne.symm different]
  · simpa [«initialize»,writeMemory,root,len] using value
  · intro i j
    obtain ⟨a,b⟩:=dirs i j
    simpa [«initialize»,writeMemory,a,b] using preOwner i j
  · intro a h
    obtain ⟨x,y⟩:=safe a h
    simp [«initialize»,writeMemory,x,y]
  · intro j h
    omega

theorem skip (L : Ledger u D id v keep input i m) (lt : i<n) (off : picked D i=false)
    (room : n<2^W) (different : ((ownerData W u) 0+1).val≠((ownerData W u) 0).val)
    (apart : ∀ i j,addresses (ownerData W u) D i j≠(ownerData W u) 0)
    (safe : ∀ a,keep a → a≠((ownerData W u) 0).val)
    (cache : ∀ j : Fin n,j.val< i → picked D j.val=true → ∀ a,(v j).uses u j.val a → a≠((ownerData W u) 0).val) :
    Ledger u D id v keep input (i+1) (bump (ownerData W u) m) := by
  let d:=ownerData W u
  have grow : ((cur d m + 1:Word W)).val=i+1 := by
    have cursor : cur d m = (i : Word W) := by
      apply Fin.ext
      rw [Fin.val_cast_of_lt (lt.trans room)]
      exact L.cursor
    rw [cursor, ← Nat.cast_one (R := Word W), ← Nat.cast_add,
      Fin.val_cast_of_lt (show i+1 < 2^W by omega)]
  apply L.next
  · simpa [cur,bump,writeMemory,d] using grow
  · simpa [bump,writeMemory,different] using L.stop
  · exact recorded_bump _ D m L.directory apart
  · intro a h; simp [bump,writeMemory,safe a h]
  · intro j hj hj' a ha; simp [bump,writeMemory,cache j hj hj' a ha]
  · intro j eq on; rw [eq,off] at on; contradiction

end Ledger

/-- Execute the actual finite guard dispatch at a visited node. Each local body returns the
newly published S12/S13 record and retains the preceding records at their three precise spans. -/
theorem visit {u i : ℕ} {D : Directory W n} {id : ((Fin 3→Bool)→F)→ℕ} {v : Fin n→NodeValue F}
    {keep : ℕ→Prop} {initial m : Memory W} (A : Archive) (B : TraceBucketAtom.Layout)
    (pub : Fin TraceEndpointROM.params→Word W) (fs : List Family) (L : Ledger u D id v keep initial i m)
    (hi : i<n) (_picked' : picked D i=true)
    (after : Memory W) (cv : (cur (ownerData W u) after).val=i+1)
    (limit : (after ((ownerData W u) 0+1).val).val=n) (owner : Recorded (ownerData W u) D after)
    (keep' : ∀ a,keep a → after a=m a)
    (old : ∀ j : Fin n,j.val< i → picked D j.val=true → ∀ a,(v j).uses u j.val a → after a=m a)
    (newRecord : (v ⟨i,hi⟩).Cached id u i after)
    (seedCost : ℕ) (stageCost : Family→ℕ)
    (wide : 2<2^W) (cursor : base u 18<2^W)
    (adr : nodeAddress u (bump (ownerData W u) m)+5<2^W)
    (stage : ∀ f∈fs,((bump (ownerData W u) m) (nodeAddress u (bump (ownerData W u) m))).val=kind f.mode →
      stageAddress u (bump (ownerData W u) m)+48<2^W ∧ f.oldPorts<2^W)
    (matched : ∀ f,fs.find? (matchesFamily u (bump (ownerData W u) m))=some f →
      (HistoryStageBody.procedure (layout u A f) f.childBound W).Exec (bump (ownerData W u) m) after (stageCost f))
    (leaf : fs.find? (matchesFamily u (bump (ownerData W u) m))=none →
      (HistoryInitialSeed.procedure W (Physical.initial u B) pub).Exec (bump (ownerData W u) m) after seedCost) :
    (body W u A B pub fs).Spec (·=bump (ownerData W u) m)
      (fun _ out=>Ledger u D id v keep initial (i+1) out)
      (bodyCost u (bump (ownerData W u) m) seedCost stageCost fs) := by
  have finish : Ledger u D id v keep initial (i+1) after :=
    L.next cv limit owner keep' old (fun j e _=> by
      obtain rfl : j=⟨i,hi⟩:=Fin.ext e
      exact newRecord)
  apply body_spec W u A B pub fs _ _ seedCost stageCost wide cursor adr stage
  · intro f mem
    exact Procedure.Spec.mono (A:=HistoryStageBody.procedure (layout u A f) f.childBound W)
      (post:=fun _ out=>out=after) (matched f mem) (fun _ h=>h)
      (fun _ _ h=>h.symm ▸ finish) le_rfl
  · intro mem
    exact Procedure.Spec.mono (A:=HistoryInitialSeed.procedure W (Physical.initial u B) pub)
      (post:=fun _ out=>out=after) (leaf mem) (fun _ h=>h)
      (fun _ _ h=>h.symm ▸ finish) le_rfl

/-- The actual selected program returns the full chosen root cache. Its total fuel
is indexed by the published terminal owners, so every successful S12 publication can
be charged to that root using the chronological subtree bound. -/
theorem selected_cache (u : ℕ) (A : Archive) (B : TraceBucketAtom.Layout)
    (pub : Fin TraceEndpointROM.params→Word W) (fs : List Family) (input : Memory W)
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
           (HistoryInitialSeed.procedure W (Physical.initial u B) pub).Exec before out (seedCost j)) ∧
        (cur (ownerData W u) out).val=j.val+1 ∧ (out ((ownerData W u) 0+1).val).val=n ∧
        Recorded (ownerData W u) D out ∧ (∀ a,keep a → out a=m a) ∧
        (∀ t : Fin n,t.val<j.val → picked D t.val=true → ∀ a,(v t).uses u t.val a → out a=m a) ∧
        (v j).Cached tag u j.val out))
    (budget : 17+24*n+∑ root : Word W, (if D.owner root=(D.group,D.slot) then
      ∑ j : {i : Fin n // D.root i=root},cost j.val.val else 0) ≤ cap) :
    (selected W u A B pub fs).Spec (·=input) (fun _ out=>Ledger u D tag v keep input n out) cap := by
  classical
  let d:=ownerData W u
  let inv:=fun (_ : Memory W) i m=>Ledger u D tag v keep input i m
  have apart (i : Fin n) (j : Fin 5) : addresses d D i j≠d 0 :=
    fun eq=>(dirs i j).1 (congrArg Fin.val eq)
  change (HistoryNodeDirectory.Selected.procedure d (body W u A B pub fs)).Spec
    (·=input) (fun m out=>inv m n out) cap
  refine Procedure.Spec.mono (A:=HistoryNodeDirectory.Selected.procedure d (body W u A B pub fs))
    (procedure_owners d (body W u A B pub fs) D cost (·=input) inv ?_ ?_ ?_ apart ?_ ?_)
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
      visit A B pub fs L hi on out cursor stop recorded stable previous current
        (seedCost j) (stageCost j) wide ctrlRoom node stage matched leaf
        M pc reg kd exit inst slots cfg (bump (ownerData W u) m) start rfl
    exact ⟨t,h.trans enough,c',o,run,pc',post⟩


end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
