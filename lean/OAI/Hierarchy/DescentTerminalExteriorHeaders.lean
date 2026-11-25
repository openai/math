import OAI.Hierarchy.DescentTerminalFixedHeaders
import OAI.Hierarchy.DescentTerminalPublicGroup
import OAI.ThreeFlat.Routing.CallBatches

namespace OAI
/-! # Reached first-word and clipping controls of the sparse exterior group tape -/
namespace Hierarchy.DescentTerminalExteriorHeaders
open Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalPorts DescentTerminalCableOrder
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow DescentTerminalDenseHeader
open DescentTerminalHeaderGroups DescentTerminalPublicGroup
open ThreeFlat.Routing
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {D S p q : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} (N : Network D P bits) (home : N.Site→Fin S)
    (native : N.Edge ↪ Fin (Fintype.card N.Edge)) (external : P ↪ ℕ)
    (nodes : N.Site ↪ ℕ) (ops : ∀v,DescentKernelHistory.Boundary N v ↪ ℕ)
local notation "L" => order N home native p external nodes ops
abbrev Live (i : Fin S) := ∃nm : Names N p,Order.Used L i nm ∧ Order.neighbor L i nm=none

def block (i : Fin S) (g : Order.Group L i) :=
  chunkRows (groupLengths N L i g) (p:=p) (fun u=>by
    unfold groupLengths
    cases ((Order.inGroup L i g).symm u).val <;> exact Nat.min_le_left ..) q

def siteRows (i : Fin S) : List (Profile q p) :=
  if h : Live (p:=p) N home native external nodes ops i then
    block (p:=p) (q:=q) N home native external nodes ops i ⟨none,h⟩ else []

def stream : ℕ→List (Profile q p)
  | 0=>[]
  | k+1=>stream k++(if h:k<S then siteRows N home native external nodes ops ⟨k,h⟩ else [])
def prior (k : ℕ) := ∑z : P,if (home (N.attach z)).val<k then bits z else 0
def siteMass (i : Fin S) := ∑z : P,if home (N.attach z)=i then bits z else 0

theorem total (hp : 0<p) (i : Fin S) (g : Order.Group L i) (ext : g.val=none) :
    pref (groupLengths N L i g) (Fintype.card (Order.At L i g))=siteMass N home i := by
  rw [sum_before _ _ (le_refl _)]
  simp only [Fin.is_lt,ite_true]
  rw [←(Order.inGroup L i g).sum_comp]
  simp only [groupLengths,Equiv.symm_apply_apply]
  rw [←Finset.sum_subtype (Finset.univ.filter (fun x=>Order.Used L i x ∧ Order.neighbor L i x=g.val)) (by simp) (nameWidth N)]
  simp only [ext,Finset.sum_filter,Fintype.sum_sum_type,Fintype.sum_sigma,Order.neighbor,reduceCtorEq,
    and_false,ite_false,Finset.sum_const_zero,Nat.zero_add,and_true,Order.used_port]
  change (∑ z : P, ∑ l : Fin (poolBatchCount (bits z) p),
    if home (N.attach z) = i then nameWidth N (.inr ⟨z,l⟩) else 0) =
    ∑ z : P, if home (N.attach z) = i then bits z else 0
  apply Finset.sum_congr rfl
  intro z _
  by_cases live : home (N.attach z)=i
  · simp only [live,ite_true,nameWidth]
    exact sum_piece_sizes p (bits z) hp
  · simp [live]

theorem site_mass (hq : 0<q) (hp : 0<p) (i : Fin S) :
    listMass (siteRows (p:=p) (q:=q) N home native external nodes ops i)=siteMass N home i := by
  unfold siteRows
  split
  next h=>exact (chunks_all _ _ hq).trans (total N home native external nodes ops hp i ⟨none,h⟩ rfl)
  next off=>
    symm
    change (∑ z : P, if home (N.attach z) = i then bits z else 0) = 0
    apply Finset.sum_eq_zero
    intro z _
    by_cases atSite : home (N.attach z)=i
    · simp only [atSite,ite_true]
      by_contra ne
      have rows:=CallPool.count_le_batches_mul (bits z) p hp
      have live : 0 < poolBatchCount (bits z) p := by
        by_contra! zero
        rw [Nat.eq_zero_of_le_zero zero, Nat.mul_zero] at rows
        exact ne (Nat.eq_zero_of_le_zero rows)
      exact off ⟨.inr ⟨z,⟨0,live⟩⟩,(Order.used_port L i z _).2 atSite,rfl⟩
    · simp [atSite]

theorem stream_mass (hq : 0<q) (hp : 0<p) (k : ℕ) :
    listMass (stream (p:=p) (q:=q) N home native external nodes ops k)=prior N home k := by
  induction k with
  | zero=>simp [stream,listMass,prior]
  | succ k ih=>
    rw [stream,mass_append,ih]
    by_cases hk:k<S
    · rw [dite_eq_left hk,site_mass N home native external nodes ops hq hp,prior,siteMass,prior,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      simp only [Fin.ext_iff]
      split_ifs <;> omega
    · rw [dite_eq_right hk]
      simp only [listMass,List.map_nil,List.sum_nil,add_zero,prior]
      apply Finset.sum_congr rfl
      intro z _
      have:= (home (N.attach z)).isLt
      split_ifs <;> omega

theorem stream_append (i : Fin S) (g : Order.Group L i) (ext : g.val=none) :
    ∃endRows,stream (p:=p) (q:=q) N home native external nodes ops S=
      stream (p:=p) (q:=q) N home native external nodes ops i.val++block (p:=p) (q:=q) N home native external nodes ops i g++endRows := by
  have live : Live (p:=p) N home native external nodes ops i:=by simpa only [ext] using g.property
  have start : stream (p:=p) (q:=q) N home native external nodes ops (i.val+1)=
      stream (p:=p) (q:=q) N home native external nodes ops i.val++block (p:=p) (q:=q) N home native external nodes ops i g := by
    simp only [stream,dite_eq_left i.isLt,siteRows,dite_eq_left live,Fin.eta]
    rw [show (⟨none,live⟩ : Order.Group L i)=g from Subtype.ext ext.symm]
  have startLe : i.val+1 ≤ S:=i.isLt
  obtain ⟨k,h⟩:=Nat.exists_eq_add_of_le startLe
  have post (t : ℕ) : ∃l,stream (p:=p) (q:=q) N home native external nodes ops (i.val+1+t)=
      stream (p:=p) (q:=q) N home native external nodes ops (i.val+1)++l := by
    induction t with
    | zero=>exact ⟨[],by simp⟩
    | succ t ih=>
      obtain ⟨l,eq⟩:=ih
      exact ⟨_,by rw [Nat.add_succ,stream,eq,List.append_assoc]⟩
  obtain ⟨l,eq⟩:=post k
  exact ⟨l,by rw [←h,start] at eq;exact eq⟩

theorem physical_headers {bitsW nFixed : ℕ} (layout : DescentTerminalDenseHeaderRAM.Layout) (m : Memory bitsW)
    (hq : 0<q) (hp : 0<p) (room : (stream (p:=p) (q:=q) N home native external nodes ops S).length ≤ nFixed)
    (fit : DescentTerminalDenseHeaderRAM.Fits layout bitsW nFixed)
    (reads : DescentTerminalDenseHeaderRAM.Reads layout (padded (n:=nFixed) (stream (p:=p) (q:=q) N home native external nodes ops S)) m) :
    let _all:=stream (p:=p) (q:=q) N home native external nodes ops S
    ∃after,(DescentTerminalDenseHeaderRAM.program bitsW nFixed layout).Exec m after (DescentTerminalDenseHeaderRAM.cost nFixed layout) ∧
      ∀(i:Fin S) (g : Order.Group L i) (_ext:g.val=none) (r : Fin (poolBatchCount (Fintype.card (Order.At L i g)) q)),
      let pre:=stream (p:=p) (q:=q) N home native external nodes ops i.val
      let len:=groupLengths N L i g
      let small : ∀k,len k ≤ p:=fun k=>by dsimp [len,groupLengths];cases ((Order.inGroup L i g).symm k).val <;> exact Nat.min_le_left ..
      after (layout.index.base+(pre.length+r.val))=((first len q (siteBase N home i) r.val/(q*p):ℕ):Word bitsW) ∧
      after (layout.control.base+(pre.length+r.val))=((formatIndex q p (format len (Nat.mul_pos hq hp) small (siteBase N home i) r.val)).val:Word bitsW) := by
  intro all
  obtain ⟨after,run,_,written⟩:=fixed_scan layout all room (Nat.mul_pos hq hp) m fit reads
  refine ⟨after,run,?_⟩
  intro i g ext r pre len small
  obtain ⟨tail,split⟩:=stream_append (q:=q) N home native external nodes ops i g ext
  have rin : r.val<(block (p:=p) (q:=q) N home native external nodes ops i g).length:=by simp [block]
  have decomposition : all=pre++block (p:=p) (q:=q) N home native external nodes ops i g++tail := split
  have bound : pre.length+r.val<all.length := by
    rw [decomposition,List.length_append,List.length_append]
    omega
  let k:Fin all.length:=⟨_,bound⟩
  have start : priorBits all.get k.val=first len q (siteBase N home i) r.val := by
    rw [prior_list all _ k.isLt.le]
    have cut : all.take k.val=pre++(block (p:=p) (q:=q) N home native external nodes ops i g).take r.val := by
      change all.take (pre.length+r.val)=_
      rw [decomposition,List.append_assoc,List.take_append]
      simp [List.take_append_of_le_length rin.le]
    rw [cut,mass_append,show listMass pre=prior N home i.val from stream_mass N home native external nodes ops hq hp i.val]
    rw [show prior N home i.val=siteBase N home i by simp only [prior,siteBase,Finset.sum_filter,Fin.lt_def]]
    exact congrArg (_+·) (chunk_mass len small r.val r.isLt.le)
  have selected : all[pre.length+r.val]?=some (rowProfile len small r.val) := by
    rw [show all=pre++(block (p:=p) (q:=q) N home native external nodes ops i g++tail) by
      simpa [all,pre,List.append_assoc] using split]
    rw [List.getElem?_append_right (Nat.le_add_right pre.length r.val),Nat.add_sub_cancel_left,
      List.getElem?_append_left rin,List.getElem?_eq_getElem rin]
    simp [block,chunkRows,len]
  have atK : all.get k=rowProfile len small r.val := by
    rw [List.getElem?_eq_getElem k.isLt] at selected
    exact Option.some.inj selected
  obtain ⟨index,fmt⟩:=written k
  constructor
  · exact index.trans (congrArg (fun z : ℕ=>((z/(q*p):ℕ):Word bitsW)) start)
  · have pos:=Nat.mul_pos hq hp
    have residue : (⟨priorBits all.get k.val%(q*p),Nat.mod_lt _ pos⟩:Fin (q*p))=
        ⟨first len q (siteBase N home i) r.val%(q*p),Nat.mod_lt _ pos⟩ :=
      Fin.ext (congrArg (fun z : ℕ=>z%(q*p)) start)
    change after (layout.control.base+k.val)=
      ((formatIndex q p (format len pos small (siteBase N home i) r.val)).val:Word bitsW)
    rw [fmt,DescentTerminalDenseHeaderRAM.Header,atK,residue,control_row len small pos]

end
end Hierarchy.DescentTerminalExteriorHeaders

end OAI
