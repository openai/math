import OAI.Hierarchy.DescentTerminalNeighborCalendar
import OAI.Hierarchy.DescentSortedRoster

namespace OAI
/-! # Fixed H-times-D count rows, including empty neighbor entries and the reverse side -/
namespace Hierarchy.DescentTerminalGrainProfiles
open Computability.BorderVNP.Crossing DescentTerminalCableOrder DescentTerminalHeaderGroups DescentSortedRoster
open scoped Classical BigOperators
noncomputable section

variable {H D:ℕ} (R:Fin H→Fin D→Option (Fin H))

def picked (v:Fin H) (j:Fin D) : Option ℕ := do
  let u←R v j
  if v≤u then some (pair v u) else none

theorem picked_eq {v:Fin H} {j:Fin D} {t:ℕ} :
    picked R v j=some t ↔ ∃u,R v j=some u ∧ v≤u ∧ pair v u=t := by
  cases h:R v j with
  | none=>simp [picked,h]
  | some u=>by_cases pos:v≤u <;> simp [picked,h,pos]

def slotKey (i:Fin (H*D)):=let ij:=finProdFinEquiv.symm i;picked R ij.1 ij.2
def goodKeys:=(List.finRange (H*D)).filterMap (slotKey R)
def Sorted:Prop:=∀v (a b:Fin D) {x y},R v a=some x→R v b=some y→a<b→x<y

theorem sorted_mounted (peer:Fin H→Fin D→Option (Fin H)) : Sorted (indexed peer) := by
  intro v a b x y left right ab
  obtain ⟨mem,low⟩:=(indexed_iff peer v a x).1 left
  obtain ⟨has,high⟩:=(indexed_iff peer v b y).1 right
  rcases lt_trichotomy x y with xy|e|yx
  · exact xy
  · subst y;omega
  · have:=before_strict peer has yx
    omega

theorem sorted_keys (ordered:Sorted R) : (goodKeys R).Pairwise (·<·):=by
  apply List.pairwise_filterMap.mpr
  apply (List.pairwise_lt_finRange (H*D)).imp
  intro a b ab x left y right
  let va:=finProdFinEquiv.symm a
  let vb:=finProdFinEquiv.symm b
  obtain ⟨u,ua,small,rfl⟩:=(picked_eq R).1 left
  obtain ⟨v,vbHit,above,rfl⟩:=(picked_eq R).1 right
  have addr (m:Fin (H*D)) :
      m.val=(finProdFinEquiv.symm m : Fin H×Fin D).1.val*D+(finProdFinEquiv.symm m : Fin H×Fin D).2.val := by
    simpa only [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using
      congrArg Fin.val (finProdFinEquiv.apply_symm_apply m).symm
  have addrOrder:va.1.val*D+va.2.val<vb.1.val*D+vb.2.val:=by rw [←addr a,←addr b];exact ab
  change pair va.1 u < pair vb.1 v
  have first : va.1.val ≤ u.val := small
  have second : vb.1.val ≤ v.val := above
  simp only [pair,min_eq_left first,max_eq_right first,min_eq_left second,max_eq_right second]
  apply (digit_lt u.isLt v.isLt).2
  rcases (digit_lt va.2.isLt vb.2.isLt).1 addrOrder with lt|⟨eq,slots⟩
  · exact Or.inl lt
  · refine Or.inr ⟨eq,?_⟩
    have homes:va.1=vb.1:=Fin.ext eq
    have leftEntry : R va.1 va.2 = some u := ua
    rw [homes] at leftEntry
    exact ordered vb.1 va.2 vb.2 leftEntry vbHit slots

theorem slot_calendar (ordered:Sorted R) : goodKeys R=calendar (present R) := by
  have one:=sorted_keys R ordered
  have two:=calendar_sorted (present R)
  have extSet : (goodKeys R).toFinset=(calendar (present R)).toFinset := by
    ext t
    simp only [List.mem_toFinset,goodKeys,List.mem_filterMap,List.mem_finRange,true_and,mem_calendar,
      present,Finset.mem_filter,Finset.mem_univ]
    constructor
    · rintro ⟨i,h⟩
      obtain ⟨u,hit,up,eqn⟩:=(picked_eq R).1 h
      exact ⟨_,u,⟨(finProdFinEquiv.symm i).2,hit⟩,up,eqn⟩
    · rintro ⟨i,u,⟨j,hit⟩,up,eqn⟩
      exact ⟨finProdFinEquiv (i,j),by simpa [slotKey] using (picked_eq R).2 ⟨u,hit,up,eqn⟩⟩
  rw [←((List.toFinset_sort (·≤·) (one.imp (fun ab=>ne_of_lt ab))).mpr (one.imp le_of_lt)),
    ←((List.toFinset_sort (·≤·) (two.imp (fun ab=>ne_of_lt ab))).mpr (two.imp le_of_lt)),extSet]

variable {d p:ℕ} {P:Type} [Fintype P] {bits:P→ℕ} (N:Network d P bits) (home:N.Site→Fin H)
    (native:N.Edge↪Fin (Fintype.card N.Edge)) (external:P↪ℕ) (nodes:N.Site↪ℕ) (ops:∀v,DescentKernelHistory.Boundary N v↪ℕ)

def slotCount (i:Fin (H*D)) := (slotKey R i).elim 0 (fun t=>pairMass N home t/p)

/-- Fixed count rows H*D are consumed by the native prefix even on empty graphs. -/
theorem slot_stream (hp:0<p) (internal:∀e,p∣N.width e) («public»:∀z,p∣bits z)
    (ordered:Sorted R) (covers:∀e,0<N.width e→home (N.dst e)∈present R (home (N.src e)) ∧
      home (N.src e)∈present R (home (N.dst e))) (q:ℕ) :
    (List.ofFn (slotCount (p:=p) R N home)).flatMap (rows q p)=stream N home native external nodes ops q hp (H*H) := by
  have drop (l:List (Fin (H*D))) :
      (l.map (slotCount (p:=p) R N home)).flatMap (rows q p)=
        (l.filterMap (slotKey R)).flatMap (fun t=>rows q p (pairMass N home t/p)) := by
    induction l with
    | nil=>rfl
    | cons i l ih=>cases h:slotKey R i <;> simp [slotCount,h,ih]
  rw [List.ofFn_eq_map,drop]
  change (goodKeys R).flatMap _=_
  rw [slot_calendar R ordered]
  exact cable_stream N home native external nodes ops hp internal «public» q (H*H) _ (calendar_catalog _ N home covers)

end
end Hierarchy.DescentTerminalGrainProfiles

end OAI
