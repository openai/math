import OAI.Hierarchy.DescentTerminalNeighborSlots
import OAI.Hierarchy.DescentTerminalPublicWidthTape

namespace OAI
/-! # The source header offset for either endpoint is the original canonical prefix -/
namespace Hierarchy.DescentTerminalGrainProfiles
open Computability.BorderVNP.Crossing DescentTerminalCableOrder DescentTerminalSparseHeader DescentSortedRoster
open DescentTerminalHeaderGroups DescentTerminalWidthRowsRAM
open scoped Classical
noncomputable section

variable {D H : ℕ} (R : Fin H→Fin D→Option (Fin H))
private def prior (i : Fin (H*D)) := ((List.finRange (H*D)).take i.val).filterMap (slotKey R)

private theorem separates (ordered:Sorted R) (i:Fin (H*D)) (t:ℕ) (here:slotKey R i=some t) :
    ∀x,x∈prior R i ↔ x∈goodKeys R ∧ x<t := by
  let all_:=List.finRange (H*D)
  let rest:=(all_.drop (i.val+1)).filterMap (slotKey R)
  have eqn : goodKeys R=prior R i++t::rest := by
    have lt:i.val<all_.length:=by simp [all_]
    have head : all_[i.val]=i:=by simp [all_]
    have e:=List.take_append_drop i.val all_
    rw [List.drop_eq_getElem_cons lt,head] at e
    change all_.filterMap (slotKey R)=_
    conv_lhs => rw [←e]
    simp only [List.filterMap_append,List.filterMap_cons,here]; rfl
  have order_:=sorted_keys R ordered
  rw [eqn,List.pairwise_append,List.pairwise_cons] at order_
  intro x
  rw [eqn]
  constructor
  · intro hx
    exact ⟨List.mem_append_left _ hx,order_.2.2 x hx t (by simp)⟩
  · rintro ⟨hx,lt⟩
    rcases List.mem_append.mp hx with old|nxt
    · exact old
    · rcases List.mem_cons.mp nxt with eq|after
      · omega
      · have:=order_.2.1.1 x after;omega

variable {deg p:ℕ} {P:Type} [Fintype P] {bits:P→ℕ} (N:Network deg P bits) (home:N.Site→Fin H)
    (native:N.Edge↪Fin (Fintype.card N.Edge)) (ext:P↪ℕ) (nodes:N.Site↪ℕ) (ops:∀v,DescentKernelHistory.Boundary N v↪ℕ)
    (hp:0<p) (edges:∀e,p∣N.width e) (ports:∀z,p∣bits z)
    (ordered:Sorted R) (covers:∀e,0<N.width e→home (N.dst e)∈present R (home (N.src e)) ∧
      home (N.src e)∈present R (home (N.dst e)))

include hp edges ports ordered covers in
theorem canonical_prefix (q:ℕ) (i:Fin (H*D)) (t:ℕ) (here:slotKey R i=some t) :
    passed q p (slotCount (p:=p) R N home) i.val=
      stream N home native ext nodes ops q hp t := by
  have total:(goodKeys R).filter (fun n=>decide (0<pairMass N home n))=(occupied N home (H*H)).sort := by
    rw [slot_calendar R ordered,calendar_catalog _ _ _ covers]
  have valid : t<H*H := by
    obtain ⟨j,_,up,rfl⟩:=(picked_eq R).1 here
    let v := (finProdFinEquiv.symm i : Fin H × Fin D).1
    have orderedValues : v.val ≤ j.val := up
    change min v.val j.val * H + max v.val j.val < H * H
    rw [min_eq_left orderedValues, max_eq_right orderedValues]
    calc
      v.val * H + j.val < v.val * H + H := Nat.add_lt_add_left j.isLt _
      _ = (v.val + 1) * H := (Nat.succ_mul _ _).symm
      _ ≤ H * H := Nat.mul_le_mul_right H v.isLt
  let pos:=fun n=>decide (0<pairMass N home n)
  have setEq : ((prior R i).filter pos).toFinset=occupied N home t := by
    ext x
    have key := separates R ordered i t here x
    have spec : (x∈goodKeys R ∧ 0<pairMass N home x) ↔ x∈occupied N home (H*H) := by
      simpa [List.mem_filter] using (congrArg (fun l:List ℕ=>x∈l) total).to_iff
    simp only [List.mem_toFinset,List.mem_filter,pos,decide_eq_true_eq,key]
    unfold occupied at spec ⊢
    simp only [Finset.mem_filter] at spec ⊢
    constructor
    · rintro ⟨⟨mem,lt⟩,mass⟩
      exact ⟨(spec.mp ⟨mem,mass⟩).1,lt⟩
    · rintro ⟨live,lt⟩
      have good:=spec.mpr ⟨live,lt.trans valid⟩
      exact ⟨⟨good.1,lt⟩,good.2⟩
  have sorted : (prior R i).Pairwise (·<·) := by
    have h:=List.pairwise_filterMap.mp (sorted_keys R ordered)
    apply List.pairwise_filterMap.mpr
    exact h.take
  have ranked:=sorted.filter pos
  have keys:(prior R i).filter pos=(occupied N home t).sort := by
    rw [←setEq]
    exact ((List.toFinset_sort (·≤·) (ranked.imp (fun ab=>ne_of_lt ab))).mpr (ranked.imp (fun ab=>le_of_lt ab))).symm
  let code:=fun z=>rows q p (pairMass N home z/p)
  have drop (l:List (Fin (H*D))) : (l.map (slotCount (p:=p) R N home)).flatMap (rows q p)=
      (l.filterMap (slotKey R)).flatMap code := by
    induction l with
    | nil=>rfl
    | cons j l ih=>cases h:slotKey R j <;> simp [slotCount,h,code,ih]
  have takeEq : passed q p (slotCount (p:=p) R N home) i.val=(prior R i).flatMap code := by
    rw [passed,List.ofFn_eq_map,← List.map_take]
    exact drop ((List.finRange (H*D)).take i.val)
  exact takeEq.trans (cable_stream N home native ext nodes ops hp edges ports q t _ keys)

end
end Hierarchy.DescentTerminalGrainProfiles

end OAI
