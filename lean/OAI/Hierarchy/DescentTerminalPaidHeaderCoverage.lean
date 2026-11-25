import OAI.Hierarchy.DescentTerminalPaidHeaderRAM
import OAI.Hierarchy.DescentTerminalScatterColumns

namespace OAI
/-! # Exactly one issued event per actual paid port row, with gaps and table rows inactive -/
namespace Hierarchy.DescentTerminalPaidHeaderEvents
open DescentTerminalChipSource DescentTerminalRecipeRows DescentTerminalBinPack
open DescentTerminalSpanBook ProtocolRAMPortRanks
open scoped BigOperators Classical
noncomputable section
variable {d G H W q K:ℕ}

private def earlier (size:Fin d→ℕ) (ls:List (Fin d)) (j:Fin d) :=
  (ls.map (fun k=>if k<j then size k else 0)).sum
private theorem earlier_all (size:Fin d→ℕ) (ls:List (Fin d)) (j:Fin d) (h:∀t∈ls,j≤t) :
    earlier size ls j=0 := by
  induction ls with
  | nil=>rfl
  | cons a l ih=>
    have a₀:=h a (by simp)
    have tl:=ih (fun t ht=>h t (by simp [ht]))
    change (if a<j then size a else 0)+earlier size l j=0
    simp [not_lt.mpr a₀,tl]

private theorem findAt (size:Fin d→ℕ) (ls:List (Fin d)) (sorted:ls.Pairwise (·<·))
    (j:Fin d) (mem:j∈ls) (r:Fin (size j)) :
    locate size ls (earlier size ls j+r.val)=some (j,r.val) := by
  induction ls with
  | nil=>simp at mem
  | cons a ls ih=>
    obtain ⟨head,tail⟩:=List.pairwise_cons.mp sorted
    rcases List.mem_cons.mp mem with eqn|later
    · subst j
      have zero:=earlier_all size ls a (fun t ht=>(head t ht).le)
      change locate size (a::ls) ((if a<a then size a else 0)+earlier size ls a+r.val)=_
      simp [zero,locate,r.isLt]
    · have less:=head j later
      change locate size (a::ls) ((if a<j then size a else 0)+earlier size ls j+r.val)=_
      simpa [less,locate,Nat.add_assoc] using ih tail later

private theorem miss (size:Fin d→ℕ) (ls:List (Fin d)) (r:ℕ) (after_:(ls.map size).sum≤r) :
    locate size ls r=none := by
  induction ls generalizing r with
  | nil=>rfl
  | cons a ls ih=>
    change size a+(ls.map size).sum≤r at after_
    simp [locate,show ¬r<size a by omega,ih (r-size a) (by omega)]

theorem at_address (size:Fin d→ℕ) (j:Fin d) (r:Fin (size j)) :
    locate size (List.finRange d) (ProtocolRAMPortRanks.prefix size Fin.val j+r.val)=some (j,r.val) := by
  have eqn:earlier size (List.finRange d) j=ProtocolRAMPortRanks.prefix size Fin.val j :=
    by simp [earlier,List.finRange,List.map_ofFn,Function.comp_def,List.sum_ofFn,ProtocolRAMPortRanks.prefix,Finset.sum_filter]
  rw [←eqn]; apply findAt size _ _ _ (List.mem_finRange j) r
  exact (List.sortedLT_finRange d).pairwise

theorem past_last (size:Fin d→ℕ) (r:ℕ) (after_:(∑j,size j)≤r) :
    locate size (List.finRange d) r=none :=
  miss size _ r (by simpa [List.finRange,List.map_ofFn,Function.comp_def,List.sum_ofFn] using after_)

/-- A local slot can be physically reserved with zero rows; only occupied slots occur in
the mathematical per-site group ordinal. The injection records their original sorted order. -/
structure Slots (sites:Fin H→Site) (q d:ℕ) where
  width : Fin H→Fin d→ℕ
  place : ∀h,Fin (sites h).groups↪Fin d
  order : ∀h,StrictMono (place h)
  actual : ∀h g,width h (place h g)=(sites h).chunks q g
  absent : ∀h t,(∀g,place h g≠t)→width h t=0

namespace Slots
variable {sites:Fin H→Site} (S:Slots sites q d)
theorem subtotal (h:Fin H) (j:Fin (sites h).groups) :
    ProtocolRAMPortRanks.prefix (S.width h) Fin.val (S.place h j)=
      ProtocolRAMPortRanks.prefix ((sites h).chunks q) Fin.val j := by
  classical
  simp only [ProtocolRAMPortRanks.prefix,Finset.sum_filter]
  symm
  apply Fintype.sum_of_injective (S.place h) (S.place h).injective
  · intro t miss_
    have off:=S.absent h t (fun a eqn=>miss_ ⟨a,eqn⟩)
    simp [off]
  · intro a
    have ord : (S.place h a).val<(S.place h j).val ↔ a.val<j.val := (S.order h).lt_iff_lt
    simp only [S.actual,ord]

theorem total (h:Fin H) : (∑j,S.width h j)=(sites h).portRows q := by
  classical
  symm; apply Fintype.sum_of_injective (S.place h) (S.place h).injective
  · intro t miss_;exact S.absent h t (fun a eqn=>miss_ ⟨a,eqn⟩)
  · intro a;exact (S.actual h a).symm

def emitted (_wp:0<W) (fit:∀i,(sites i).rows q≤W) (i:Fin (K*W)) : Option (GroupRow (q:=q) sites) := do
  let seat←resolve sites fit i.val
  if h:seat.2.val<(sites seat.1).portRows q then
    pure ⟨seat.1,(ProtocolRAMPortRanks.enumerate ((sites seat.1).chunks q) Fin.val Fin.val_injective).symm ⟨seat.2.val,h⟩⟩
  else none

theorem locations (wp:0<W) (fit:∀i,(sites i).rows q≤W) (c:Column) (begin_:Fin H→Fin d→ℕ)
    (i:Fin (K*W)) :
    (resolve sites fit i.val).elim 0 (fun z=>number c (begin_ z.1) (locate (S.width z.1) (List.finRange d) z.2.val))=
    (emitted (sites:=sites) wp fit i).elim 0 (fun a=>number c (begin_ a.1)
      (some (S.place a.1 a.2.1,a.2.2.val))) := by
  cases seat:resolve sites fit i.val with
  | none=>simp [emitted,seat,number]
  | some z=>
    obtain ⟨v,r⟩:=z
    by_cases live:r.val<(sites v).portRows q
    · let e:=ProtocolRAMPortRanks.enumerate ((sites v).chunks q) Fin.val Fin.val_injective
      let a:=e.symm ⟨r.val,live⟩
      have at_:=congrArg Fin.val (e.apply_symm_apply ⟨r.val,live⟩)
      change ProtocolRAMPortRanks.prefix ((sites v).chunks q) Fin.val a.1+a.2.val=r.val at at_
      let k:Fin (S.width v (S.place v a.1)):=a.2.cast (S.actual v a.1).symm
      have cut:=at_address (S.width v) (S.place v a.1) k
      rw [S.subtotal] at cut
      change locate (S.width v) (List.finRange d) (_+a.2.val)=some (_,a.2.val) at cut
      rw [at_] at cut
      simp [emitted,seat,live,cut,e,a]
    · have cut:=past_last (S.width v) r.val (by rw [S.total];omega)
      simp [emitted,seat,live,cut,number]

theorem occurrence (wp:0<W) (fit:∀i,(sites i).rows q≤W) (bins:Bins (W:=W) (q:=q) sites≤K)
    (a:GroupRow (q:=q) sites) :
    emitted (sites:=sites) wp fit (DescentTerminalScatterColumns.fixed sites wp bins a)=some a := by
  let addr:=localAddr sites a
  let r:Fin W:=addr.castLE (fit a.1)
  have atSeat:resolve sites fit (DescentTerminalScatterColumns.fixed sites wp bins a).val=some (a.1,r) := by
    apply (resolve_iff sites fit _ _ _).2
    exact ⟨addr,rfl,rfl⟩
  let e:=ProtocolRAMPortRanks.enumerate ((sites a.1).chunks q) Fin.val Fin.val_injective
  have good:r.val<(sites a.1).portRows q:=(e a.2).isLt
  have eqn:e.symm ⟨r.val,good⟩=a.2:=e.symm_apply_apply a.2
  have sameRow : (⟨a.1,e.symm ⟨r.val,good⟩⟩ : GroupRow (q:=q) sites)=a :=
    congrArg (fun t : ProtocolRAMPortRanks.Units ((sites a.1).chunks q) =>
      (⟨a.1,t⟩ : GroupRow (q:=q) sites)) eqn
  simpa [emitted,atSeat,good,e] using sameRow

theorem placed (wp:0<W) (fit:∀i,(sites i).rows q≤W) (bins:Bins (W:=W) (q:=q) sites≤K)
    (i:Fin (K*W)) (a:GroupRow (q:=q) sites) (hit:emitted (sites:=sites) wp fit i=some a) :
    DescentTerminalScatterColumns.fixed sites wp bins a=i := by
  cases seat:resolve sites fit i.val with
  | none=>simp [emitted,seat] at hit
  | some z=>
    obtain ⟨v,r⟩:=z
    obtain ⟨j,ij,rj⟩:=(resolve_iff sites fit _ _ _).1 seat
    by_cases live:r.val<(sites v).portRows q
    · let e:=ProtocolRAMPortRanks.enumerate ((sites v).chunks q) Fin.val Fin.val_injective
      let z:=e.symm ⟨r.val,live⟩
      have assigned : (⟨v,z⟩:GroupRow (q:=q) sites)=a:=by simpa [emitted,seat,live,e,z] using hit
      subst a
      have rank : (e z).val=r.val :=
        congrArg Fin.val (e.apply_symm_apply ⟨r.val,live⟩)
      apply Fin.ext
      change DescentTerminalBinPack.first W (counts (q:=q) sites) v+(e z).val=i.val
      rw [rank,rj]
      exact ij.symm
    · simp [emitted,seat,live] at hit
end Slots
end
end Hierarchy.DescentTerminalPaidHeaderEvents

end OAI
