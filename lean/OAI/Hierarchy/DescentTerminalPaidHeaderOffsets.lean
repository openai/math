import OAI.Hierarchy.DescentTerminalHeaderGroupSlots

namespace OAI
/-! # Identifying each purchased source row with its true cable or public header -/
namespace Hierarchy.DescentTerminalPaidHeaderEvents
open Computability.BorderVNP.Crossing DescentTerminalPorts DescentTerminalGraphPositions DescentTerminalCableOrder
open DescentSortedRoster DescentTerminalGrainProfiles DescentTerminalHeaderGroups DescentTerminalSparseHeader
open DescentTerminalHeaderSockets DescentTerminalWidthRowsRAM DescentTerminalChipSource DescentKernelHistory
open ThreeFlat.Routing
open scoped Classical
noncomputable section
variable {H D:ℕ} (R:Fin H→Fin D→Option (Fin H))
    {deg p q:ℕ} {P Tag:Type} [Fintype P] {bw:P→ℕ} (N:Network deg P bw) (home:N.Site→Fin H)
    (native:N.Edge↪Fin (Fintype.card N.Edge)) (ext:P↪ℕ) (nodes:N.Site↪ℕ) (ops:∀v,Boundary N v↪ℕ)
    (hp:0<p) (hq:0<q) (edges:∀e,p∣N.width e) (ports:∀z,p∣bw z)
    (sorted:Sorted R) (covers:∀e,0<N.width e→home (N.dst e)∈present R (home (N.src e)) ∧
      home (N.src e)∈present R (home (N.dst e)))
local notation "L" => order N home native p ext nodes ops
local notation "inputs" => slotCount (p:=p) R N home
local notation "outward" => fun v=>DescentTerminalExteriorHeaders.siteMass N home v/p

def cableOffset (q:ℕ) (t:ℕ) := (passed q p inputs t).length
def publicOffset (q:ℕ) (t:ℕ) := (passed q p outward t).length
local notation "cut" => cableOffset (p:=p) R N home q
local notation "pub" => publicOffset (p:=p) N home q

include hp hq edges ports in
theorem public_before (k:ℕ) (small:k≤H) :
    pub k=(DescentTerminalExteriorHeaders.stream (q:=q) (p:=p) N home native ext nodes ops k).length := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    let i:Fin H:=⟨k,by omega⟩
    change (passed q p outward (i.val+1)).length=_
    rw [passed_len]
    change pub k+_=_
    rw [ih (by omega)]
    have low : k < H := by omega
    simp [DescentTerminalExteriorHeaders.stream,low,i,
      public_rows N home native ext nodes ops hp edges ports q hq]

include covers in
omit [Fintype P] in
private theorem reverse_live (v u:Fin H) (positive:0<pairMass N home (pair v u)) :
    ∃j,R u j=some v := by
  obtain ⟨e,he,tag⟩:=(positive_iff N home _).1 positive
  have at_:=(pair_iff (home (N.src e)) (home (N.dst e)) v u).1 tag
  have seen:v∈present R u:=by
    rcases at_ with ⟨src,dst⟩|⟨src,dst⟩ <;> rw [←src,←dst]
    · exact (covers e he).2
    · exact (covers e he).1
  exact (Finset.mem_filter.mp seen).2

include covers in
omit [Fintype P] in
theorem active_ordinal (v u:Fin H) (j:Fin D) (other:R v j=some u)
    (has:0<pairMass N home (pair v u)) : ∃k,ordinal R v j=some k := by
  by_cases flip:u<v
  · obtain ⟨s,rs⟩:=reverse_live R N home covers v u has
    cases find_:(List.finRange D).find? (fun t=>decide (R u t=some v)) with
    | some it=>simp [ordinal,other,flip,find_]
    | none=>
      have no:=(List.find?_eq_none.mp find_) s (List.mem_finRange s)
      simp [rs] at no
  · simp [ordinal,other,flip]

include covers in
theorem socket_width (v:Fin H) (j:Fin (D+1)) :
    endAt R v cut pub j-origin R v cut pub j=poolBatchCount (grainCount (p:=p) R N home v j) q := by
  refine Fin.cases ?_ (fun t=>?_) j
  · change (passed q p outward (v.val+1)).length-(passed q p outward v.val).length=_
    rw [passed_len,Nat.add_sub_cancel_left];rfl
  · cases k:ordinal R v t with
    | some idx=>
      obtain ⟨u,other,tag⟩:=ordinal_key R v t idx k
      change finish cut (ordinal R v t)-source cut (ordinal R v t)=_
      rw [k]
      change (passed q p inputs (idx.val+1)).length-(passed q p inputs idx.val).length=_
      simp [passed_len,slotCount,tag,grainCount,label,other]
    | none=>
      have zero:grainCount (p:=p) R N home v t.succ=0:=by
        cases other:R v t with
        | none=>simp [grainCount,label,other]
        | some u=>
          have dead:pairMass N home (pair v u)=0:=by
            by_contra! live
            obtain ⟨idx,cannot⟩:=active_ordinal R N home covers v u t other (Nat.pos_of_ne_zero live)
            rw [k] at cannot;contradiction
          simp [grainCount,label,other,dead]
      change finish cut (ordinal R v t)-source cut (ordinal R v t)=_
      rw [zero,k]
      have h:=rows_length q p 0
      simpa [DescentTerminalHeaderSockets.finish,source,rows_zero] using h

variable (r:∀v,Recipe Tag (DescentTerminalBundleRows.SiteRef (p:=p) N v)) (birth:∀v,(r v).Node↪ℕ)
local notation "sites" => DescentTerminalBundleRows.site L r hp birth
local notation "embed" => groupEmbed R N home native ext nodes ops hp covers
local notation "gOf" => fun (a : GroupRow (q:=q) sites) =>
  (Equiv.symm (Order.groups L (Sigma.fst a))) (Sigma.fst (Sigma.snd a))
include hp hq edges ports sorted covers in
theorem event_source (a:GroupRow (q:=q) sites) :
    origin R a.1 cut pub (embed a.1 a.2.1)=DescentTerminalScatterRows.srcStart N home native ext nodes ops r hp birth a ∧
    ((embed a.1 a.2.1).val=0 ↔ (gOf a).val=none) := by
  let j:=embed a.1 a.2.1
  have match_:label R a.1 j=some (gOf a).val:=socket_name R N home native ext nodes ops hp covers _ _
  have classify : j.val=0 ↔ (gOf a).val=none := by
    constructor
    · intro h;have hj:j=0:=Fin.ext h
      simpa [hj,label] using match_.symm
    · intro g
      cases eqn:j using Fin.cases with
      | zero=>rfl
      | succ k=>
        rw [eqn,g] at match_
        cases u:R a.1 k <;> simp [label,u] at match_
  refine ⟨?_,classify⟩
  cases t:(gOf a).val with
  | none=>
    have hj:j=0:=Fin.ext (classify.mpr t)
    change origin R a.1 cut pub j=_
    rw [hj]
    simpa [origin,DescentTerminalScatterRows.srcStart,t] using
      public_before N home native ext nodes ops hp hq edges ports a.1.val a.1.isLt.le
  | some u=>
    have pos:=DescentTerminalScatterRows.positive N home native ext nodes ops r hp birth a u t
    have jne:j≠0:=by intro zero;have nn:=classify.mp (congrArg Fin.val zero);rw [t] at nn;contradiction
    have next:∃k:Fin D,j=k.succ:=
      Fin.cases (motive:=fun z : Fin (D+1) => z≠0 → ∃k:Fin D,z=k.succ)
        (fun h=>False.elim (h rfl)) (fun s _=>⟨s,rfl⟩) j jne
    obtain ⟨k,jk⟩:=next
    rw [jk,t] at match_
    have other:R a.1 k=some u:=by
      cases h:R a.1 k with
      | none=>simp [label,h] at match_
      | some w=>simpa [label,h] using match_
    obtain ⟨idx,ki⟩:=active_ordinal R N home covers a.1 u k other pos
    obtain ⟨v,also,tag⟩:=ordinal_key R a.1 k idx ki
    have same:=Option.some.inj (also.symm.trans other);subst v
    have rows:=canonical_prefix R N home native ext nodes ops hp edges ports sorted covers q idx _ tag
    change origin R a.1 cut pub j=_
    simpa [jk,origin,source,ki,cableOffset,DescentTerminalScatterRows.srcStart,t] using congrArg List.length rows

include hp hq edges ports sorted covers in
theorem event_bound (a:GroupRow (q:=q) sites) {n:ℕ} (cRoom:(tape q p inputs).length≤n)
    (pRoom:(tape q p outward).length≤n) :
    DescentTerminalScatterRows.srcStart N home native ext nodes ops r hp birth a+a.2.2.val<n := by
  let j:=embed a.1 a.2.1
  let s:=graphSlots R N home native ext nodes ops hp edges ports sorted covers r birth q
  have length_:endAt R a.1 cut pub j-origin R a.1 cut pub j=(sites a.1).chunks q a.2.1 :=
    (socket_width R N home covers a.1 j).trans (s.actual a.1 a.2.1)
  have start_:= (event_source R N home native ext nodes ops hp hq edges ports sorted covers r birth a).1
  change origin R a.1 cut pub j=_ at start_
  have early: a.2.2.val<(sites a.1).chunks q a.2.1:=a.2.2.isLt
  have bound_ (slot:Fin (D+1)) : endAt R a.1 cut pub slot≤n := by
    refine Fin.cases ?_ (fun t=>?_) slot
    · exact (DescentTerminalWidthRowsRAM.within q p outward _).trans pRoom
    · change finish cut (ordinal R a.1 t)≤n
      cases h:ordinal R a.1 t with
      | none=>exact Nat.zero_le n
      | some idx=>exact (DescentTerminalWidthRowsRAM.within q p inputs _).trans cRoom
  have := bound_ j
  omega

end
end Hierarchy.DescentTerminalPaidHeaderEvents

end OAI
