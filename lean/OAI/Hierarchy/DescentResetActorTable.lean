import OAI.Hierarchy.DescentResetActorLookup
import OAI.Hierarchy.DescentIssuedFallbackOrdinal

namespace OAI
/-! # Terminal occupancy and tree height read from the measured reset source -/

namespace Hierarchy.DescentSixParty.ResetInput.SourceFrame
open DescentGL DescentColonies DescentContacts DescentChosenRouter
open DescentRelativeContacts DescentFallbackLeafScan DescentPlainTerminal
open scoped Classical
noncomputable section
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V]
  {d k : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
  {price ε : ℝ} {h C Ht g : ℕ} {Z : ResetInput A price ε h C Ht} {T : Terminals Z}
  {pos : A.graph.Site→V} {ix : A.graph.Site→Block k} {hub : V→Bool}
variable (frame : SourceFrame Z T pos ix hub g)
variable (vertex : V↪ℕ) (near : V→Finset V) (n f B wire K Δ : ℕ)
    (wt : V→Block k→ℕ) (flow : V→V→Block k→ℝ)
variable (roster : SourceFrame.Roster Z T pos ix hub g frame vertex near n f B wire K flow Δ wt)
local notation "fallbackDegree" => 32*Nat.clog 2 (2*Δ)
local notation "m" => T.commonDepth
local notation "depth" => fun v=>Z.placement.b (frame.host v)
set_option quotPrecheck false in
local notation "budget" => roster.2.2.2.2.2.choose
local notation "ep" => DescentPlainTerminal.endpoint near depth frame.basis wt f fallbackDegree B g (2^Z.n)
  budget (fun v j=>(frame.host v,j)∈Z.placement.keys) hub

private theorem numeric_inj {Y : ℕ} : Function.Injective (DescentPlainTerminal.fields (Y:=Y)) := by
  rintro ⟨address,a⟩ ⟨address',b⟩ eqn
  have sameAddress : address=address' := congrArg (fun row : (ℕ×ℕ)×Option ℕ=>row.1) eqn
  have sameTag : a.map Fin.val=b.map Fin.val := congrArg Prod.snd eqn
  exact Prod.ext sameAddress ((Option.map_inj_right (fun _ _ h=>Fin.ext h)).mp sameTag)

/-- All 2^k old source slots at one physical position participate, including
empty old cells whose declared row receives a reset root. -/
theorem terminal_hit (v : V) (z : Endpoint (2^Z.n)) :
    (∃t,T.code t=(frame.host v,z)) ↔
      (List.finRange (2^k)).any (fun x=>decide (ep v x=DescentPlainTerminal.fields z))=true := by
  have names:=roster.2.2.2.2.2.choose_spec.2 v (DescentPlainTerminal.fields z)
  constructor
  · rintro ⟨t,name⟩
    obtain ⟨x,eqn⟩:=names.mp ⟨t,by rw [name],by rw [name]⟩
    simpa [List.any_eq_true,List.mem_finRange] using (show ∃i : Block k,ep v i=DescentPlainTerminal.fields z from ⟨x,eqn⟩)
  · intro found
    obtain ⟨x,atX⟩ : ∃x : Block k,ep v x=DescentPlainTerminal.fields z := by simpa [List.any_eq_true,List.mem_finRange] using found
    obtain ⟨t,first,last⟩:=names.mpr ⟨x,atX⟩
    exact ⟨t,Prod.ext first (numeric_inj last)⟩

variable (peer : V→Fin Δ→Option V) (real : ∀v x,x∈near v ↔ ∃j,peer v j=some x)
local notation "pred" => fun (v : Z.V) (j : Fin Δ)=>Option.map frame.host (peer (frame.host.symm v) j)
local notation "hubs" => fun v=>hub (frame.host.symm v)

def queryHeight (z : Z.V×Endpoint (2^Z.n)) : ℕ :=
  Nat.clog 2 ((Finset.univ.filter (fun j : Fin Δ×Fin (2^Ht)=>
    (candidate (k:=Z.k-m) (D:=fallbackDegree) (g:=g) (f:=f) hubs pred (shortName m z) j).isSome)).card)

include real in
/-- The exact installed optional height, computed by a local old-slot OR
and the bounded neighbor list of this previous host. -/
theorem terminal_entry (s : Bool) (v : V) (z : Endpoint (2^Z.n)) :
    terminalEntry Z T s (frame.host v,z)=
      if (List.finRange (2^k)).any (fun x=>decide (ep v x=DescentPlainTerminal.fields z)) then
        some (queryHeight frame f Δ peer (frame.host v,z)) else none := by
  by_cases present : ∃t,T.code t=(frame.host v,z)
  · obtain ⟨t,code⟩:=present
    have hit:=(terminal_hit frame vertex near n f B wire K Δ wt flow roster v z).mp ⟨t,code⟩
    rw [ite_eq_left hit]
    apply (terminal_read Z T s _ _).mpr
    refine ⟨t,code,?_⟩
    simpa only [queryHeight,code] using source_height frame vertex near n f B wire K Δ wt flow roster peer real s t
  · have miss : ¬(List.finRange (2^k)).any (fun x=>decide (ep v x=DescentPlainTerminal.fields z))=true :=
      fun yes=>present ((terminal_hit frame vertex near n f B wire K Δ wt flow roster v z).mpr yes)
    simp [terminalEntry,present,miss]

end
end Hierarchy.DescentSixParty.ResetInput.SourceFrame

end OAI
