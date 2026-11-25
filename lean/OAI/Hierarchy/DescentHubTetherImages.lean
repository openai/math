import OAI.Hierarchy.DescentHubTetherLedger

namespace OAI
/-! # Surviving tether bijections in the three physical graph operations -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open Computability.BorderVNP.Crossing DescentHostDirectory
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {d : ℕ} {P : Type*} {bits : P→ℕ}

section Selected
variable (A : MarkedWorld F d P bits) {I C : Type} [Fintype I] (G : PoweredGadget F)
variable (pick : I×Fin 2 ↪ A.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,A.graph.width (pick (i,s))=z i*G.b) (pack : A.graph.Site→C) (p : I→Profile G.C)
variable (hub : A.graph.Site→Bool) (inc : HubIncidence A hub) (picked : ∀t,pick t∈A.core)
variable (packed : ∀u v,pack u=pack v → hub u=hub v)
local notation "sw" => branchWidth G z p
local notation "lay" => bestLayout sw
local notation "Z" => A.selected G pick z hz fit pack p
local notation "location" => newSite A.graph pick lay pack

def selectedTethers : TetherImage A Z (fun u=>location (.inl u)) := by
  let zeroPos := fun _ : Merged A.graph pick lay pack => (0:EuclideanSpace ℝ (Fin d))
  let ball := fun u => (by simp [zeroPos] : ‖zeroPos u‖≤1)
  let tag := selectedHub A G pick z hz fit pack p hub inc picked packed
  have dest (e : Tether A) : GadgetNetwork.target A.graph pick (.inl e.val)=.inl (A.graph.dst e.val) := by
    cases hs : GadgetNetwork.selected A.graph pick e.val with
    | none => simp [GadgetNetwork.target,hs]
    | some t => exact (e.property (GadgetNetwork.selected_spec A.graph pick hs ▸ picked t)).elim
  have cross (e : Tether A) : location (.inl (A.graph.src e.val)) ≠ location (GadgetNetwork.target A.graph pick (.inl e.val)) := by
    rw [dest]
    exact fun h=>inc.outside _ e.property (congrArg tag h)
  let f (e : Tether A) : Tether Z := ⟨⟨.inl e.val,cross e⟩,
    mt (GadgetNetwork.mem_nextCore A.graph pick sw lay pack zeroPos ball A.core _).mp e.property⟩
  have inj : Function.Injective f := by
    intro e b h
    exact Subtype.ext (Sum.inl.inj (congrArg (fun j : Tether Z=>j.val.val) h))
  have surj : Function.Surjective f := by
    rintro ⟨⟨e,external⟩,outside⟩
    have h := mt (GadgetNetwork.mem_nextCore A.graph pick sw lay pack zeroPos ball A.core ⟨e,external⟩).mpr outside
    rcases e with e|t
    · exact ⟨⟨e,h⟩,rfl⟩
    · exact (h trivial).elim
  exact { edges := Equiv.ofBijective f ⟨inj,surj⟩, width := fun _=>rfl, src := fun _=>rfl,
          dst := fun e=>congrArg location (dest e) }
end Selected

section Coalesced
variable {V P : Type} {bits : P→ℕ} [DecidableEq V] (A : MarkedWorld F d P bits)
variable (key : A.graph.Site→Key V) (hub : V→Bool) (k g : ℕ)
local notation "Z" => A.coalesced key hub k g
local notation "location" => address A key hub k g

def coalescedTethers (oldHub : A.graph.Site→Bool) (inc : HubIncidence A oldHub)
    (same : ∀u,hub (key u).1=oldHub u) : TetherImage A Z location := by
  have cross (e : Tether A) : location (A.graph.src e.val) ≠ location (A.graph.dst e.val) := by
    intro h
    have eqn := congrArg (coalescedHub A key hub k g) h
    simp only [coalesced_at_hub,same] at eqn
    exact inc.outside _ e.property eqn
  let f (e : Tether A) : Tether Z := ⟨⟨e.val,cross e⟩,fun h=>e.property (Finset.mem_filter.mp h).2⟩
  have in_univ (ft : Fintype (Z).graph.Edge) (e : (Z).graph.Edge) :
      e ∈ @Finset.univ _ ft := @Finset.mem_univ _ ft e
  let back (t : Tether Z) : Tether A := ⟨t.val.val,fun h=>t.property (Finset.mem_filter.mpr ⟨in_univ _ t.val,h⟩)⟩
  exact {edges := ⟨f,back,fun _=>rfl,fun _=>rfl⟩,width := fun _=>rfl,src := fun _=>rfl,dst := fun _=>rfl}
end Coalesced

section Pieces
variable (A : MarkedWorld F d P bits) (q : ℕ) (m : A.graph.Edge→ℕ) (fit : ∀e∈A.core,A.graph.width e=m e*q)
local notation "Z" => A.pieces q m fit

def piecesTethers : TetherImage A Z id := by
  let f (e : Tether A) : Tether Z := ⟨.inl e,mt (DescentCableUnbundling.mem_nextCore A.graph A.core m q _).mp e.property⟩
  have inj : Function.Injective f := fun _ _ h=>Sum.inl.inj (congrArg Subtype.val h)
  have surj : Function.Surjective f := by
    rintro ⟨e,outside⟩
    have h := mt (DescentCableUnbundling.mem_nextCore A.graph A.core m q e).mpr outside
    rcases e with t|⟨t,i⟩
    · exact ⟨t,rfl⟩
    · exact (h t.property).elim
  exact {edges := Equiv.ofBijective f ⟨inj,surj⟩,width := fun _=>rfl,src := fun _=>rfl,dst := fun _=>rfl}
end Pieces

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
