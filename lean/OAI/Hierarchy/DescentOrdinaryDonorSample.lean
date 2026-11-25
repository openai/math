import OAI.Hierarchy.DescentPackedRawDonor
import OAI.Hierarchy.DescentPackedReverseMatch

namespace OAI
/-! # The ordinary donor panel carries the actual three old cluster anchors -/

namespace Hierarchy.DescentRawCablePanel
open DescentSIMDLookup DescentSixParty DescentSharedCableNames DescentCableDonorNames DescentHostDirectory
open Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {I P C V F J : Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
    [Field F] [Fintype J] [DecidableEq J] {d : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable {H R k hCode i a s : ℕ}
variable (A : GroupStage W G price ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (old : W.graph.Edge↪ℕ) (vertex : V↪Fin H) (group : J≃Fin R)
    (pick : I×Fin 2↪W.graph.Edge) (layout : Bool) (pack : W.graph.Site→C)
variable (rank : J×V↪ℕ) (key : Merged W.graph pick layout pack→Key (J×V))
    (hub : J×V→Bool) (g slots : ℕ) (valid : ∀q,key q∈keys hCode slots) (ids : 2^(hCode+1)*slots≤2^a)
variable (profile : I→Profile G.C) (fit : ∀t,W.graph.width (pick t)=A.z*G.b)
local notation "N" => W.graph
local notation "M" => GadgetNetwork.physical W.graph pick (branchWidth G (fun _=>A.z) profile)
local notation "p" => newSite W.graph pick layout pack
local notation "K" => fun u : W.graph.Site => key (p (Sum.inl u))
local notation "c" => normBits A.cap G.b G.C G.k
local notation "pre" => fun u=>packedNumber rank hCode slots (key (p u))
local notation "post" => fun u=>packedNumber rank hCode slots (mergeHub hub hCode g (key (p u)))

def sample (e : Live A pick) : Cell (2+c) := cell
  (decide (pre ((M).src e.val)=pre ((M).dst e.val))) (decide (post ((M).src e.val)=post ((M).dst e.val)))
  ⟨normalized A profile e.val,normalized_fits A S ready profile _⟩

def first (e : W.graph.Edge) : Option I := if h : ∃i,pick (i,0)=e then some h.choose else none

omit [DecidableEq I] [Field F] in
@[simp] theorem first_pick (j : I) : first pick (pick (j,0))=some j := by
  have yes : ∃i,pick (i,0)=pick (j,0):=⟨j,rfl⟩
  have found:=congrArg Prod.fst (pick.injective yes.choose_spec)
  simp [first]

omit [DecidableEq I] [Field F] in
theorem first_spec {e : W.graph.Edge} {j : I} (got : first pick e=some j) : pick (j,0)=e := by
  unfold first at got
  split at got
  next existsPair => exact Option.some.inj got ▸ existsPair.choose_spec
  next => contradiction

def terms (e : W.graph.Edge) : List W.graph.Site :=
  [(N).src e,(N).dst e]++((first pick e).toList.flatMap (fun j=>List.ofFn (StarKeys.endpoint (N) pick j)))

omit [DecidableEq I] [Field F] in
theorem source_mem (e : W.graph.Edge) : (N).src e∈terms pick e := by simp [terms]
omit [DecidableEq I] [Field F] in
theorem target_mem (e : W.graph.Edge) : (N).dst e∈terms pick e := by simp [terms]
omit [DecidableEq I] [Field F] in
theorem term_mem (j : I) (t : Fin 3) : StarKeys.endpoint (N) pick j t∈terms pick (pick (j,0)) := by
  unfold terms
  apply List.mem_append_right
  rw [first_pick]
  exact List.mem_flatMap.mpr ⟨j, by simp, List.mem_ofFn.mpr ⟨t, rfl⟩⟩

/-- At most five genuine earlier actor terms are compared by this donor's
physical chart. No code is shared between unrelated donor charts. -/
def relative (e : W.graph.Edge) (u : W.graph.Site) : Cell 3 :=
  Fin.ofNat (2^3) (((terms pick e).map (fun v=>(K v).1)).idxOf ((K u).1))

omit [DecidableEq I] [Fintype V] [Field F] [Fintype J] in
theorem relative_eq (e : W.graph.Edge) {u v : W.graph.Site} (hu : u∈terms pick e) (hv : v∈terms pick e) :
    relative pick layout pack key e u=relative pick layout pack key e v ↔ (K u).1=(K v).1 := by
  let names:=(terms pick e).map (fun t=>(K t).1)
  have within : names.length≤5 := by
    cases q:first pick e <;> simp [names,terms,q]
  have left : (K u).1∈names:=List.mem_map.mpr ⟨u,hu,rfl⟩
  have right : (K v).1∈names:=List.mem_map.mpr ⟨v,hv,rfl⟩
  have small {x : J×V} (h : x∈names) : names.idxOf x<2^3 := by have:=List.idxOf_lt_length_of_mem h;omega
  constructor
  · intro eqn
    have eqidx:=congrArg Fin.val eqn
    change names.idxOf ((K u).1) % (2^3) = names.idxOf ((K v).1) % (2^3) at eqidx
    rw [Nat.mod_eq_of_lt (small left), Nat.mod_eq_of_lt (small right)] at eqidx
    let ui : Fin names.length := ⟨_, List.idxOf_lt_length_of_mem left⟩
    let vi : Fin names.length := ⟨_, List.idxOf_lt_length_of_mem right⟩
    calc
      _ = names.get ui := (List.getElem_idxOf (xs:=names) (x:=(K u).1) ui.isLt).symm
      _ = names.get vi := congrArg names.get (show ui = vi from Fin.ext eqidx)
      _ = _ := List.getElem_idxOf (xs:=names) (x:=(K v).1) vi.isLt
  · intro eqn
    simp only [relative,eqn]

/-- An alternative bounded halo numbering can be substituted directly,
provided it assigns the very same equality classes to these five short terms. -/
def measuredDonor (localID : W.graph.Edge→W.graph.Site→Cell s) (e : Stage.Positive A) : Donor s a c :=
  let atSite (u : W.graph.Site):=rooted hCode slots s a hub (K u) (localID e.val u)
  { live:=true, picked:=(GadgetNetwork.selected (N) pick e.val).isSome, first:=(first pick e.val).isSome,
    layout:=layout, left:=atSite ((N).src e.val),right:=atSite ((N).dst e.val)
    anchors:=fun t=>((first pick e.val).map (fun j=>atSite (StarKeys.endpoint (N) pick j t))).getD 0
    oldUnits:=⟨normalized A profile (.inl e.val),normalized_fits A S ready profile _⟩
    armUnits:=Fin.ofNat (2^c) G.b
    supplyUnits:=fun t=>((first pick e.val).map (fun j=>(⟨normalized A profile (.inr (.inr (j,t))),
      normalized_fits A S ready profile _⟩:Cell c))).getD 0 }

variable (localID : W.graph.Edge→W.graph.Site→Cell s)
variable (chart : ∀ (e : W.graph.Edge) (u v : W.graph.Site),
    u ∈ terms pick e → v ∈ terms pick e →
      (localID e u = localID e v ↔
        (Prod.fst (key (newSite W.graph pick layout pack (Sum.inl u))) : J × V) =
          Prod.fst (key (newSite W.graph pick layout pack (Sum.inl v)))))
local notation "donor" => measuredDonor (a:=a) (hCode:=hCode) A S ready pick layout pack key hub slots profile localID
local notation "samp" => sample (hCode:=hCode) A S ready pick layout pack rank key hub g slots profile

include valid ids chart in
omit [DecidableEq I] in
theorem live_old (e : Stage.Positive A) :
    report hCode g slots (donor e) 0=samp ⟨.inl e.val,e.property⟩ := by
  rw [old_report hCode g slots (donor e) rfl]
  exact old_read (N) pick layout pack rank key hCode g slots hub valid ids e.val _ _
    (chart e.val ((N).src e.val) ((N).dst e.val)
      (source_mem pick e.val) (target_mem pick e.val)) _

omit [DecidableEq I] in
theorem live_arm (j : I) (t : Fin 2) (live : 0<A.grainCount (pick (j,0))) :
    report hCode g slots (donor ⟨pick (j,0),live⟩) (role (.inr (.inl (j,t)) : Raw (N).Edge I))=
      samp ⟨.inr (.inl (j,t)),live⟩ := by
  have rr : role (.inr (.inl (j,t)) : Raw (N).Edge I)=Fin.succ (Fin.castAdd 8 t) := Fin.ext (by simp [role];omega)
  rw [rr,arm_report]
  have small : G.b<2^c:=normalized_fits A S ready profile (.inr (.inl (j,t)))
  simp only [measuredDonor,first_pick,Option.isSome_some,ite_true]
  have amount : Fin.ofNat (2^c) G.b = (⟨G.b,small⟩ : Cell c) :=
    Fin.ext (Nat.mod_eq_of_lt small)
  rw [amount]
  exact arm_read (N) pick layout pack rank key hCode g slots hub j t (⟨G.b,small⟩ : Cell c)

include valid ids chart in
omit [DecidableEq I] in
theorem live_supply (j : I) (t : Fin 8) (live : 0<A.grainCount (pick (j,0))) :
    report hCode g slots (donor ⟨pick (j,0),live⟩) (role (.inr (.inr (j,t)) : Raw (N).Edge I))=
      samp ⟨.inr (.inr (j,t)),live⟩ := by
  have rr : role (.inr (.inr (j,t)) : Raw (N).Edge I)=Fin.succ (Fin.natAdd 2 t) := Fin.ext (by simp [role];omega)
  rw [rr,supply_report]
  simp only [measuredDonor,first_pick,Option.isSome_some,ite_true,Option.map_some,Option.getD_some]
  exact motif_read (N) pick layout pack rank key hCode g slots hub valid ids j t
    (fun x => localID (pick (j,0)) (StarKeys.endpoint (N) pick j x))
    (fun x y => chart (pick (j,0)) (StarKeys.endpoint (N) pick j x)
      (StarKeys.endpoint (N) pick j y) (term_mem pick j x) (term_mem pick j y))
    (fun u => (⟨normalized A profile (.inr (.inr (j,u))), normalized_fits A S ready profile _⟩ : Cell c))

end
end Hierarchy.DescentRawCablePanel

end OAI
