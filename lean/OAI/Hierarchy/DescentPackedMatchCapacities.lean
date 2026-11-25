import OAI.Hierarchy.DescentPackedMatchNeeds
import OAI.Hierarchy.DescentPackedHoleMatch

namespace OAI
/-! # Thick capacity in every nonempty and every empty numerical bin -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup
open scoped Classical
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (names : DescentSharedCableNames.Stage.Host J V k↪ℕ) (win : J×V→Fin (2^k)→Cell a)
    (next : (J×V)→Fin A.degree→Option (J×V)) (he : 0≤ε)
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "Dest" => target A native S ready names
local notation "Addr" => address A native S ready

abbrev Edges (c : ScanColonies he A.stage) := {e : W.graph.Edge // e∈W.core ∧ home (W.graph.src e)=c ∧ color (W.graph.src e)=true}

def endpoint {c} (e : Edges A he c) : PackedCensus.Out W A.pos A.block (addr c).1 (A.block (W.graph.src e.val)) :=
  ⟨e.val,⟨by rw [←source_host A he (W.graph.src e.val),e.property.2.1],rfl⟩,e.property.1⟩

def port {c} (e : Edges A he c) : Port (2^k) (2*A.cap) :=
  (A.block (W.graph.src e.val),Addr (_,_) (endpoint A he e))

def receiver {c} (e : Edges A he c) := Dest (_,_) (endpoint A he e)

private theorem address_transport (h : J × V) (b b' : Fin (2^k))
    (g : PackedCensus.Out W A.pos A.block h b) (atBlock : b = b') :
    Addr (h,b) g = Addr (h,b') ⟨g.val,⟨g.property.1.1,g.property.1.2.trans atBlock⟩,g.property.2⟩ := by
  subst b'
  rfl

theorem port_injective (c : ScanColonies he A.stage) : Function.Injective (port A native S ready he (c:=c)) := by
  intro e f same
  have be : A.block (W.graph.src e.val)=A.block (W.graph.src f.val) := congrArg Prod.fst same
  let b := A.block (W.graph.src e.val)
  let j : PackedCensus.Out W A.pos A.block (addr c).1 b := ⟨f.val,⟨(endpoint A he f).property.1.1,be.symm⟩,f.property.1⟩
  have eqn : Addr ((addr c).1,b) (endpoint A he e)=Addr ((addr c).1,b) j :=
    (congrArg Prod.snd same).trans (address_transport A native S ready (addr c).1 _ b (endpoint A he f) be.symm)
  have raw := congrArg (fun g : PackedCensus.Out W A.pos A.block (addr c).1 b => g.val)
    ((Addr ((addr c).1,b)).injective eqn)
  exact Subtype.ext raw

private theorem count_fiber {E Y Z : Type} [Fintype E] (row : E → Y) (keyOf : E → Z)
    (z : Z) (xs : List Y) (noRepeat : xs.Nodup) (inj : Function.Injective row)
    (inside : ∀ e, keyOf e = z → row e ∈ xs)
    (onto : ∀ y ∈ xs, ∃ e, keyOf e = z ∧ row e = y) :
    xs.length = frequency keyOf z := by
  classical
  let send : {e : E // keyOf e = z} → {y : Y // y ∈ xs} := fun e =>
    ⟨row e.val, inside e.val e.property⟩
  have bij : Function.Bijective send := by
    constructor
    · intro e f same
      apply Subtype.ext
      exact inj (congrArg (fun t : {y : Y // y ∈ xs} => t.val) same)
    · intro t
      obtain ⟨e, hz, atRow⟩ := onto t.val t.property
      exact ⟨⟨e, hz⟩, Subtype.ext atRow⟩
  let order : Fin xs.length ≃ {e : E // keyOf e = z} :=
    (List.Nodup.getEquiv xs noRepeat).trans (Equiv.ofBijective send bij).symm
  unfold frequency
  exact (Fintype.card_fin xs.length).symm.trans (@Fintype.card_congr _ _ _ _ order)

theorem physical_capacity (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u,(win (A.pos u) (A.block u)).val=1+2*heap (addr (home u)).2+(color u).toNat)
    (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (df : A.degree<2^short)
    (c : ScanColonies he A.stage) (n : ℕ) :
    (thickBins (panel (addr c).1) (heap (addr c).2) n).length=
      frequency (fun e : Edges A he c=>bin (panel (addr c).1) (receiver A native S ready names he e) (A.block (W.graph.src e.val))) n := by
  let h := (addr c).1;let key := heap (addr c).2
  let place := fun e : Edges A he c=>port A native S ready he e
  let loc := fun e : Edges A he c=>bin (panel h) (receiver A native S ready names he e) (place e).1
  have peer_of (e : Edges A he c) : peer (panel h) (place e).1 (place e).2=some (receiver A native S ready names he e) :=
    peer_at A native S ready names win next (h,_) (endpoint A he e) df
  let bucket := thickBins (panel h) key n
  have member (e : Edges A he c) (eqn : loc e=n) : place e∈bucket :=
    (thick_mem _).mpr ⟨(site_member A native S ready names win next he fit winner c true _).mpr
      ⟨_,e.property.2.1,e.property.2.2,rfl⟩,_,peer_of e,eqn⟩
  have covers (y : Port (2^k) (2*A.cap)) (inBucket : y∈bucket) : ∃e : Edges A he c,loc e=n ∧ place e=y := by
    obtain ⟨site,v,peerV,position⟩ := (thick_mem _).mp inBucket
    obtain ⟨z,group,shade,block⟩ := (site_member A native S ready names win next he fit winner c true y.1).mp site
    obtain ⟨edge,slot,toV⟩ := (all_ports A native S ready names win next (h,y.1) y.2 v df).mp peerV
    have atH : A.pos z=h := by rw [←source_host A he _,group]
    have source : W.graph.src edge.val=z := coord (Prod.ext (edge.property.1.1.trans atH.symm) (edge.property.1.2.trans block.symm))
    let e : Edges A he c:=⟨edge.val,edge.property.2,by simpa only [source] using group,by simpa only [source] using shade⟩
    have same : place e=y := by
      have atBlock : A.block (W.graph.src e.val) = y.1 := edge.property.1.2
      refine Prod.ext atBlock ?_
      exact (address_transport A native S ready h _ y.1 (endpoint A he e) atBlock).trans slot
    have born := peer_of e
    rw [same,peerV] at born
    exact ⟨e,by simpa only [loc,same,←Option.some.inj born] using position,same⟩
  exact count_fiber place loc n bucket (thick_nodup (panel h) key n)
    (port_injective A native S ready he c) member covers

private theorem count_frequency_of_equiv {I E Z : Type*} [Fintype I] [Fintype E]
    (p : I→Prop) (key : E→Z) (z : Z) (e : {i // p i} ≃ {j // key j=z}) :
    DescentOldOccurrenceRAM.count p=frequency key z := by
  unfold DescentOldOccurrenceRAM.count frequency
  exact (Fintype.card_subtype p).symm.trans (Fintype.card_congr e)

theorem typed_capacity (c v : ScanColonies he A.stage) : Fintype.card (ThickPool T (thickList home color c) v)=
    frequency (fun e : Edges A he c=>home (W.graph.dst e.val)) v := by
  refine (DescentOldOccurrenceRAM.thick_eq W.graph W.core home color c v).trans ?_
  apply count_frequency_of_equiv
  exact {
    toFun := fun x => ⟨⟨x.val,x.property.1,x.property.2.2⟩,x.property.2.1⟩
    invFun := fun y => ⟨y.val.val,y.val.property.1,y.property,y.val.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }


end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
