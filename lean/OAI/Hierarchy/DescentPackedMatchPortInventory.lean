import OAI.Hierarchy.DescentPackedMatchedGeometry
import OAI.Hierarchy.DescentPackedMatchedSupport
import OAI.Hierarchy.DescentOldOccurrenceFibers

namespace OAI
/-! # Count original marked grains exactly in the ordered numerical matching input -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSixParty DescentSixParty.PackedCensus DescentSIMDLookup
open scoped Classical
noncomputable section
variable {r D p digit : ℕ} (u : Panel r D p digit)

theorem at_mem {x : Fin r} {i : Port r p} {b : ℕ} : i∈atBin u x b ↔ i.1=x ∧ ∃v,peer u x i.2=some v ∧ bin u v x=b := by
  obtain ⟨y,s⟩ := i
  by_cases same : y=x
  · subst y;simp only [true_and,at_bin_mem]
  · have other : x ≠ y := Ne.symm same
    simp [atBin,same,other]

theorem in_mem {x : Fin r} {i : Port r p} {n : ℕ} : i∈inBlock u n x ↔ i.1=x ∧ ∃v,peer u x i.2=some v ∧ bin u v x<n := by
  simp only [inBlock,List.mem_flatMap,List.mem_finRange,true_and,at_mem]
  constructor
  · rintro ⟨b,eqn,v,atV,where_⟩;exact ⟨eqn,v,atV,by simpa only [where_] using b.isLt⟩
  · rintro ⟨eqn,v,hit,room⟩;exact ⟨⟨_,room⟩,eqn,v,hit,rfl⟩

theorem in_nodup (n : ℕ) (x : Fin r) : (inBlock u n x).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun b _=>(slots_ordered u x b.val).imp (fun {l r} h eqn=>h.ne (congrArg Prod.snd eqn)),?_⟩
  apply (List.nodup_finRange n).imp
  intro b c distinct a first second
  obtain ⟨_,v,hv,bv⟩ := (at_mem u).mp first
  obtain ⟨_,v',hv',cv⟩ := (at_mem u).mp second
  have eqn : v=v' := Option.some.inj (hv.symm.trans hv')
  subst v'
  exact distinct (Fin.ext (bv.symm.trans cv))

theorem thick_mem {key b : ℕ} {i : Port r p} : i∈thickBins u key b ↔ i.1∈sites u key true ∧ ∃v,peer u i.1 i.2=some v ∧ bin u v i.1=b := by
  simp only [thickBins,List.mem_flatMap,at_mem]
  aesop

theorem thick_nodup (key b : ℕ) : (thickBins u key b).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun x _=>(slots_ordered u x b).imp (fun {l r} h eqn=>h.ne (congrArg Prod.snd eqn)),?_⟩
  apply ((List.nodup_finRange r).filter _).imp
  intro x y differ i hx hy
  exact differ (((at_mem u).mp hx).1.symm.trans ((at_mem u).mp hy).1)

namespace Stage
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (names : DescentSharedCableNames.Stage.Host J V k↪ℕ) (win : J×V→Fin (2^k)→Cell a)
    (next : (J×V)→Fin A.degree→Option (J×V))
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "Addr" => address A native S ready
local notation "Dest" => target A native S ready names

/-- The site list in each block counts every marked original unit exactly once.
The peer room condition is obtained by reading the authenticated destination actor. -/
theorem source_mass {C : Type} [Fintype C] [DecidableEq C] (home : W.graph.Site→C)
    (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (n : ℕ) (fit : A.degree<2^short)
    (room : ∀h x (e : Out W A.pos A.block h x),bin (panel h) (Dest (h,x) e) x<n) (z : W.graph.Site) :
    countAt (panel (A.pos z)) n (A.block z)=live (nativeTraffic W.graph W.core home) z := by
  classical
  let h := A.pos z;let x:= A.block z
  let src := fun (e : Out W A.pos A.block h x)=>(x,Addr (h,x) e)
  have eqSrc (e : Out W A.pos A.block h x) : W.graph.src e.val=z := coord (Prod.ext e.property.1.1 e.property.1.2)
  have serial : Function.Injective src := fun a b eqn=>(Addr (h,x)).injective (congrArg Prod.snd eqn)
  have member (e : Out W A.pos A.block h x) : src e∈inBlock (panel h) n x :=
    (in_mem _).mpr ⟨rfl,_,peer_at A native S ready names win next (h,x) e fit,room h x e⟩
  have covers : ∀y∈inBlock (panel h) n x,∃e,src e=y := by
    rintro ⟨v,s⟩ mem
    obtain ⟨atBlock,g,born,_⟩ := (in_mem _).mp mem
    change v = x at atBlock
    subst v
    obtain ⟨e,eqn,_⟩ := (all_ports A native S ready names win next (h,x) s g fit).mp born
    exact ⟨e,Prod.ext rfl eqn⟩
  have mem_count (pred : W.graph.Edge → Prop) (e : W.graph.Edge) :
      e ∈ Finset.univ.filter pred ↔ pred e := by simp
  rw [DescentOldOccurrenceRAM.live_eq]
  change (inBlock (panel h) n x).length=_
  rw [←List.toFinset_card_of_nodup (in_nodup (panel h) n x)]
  symm
  apply Finset.card_bij (fun e he=>src ⟨e,by
    obtain ⟨hc,where_⟩ := (mem_count _ _).mp he
    exact ⟨⟨congrArg A.pos where_,congrArg A.block where_⟩,hc⟩⟩)
  · intro e _;exact List.mem_toFinset.mpr (member _)
  · intro e he f hf same;exact congrArg Subtype.val (serial same)
  · intro y hy;obtain ⟨e,rfl⟩ := covers y (List.mem_toFinset.mp hy)
    exact ⟨e.val,(mem_count _ _).mpr ⟨e.property.2,eqSrc e⟩,rfl⟩

end Stage
end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
