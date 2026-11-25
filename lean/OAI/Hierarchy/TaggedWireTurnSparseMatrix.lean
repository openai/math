import OAI.Hierarchy.TaggedWireChronologicalMatrix
import OAI.Hierarchy.TaggedWireTurnScatterRead

namespace OAI
/-! # Direct use of the committed CPU turn table in the fixed local equality circuit -/
noncomputable section
namespace Hierarchy.WireTelescope.TurnShelf
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open ThreeFlat Routing Tagged Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators
variable {S n m r p e h W N : ℕ} (old : Fin n→Chord S) (edge : Fin m→Chord S)
    (route : Fin n→List (Fin m)) (bits : Fin n→ℕ)
    (sp : ∀i,Spine (rowGraph edge) (old i).1.1 (route i) (old i).1.2)
    (pos : Fin N≃Positions route) (col : Fin N→Fin 7→ℕ)
    (put : ProtocolRAMTurnShelf.Live col ↪ Fin S × Fin r)
    (widths : ∀i,col i 4=bits (pos i).1)
    (place : ∀i : ProtocolRAMTurnShelf.Live col,(put i).1=(sp (pos i.val).1).visit (pos i.val).2)

def nativeRow (s : Fin S) (u : At old edge route bits sp s) : ProtocolRAMTurnShelf.Live col :=
  ⟨pos.symm u.val,by rw [widths,pos.apply_symm_apply];exact u.property.1.ne'⟩

include place in
theorem nativeRow_site (s : Fin S) (q : At old edge route bits sp s) :
    (put (nativeRow old edge route bits sp pos col widths s q)).1=s :=
  (place _).trans ((congrArg (fun z : Positions route => (sp z.1).visit z.2)
    (pos.apply_symm_apply q.val)).trans q.property.2)

def nativeSeat (place : ∀i : ProtocolRAMTurnShelf.Live col,(put i).1=(sp (pos i.val).1).visit (pos i.val).2)
    (s : Fin S) : At old edge route bits sp s ↪ Fin r where
  toFun u:=(put (nativeRow old edge route bits sp pos col widths s u)).2
  inj' := by
    intro a b eq
    have loc := nativeRow_site old edge route bits sp pos col put widths place s
    have both:=put.injective (Prod.ext ((loc a).trans (loc b).symm) eq)
    exact Subtype.ext (pos.symm.injective (congrArg (fun z : ProtocolRAMTurnShelf.Live col => z.val) both))

/-- No seat at this site is populated by a different mathematical visit. -/
theorem nativeSeat_range (s : Fin S) (t : Fin r) :
    t∈Set.range (nativeSeat old edge route bits sp pos col put widths place s) ↔
      (s,t)∈Set.range put := by
  constructor
  · rintro ⟨u,rfl⟩
    let i:=nativeRow old edge route bits sp pos col widths s u
    refine ⟨i,Prod.ext ?_ rfl⟩
    exact nativeRow_site old edge route bits sp pos col put widths place s u
  · rintro ⟨i,eq⟩
    have site:=(place i).symm.trans (congrArg Prod.fst eq)
    let u : At old edge route bits sp s:=
      ⟨pos i.val,(widths i.val) ▸ Nat.pos_of_ne_zero i.property,site⟩
    have row : nativeRow old edge route bits sp pos col widths s u=i :=
      Subtype.ext (pos.symm_apply_apply i.val)
    exact ⟨u,(congrArg (fun i=>(put i).2) row).trans (congrArg Prod.snd eq)⟩

include widths place in
/-- The fixed site network is evaluated on literal native output pins.
All inputs to the private slab are the public role and packed start of the
two sides. The width and absent-slot conditions follow from the sparse CPU
writes. The caller supplies only the private bit at each stated scalar address. -/
theorem scattered_matrix (F : Type*) [Field F] (base : ℕ) (mem : Memory W)
    (rank : Fin h≃Σi,Fin (route i).length)
    (walk : ∀i,Traverses (rowGraph edge) ((old i).1.1) (route i) ((old i).1.2))
    (written : ∀ (f : Fin 5) (a : Fin S×Fin r),mem (addr base a.1 a.2 f)=ProtocolRAMTurnShelf.entry col put f a)
    (fieldFit : ∀u : ProtocolRAMTurnShelf.Live col,∀f : Fin 5,col u.val (f.castLE (by decide))<2^W)
    (roleFit : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 1 else 0)<2^p)
    (extent : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 3 else 2)+col u.val 4≤2^e)
    (s : Fin S) (x : State (installedWidths old bits) s)
    (y : State (installedWidths edge (routeLoad route bits)) s)
    (slab : Aperture p e→Bool)
    (two : ∀u : ProtocolRAMTurnShelf.Live col,(put u).1=s→∀b : Bool,∀ j : Fin (bits (pos u.val).1),
      ∀d : Aperture p e,d.1.val=col u.val (if b then 1 else 0)→
        d.2.val=col u.val (if b then 3 else 2)+j.val→
        slab d=readTurn (rowGraph edge) (rowGraph old) route bits (NativeSlot.allocation route bits rank)
          ⟨(pos u.val).1,j⟩ s (rowBits old bits x,rowBits edge _ y) (refAt old edge route sp (pos u.val) b)) :
    TypedWiring.value (network F r p e) (nativeView base s mem slab)=
      chordRouter old edge route bits rank walk s x y := by
  have fit (u : ProtocolRAMTurnShelf.Live col) :
      (∀b : Bool,col u.val (if b then 1 else 0)<2^p) ∧
      (∀b : Bool,col u.val (if b then 3 else 2)<2^e) ∧ col u.val 4<2^(e+p+1) := by
    have up:=extent u false
    have live:=Nat.pos_of_ne_zero u.property
    have taller : 2^e<2^(e+p+1) := Nat.pow_lt_pow_right (by decide) (by omega)
    exact ⟨roleFit u,fun b=>by have:=extent u b;omega,by omega⟩
  obtain ⟨z,bind,inside,outside⟩:=scatter_view base mem col put written fieldFit s slab fit
  rw [bind]
  let seat:=nativeSeat old edge route bits sp pos col put widths place s
  have site := nativeRow_site old edge route bits sp pos col put widths place s
  have live (u : At old edge route bits sp s) : (z (seat u)).live.val=bits u.val.1 := by
    exact ((inside _ (site u) 4).trans (widths _)).trans
      (congrArg (fun z : Positions route => bits z.1) (pos.apply_symm_apply u.val))
  have empty (t : Fin r) (h:t∉Set.range seat) : (z t).live.val=0 :=
    outside t (fun q=>h ((nativeSeat_range old edge route bits sp pos col put widths place s t).mpr q)) 4
  have room (t : Fin r) (b : Bool) : ((z t).start b).val+(z t).live.val≤2^e := by
    by_cases h : (s,t)∈Set.range put
    · obtain ⟨u,hu⟩:=h
      have atSite : (put u).1=s := congrArg Prod.fst hu
      have atSlot : (put u).2=t := congrArg Prod.snd hu
      have offset : ((z (put u).2).start b).val=col u.val (if b then 3 else 2) := by
        cases b
        · exact inside u atSite 2
        · exact inside u atSite 3
      have width : (z (put u).2).live.val=col u.val 4 := inside u atSite 4
      rw [← atSlot,offset,width]
      exact extent u b
    · have zero : (z t).live.val=0:=outside t h 4
      rw [zero,Nat.add_zero];exact ((z t).start b).isLt.le
  apply chronological_matrix old edge route bits rank walk sp F s x y z slab room seat live empty
  intro q b j
  let u:=nativeRow old edge route bits sp pos col widths s q
  have eq : pos u.val=q.val:=pos.apply_symm_apply _
  have castj : bits (pos u.val).1=bits q.val.1:=congrArg (fun t=>bits t.1) eq
  have bound : ((z (seat q)).start b).val+j.val<2^e := by
    have capacity := room (seat q) b
    rw [live q] at capacity
    exact (Nat.add_lt_add_left j.isLt _).trans_le capacity
  let d : Aperture p e := ((z (seat q)).role b,⟨((z (seat q)).start b).val+j.val,bound⟩)
  have role : d.1.val=col u.val (if b then 1 else 0) := by
    cases b
    · exact inside u (site q) 0
    · exact inside u (site q) 1
  have start : ((z (seat q)).start b).val=col u.val (if b then 3 else 2) := by
    cases b
    · exact inside u (site q) 2
    · exact inside u (site q) 3
  have rowRead (a c : Positions route) (same : a=c) (j : Fin (bits c.1)) :
      readTurn (rowGraph edge) (rowGraph old) route bits (NativeSlot.allocation route bits rank)
        ⟨a.1,j.cast (congrArg (fun v : Positions route => bits v.1) same).symm⟩ s
        (rowBits old bits x,rowBits edge _ y) (refAt old edge route sp a b)=
      readTurn (rowGraph edge) (rowGraph old) route bits (NativeSlot.allocation route bits rank)
        ⟨c.1,j⟩ s (rowBits old bits x,rowBits edge _ y) (refAt old edge route sp c b) := by
    subst c
    rfl
  exact (two u (site q) b (j.cast castj.symm) d role
    (congrArg (·+j.val) start)).trans (rowRead _ _ eq j)

end Hierarchy.WireTelescope.TurnShelf

end
end OAI
