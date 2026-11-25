import OAI.Hierarchy.DescentPackLabels
import OAI.Hierarchy.DescentStarCables
import OAI.Hierarchy.DescentPhysicalOrder

namespace OAI
/-! # A common geometric host for the actual colored whole-item contractions -/

namespace Hierarchy.DescentSixParty.GadgetNetwork
export Hierarchy.DescentSixParty (newSite)
end Hierarchy.DescentSixParty.GadgetNetwork

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentHostDirectory DescentColonies
open scoped Classical
noncomputable section

variable {V : Type} [DecidableEq V] {C : Type} [Fintype C] [DecidableEq C]
variable {n : ℕ} {P : Type*} {bits : P→ℕ} (N : Network n P bits)
variable (core : Finset N.Edge) (home : N.Site→C) (color : N.Site→Bool) (B : ℕ)

abbrev NativeSlot := ThinSite (fun _=>nativeTraffic N core home) B (thinList home color) (thickList home color)
abbrev NativePair := AllPairs (fun _=>nativeTraffic N core home) B (thinList home color) (thickList home color)

/-- Ordinal zero is the thick pack, and the native slab slot has its ordinal plus one. -/
def packAddress (col : C ↪ V×(ℕ×ℕ)) : C⊕NativeSlot N core home color B ↪ Key V where
  toFun
    | .inl c => ((col c).1,(col c).2,0)
    | .inr ⟨c,j⟩ => ((col c).1,(col c).2,j.val+1)
  inj' := by
    rintro (c|⟨c,j⟩) (t|⟨t,i⟩) h
    · have e := congrArg (fun x : Key V => (x.1,x.2.1)) h
      exact congrArg Sum.inl (col.injective e)
    · have e := congrArg (fun x : Key V=>x.2.2) h
      exact False.elim (Nat.succ_ne_zero i.val e.symm)
    · have e := congrArg (fun x : Key V=>x.2.2) h
      exact False.elim (Nat.succ_ne_zero j.val e)
    · have e := congrArg (fun x : Key V=> (x.1,x.2.1)) h
      obtain rfl : c=t := col.injective e
      have ord := congrArg (fun x : Key V=>x.2.2) h
      obtain rfl : j=i := Fin.ext (Nat.succ.inj ord)
      rfl

variable (col : C ↪ V×(ℕ×ℕ))

omit [DecidableEq V] in
theorem packed_home (u : N.Site) :
    let addr:=packAddress N core home color B col (coloredPack N core home color B u)
    (addr.1,addr.2.1)=col (home u) := by
  unfold coloredPack packLabel
  split <;> rfl

omit [DecidableEq V] in
theorem pack_room (A : ℕ) (pos : 0<B)
    (cap : ∀c,amount (live (nativeTraffic N core home)) (thinList home color c)≤A*B)
    (p : C⊕NativeSlot N core home color B) : (packAddress N core home color B col p).2.2<A+2 := by
  rcases p with c|⟨c,j⟩
  · change 0<A+2;omega
  · have lim := slots_bound (fun _=>nativeTraffic N core home) B (thinList home color) (thickList home color)
      c pos (cap c)
    simp only [SlabSlot,Locations,Fintype.card_fin] at lim
    change j.val+1<A+2
    have valid : j.val < (slabPacking (nativeTraffic N core home) B
        (thinList home color c) (thickList home color c)).decisions.length := j.isLt
    exact Nat.succ_lt_succ (valid.trans_le lim)

def chosenSlot := thinSite (fun _=>nativeTraffic N core home) B (thinList home color) (thickList home color)
def chosenCenter (l : Bool) := mergeCenter (fun _=>nativeTraffic N core home) B
    (thinList home color) (thickList home color) l (fun _ c=>c)

theorem native_centerAt (same : ∀e∈core,color (N.src e)=color (N.dst e)) (l : Bool)
    (i : NativePair N core home color B) :
    coloredPack N core home color B (thickCenter N (colorPick N core home color B) l i)=
      .inl (chosenCenter N core home color B l i) := by
  cases l with
  | false => exact colorPick_thick_src N core home color B i
  | true => exact colorPick_thick_dst N core home color B same i

/-- The actual injection uses the native paired-core embedding at both arms. -/
def nativeKey (same : ∀e∈core,color (N.src e)=color (N.dst e)) (l : Bool) :
    Merged N (colorPick N core home color B) l (coloredPack N core home color B) ↪ Key V :=
  let K := key N (colorPick N core home color B) l (coloredPack N core home color B)
    (chosenSlot N core home color B) (chosenCenter N core home color B l)
    (colorPick_thin_src N core home color B) (native_centerAt N core home color B same l)
    (native_coherent _ B _ _ (fun _ c=>c) l)
  (⟨K,key_injective N _ l _ _ _ _ _ _⟩ : _ ↪ _).trans (packAddress N core home color B col)

variable {k markCap : ℕ} (near : V→Finset V) (D a : ℕ) (load : V→Block k→ℕ)
    (limit : ∀v x,load v x ≤ B) (markLimit : ∀v x,load v x ≤ markCap) (position : N.Site→V) (block : N.Site→Block k)

abbrev depthAt := depth load (fun p q=>q∈near p) D a B limit

/-- The native grouping argument is the finite set of occupied colony codes.
The enclosing address space is independent of the color, layout and traffic. -/
def colonyCode (u : N.Site) : V×(ℕ×ℕ) :=
  (position u,depthAt B near D a load limit (position u) (block u),
    DescentColonies.group (depthAt B near D a load limit (position u) (block u)) (block u))

def occupied : Finset (V×(ℕ×ℕ)) := Finset.univ.image (colonyCode N B near D a load limit position block)

def rawColony (u : N.Site) : occupied N B near D a load limit position block :=
  ⟨colonyCode N B near D a load limit position block u,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

theorem rawColony_surjective : Function.Surjective (rawColony N B near D a load limit position block) := by
  rintro ⟨c,occupiedAt⟩
  obtain ⟨u,_,eqn⟩ := Finset.mem_image.mp occupiedAt
  exact ⟨u,Subtype.ext eqn⟩

def firstColonyRow : occupied N B near D a load limit position block ↪ ℕ :=
  DescentPhysicalOrder.first (originalId N.Site) (rawColony N B near D a load limit position block)
    (rawColony_surjective N B near D a load limit position block)

def colonyOf : N.Site → occupied N B near D a load limit position block :=
  DescentPhysicalOrder.home (firstColonyRow N B near D a load limit position block)
    (rawColony N B near D a load limit position block)

theorem colonyOf_surjective : Function.Surjective (colonyOf N B near D a load limit position block) :=
  DescentPhysicalOrder.home_surjective _ (rawColony_surjective N B near D a load limit position block)

/-- Decode the physical name chosen by the first old row back to its host and dyadic cell. -/
def occupiedAddress : occupied N B near D a load limit position block ↪ V×(ℕ×ℕ) :=
  DescentPhysicalOrder.address (firstColonyRow N B near D a load limit position block)
    (Function.Embedding.subtype _)

@[simp] theorem occupiedAddress_colonyOf (u : N.Site) :
    occupiedAddress N B near D a load limit position block (colonyOf N B near D a load limit position block u) =
      colonyCode N B near D a load limit position block u :=
  DescentPhysicalOrder.address_home _ _ (Function.Embedding.subtype _) _

theorem occupiedAddress_mem (c : occupied N B near D a load limit position block) :
    occupiedAddress N B near D a load limit position block c ∈ occupied N B near D a load limit position block := by
  obtain ⟨u,rfl⟩ := colonyOf_surjective N B near D a load limit position block c
  rw [occupiedAddress_colonyOf]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem colonyOrdinal (u : N.Site) :
    (Fintype.equivFin _ (colonyOf N B near D a load limit position block u)).val =
      (Finset.univ.filter (fun c => firstColonyRow N B near D a load limit position block c <
        firstColonyRow N B near D a load limit position block (rawColony N B near D a load limit position block u))).card :=
  DescentPhysicalOrder.home_order _ _ _

omit [DecidableEq V] in
/-- Every position usable by the actual packing belongs to the common,
fully enumerated finite address set of at most two intervals per old block. -/
theorem pack_mem [Fintype V] (A : ℕ) (positive : 0<B)
    (cap : ∀c,amount (live (nativeTraffic N core home)) (thinList home color c)≤A*B)
    (covered : Function.Surjective home)
    (realized : ∀u,col (home u)=colonyCode N markCap near D a load markLimit position block u)
    (p : C⊕NativeSlot N core home color B) : packAddress N core home color B col p∈keys k (A+2) := by
  let c : C := Sum.elim id Sigma.fst p
  have located : packAddress N core home color B col p =
      ((col c).1,(col c).2,(packAddress N core home color B col p).2.2) := by
    rcases p with _ | ⟨_,_⟩ <;> rfl
  obtain ⟨u,eqn⟩ := covered c
  have coordinate : col c=colonyCode N markCap near D a load markLimit position block u := eqn ▸ realized u
  have h := pack_room N core home color B col A positive cap p
  rw [located,coordinate]
  have depthFits := depth_le load (fun p q => q ∈ near p) D a markCap markLimit
    (position u) (block u)
  exact key_mem (position u) (block u) (depthFits.trans (Nat.sub_le k a)) h

/-- If two old position occurrences share a colony, its two physical pack
slots are adjacent even when they occur at different block ordinals. -/
private theorem same_hop {D slots : ℕ} {v : V} {dj : ℕ×ℕ} {i j : ℕ} (space : j<slots) :
    (v,dj,j)∈next near D slots (v,dj,i) := by
  have h := pad (near:=near) (D:=D) (slots:=slots) (v,dj,j) space
  exact h

/-- Every cable of the old group stays in a single block. Its two genuine
colonies meet at that block and inherit the paid dyadic neighbor-depth bound. -/
private theorem native_links (A : ℕ) (positive : 0<B)
    (cap : ∀c,amount (live (nativeTraffic N core home)) (thinList home color c)≤A*B)
    (realized : ∀u,col (home u)=colonyCode N markCap near D a load markLimit position block u)
    (same : ∀e,block (N.src e)=block (N.dst e))
    (adj : ∀e,position (N.dst e)∈near (position (N.src e)) ∧ position (N.src e)∈near (position (N.dst e))) :
    let p:=fun u=>packAddress N core home color B col (coloredPack N core home color B u)
    let pick:=colorPick N core home color B
    (∀e,Linked near D (A+2) (p (N.src e)) (p (N.dst e))) ∧
      (∀i,Linked near D (A+2) (p (N.src (pick (i,0)))) (p (N.src (pick (i,1))))) := by
  let pick := colorPick N core home color B
  let packs : N.Site → C ⊕ NativeSlot N core home color B := coloredPack N core home color B
  let physical := packAddress N core home color B col
  have room := pack_room N core home color B col A positive cap
  have atSite (u : N.Site) :
      physical (packs u) = (position u,
        (depthAt markCap near D a load markLimit (position u) (block u),
          DescentColonies.group (depthAt markCap near D a load markLimit (position u) (block u)) (block u)),
        (physical (packs u)).2.2) := by
    have cell := (packed_home N core home color B col u).trans (realized u)
    exact Prod.ext (congrArg (fun c : V × (ℕ × ℕ) => c.1) cell)
      (Prod.ext (congrArg (fun c : V × (ℕ × ℕ) => c.2) cell) rfl)
  have hop (u v : N.Site) (old : block u=block v)
      (close : position v∈near (position u)) (back : position u∈near (position v)) :
      physical (packs v)∈next near D (A+2) (physical (packs u)) := by
    have target := atSite v
    rw [←old] at target
    have travel {fromKey toKey fromCell toCell : Key V}
        (fromEq : fromKey = fromCell) (toEq : toKey = toCell)
        (step : toCell ∈ next near D (A+2) fromCell) : toKey ∈ next near D (A+2) fromKey := by
      cases fromEq
      cases toEq
      exact step
    exact travel (atSite u) target (colony_hop (D:=D) (a:=a) load markLimit close back (block u)
      (physical (packs u)).2.2 (physical (packs v)).2.2 (room (packs v)))
  have wires (e) : Linked near D (A+2) (physical (packs (N.src e))) (physical (packs (N.dst e))) :=
    ⟨hop _ _ (same e) (adj e).1 (adj e).2,hop _ _ (same e).symm (adj e).2 (adj e).1⟩
  have mates (i : NativePair N core home color B) : Linked near D (A+2)
      (physical (packs (N.src (pick (i,0))))) (physical (packs (N.src (pick (i,1))))) := by
    have transport {x y thick thin : C ⊕ NativeSlot N core home color B}
        (hx : x = thick) (hy : y = thin)
        (step : Linked near D (A+2) (physical thick) (physical thin)) :
        Linked near D (A+2) (physical x) (physical y) := by
      cases hx
      cases hy
      exact step
    apply transport (colorPick_thick_src N core home color B i) (colorPick_thin_src N core home color B i)
    exact ⟨same_hop near (room (.inr (chosenSlot N core home color B i))),
      same_hop near (room (.inl i.1))⟩
  exact ⟨wires,mates⟩

theorem native_cables_both (A : ℕ) (positive : 0<B)
    (cap : ∀c,amount (live (nativeTraffic N core home)) (thinList home color c)≤A*B)
    (realized : ∀u,col (home u)=colonyCode N markCap near D a load markLimit position block u)
    (same : ∀e,block (N.src e)=block (N.dst e))
    (adj : ∀e,position (N.dst e)∈near (position (N.src e)) ∧ position (N.src e)∈near (position (N.dst e)))
    (sheet : Block k→Bool) (painted : ∀u,color u=sheet (block u))
    (l : Bool) (sw : NativePair N core home color B→Fin 8→ℕ) {d : ℕ}
    (pos : Merged N (colorPick N core home color B) l (coloredPack N core home color B)→EuclideanSpace ℝ (Fin d))
    (hpos : ∀q,‖pos q‖≤1) :
    let colors : ∀e∈core,color (N.src e)=color (N.dst e) := fun e _=>by rw [painted,painted,same e]
    let addr := nativeKey N core home color B col colors l
    let M := GadgetNetwork.merged N (colorPick N core home color B) sw l (coloredPack N core home color B) pos hpos
    ∀ e : M.Edge, addr (M.dst e)∈directory near D (A+2) 8 (addr (M.src e)) ∧
      addr (M.src e)∈directory near D (A+2) 8 (addr (M.dst e)) := by
  intro colors addr M
  let pick := colorPick N core home color B
  let packs := coloredPack N core home color B
  let physical := packAddress N core home color B col
  have room := pack_room N core home color B col A positive cap
  obtain ⟨wires,mates⟩:=native_links N core home color B col near D a load markLimit position block
    A positive cap realized same adj
  exact merged_cables_both near D (A+2) N pick l packs (chosenSlot N core home color B)
    (chosenCenter N core home color B l) (colorPick_thin_src N core home color B)
    (native_centerAt N core home color B colors l) (native_coherent _ B _ _ _ l)
    physical room wires mates sw pos hpos

/-- The original source of the old wire, or of the thick wire naming a
born arm or supply, lies in this fixed four-hop common neighborhood. -/
theorem native_donor (A : ℕ) (positive : 0<B)
    (cap : ∀c,amount (live (nativeTraffic N core home)) (thinList home color c)≤A*B)
    (realized : ∀u,col (home u)=colonyCode N markCap near D a load markLimit position block u)
    (same : ∀e,block (N.src e)=block (N.dst e))
    (adj : ∀e,position (N.dst e)∈near (position (N.src e)) ∧ position (N.src e)∈near (position (N.dst e)))
    (colors : ∀e∈core,color (N.src e)=color (N.dst e)) (l : Bool) :
    let pk:=colorPick N core home color B
    let pack:=coloredPack N core home color B
    let addr:=nativeKey N core home color B col colors l
    ∀e : GadgetNetwork.Edge (I:=NativePair N core home color B) N,
      packAddress N core home color B col (pack (N.src (donorEdge N pk e)))∈
        directory near D (A+2) 4 (addr (GadgetNetwork.newSite N pk l pack (GadgetNetwork.source N e))) := by
  obtain ⟨wires,mates⟩:=native_links N core home color B col near D a load markLimit position block
    A positive cap realized same adj
  exact donor_mem near D (A+2) N _ l _ (chosenSlot N core home color B) (chosenCenter N core home color B l)
    (colorPick_thin_src N core home color B) (native_centerAt N core home color B colors l)
    (native_coherent _ B _ _ _ l) (packAddress N core home color B col) (pack_room N core home color B col A positive cap)
    wires mates

theorem native_old_donor (A : ℕ) (positive : 0<B)
    (cap : ∀c,amount (live (nativeTraffic N core home)) (thinList home color c)≤A*B)
    (realized : ∀u,col (home u)=colonyCode N markCap near D a load markLimit position block u)
    (same : ∀e,block (N.src e)=block (N.dst e))
    (adj : ∀e,position (N.dst e)∈near (position (N.src e)) ∧ position (N.src e)∈near (position (N.dst e)))
    (colors : ∀e∈core,color (N.src e)=color (N.dst e)) (l : Bool) :
    let pk:=colorPick N core home color B
    let pack:=coloredPack N core home color B
    let addr:=nativeKey N core home color B col colors l
    ∀u : N.Site,
      packAddress N core home color B col (pack u)∈
        directory near D (A+2) 4 (addr (GadgetNetwork.newSite N pk l pack (.inl u))) := by
  obtain ⟨wires,mates⟩:=native_links N core home color B col near D a load markLimit position block
    A positive cap realized same adj
  exact old_donor_mem near D (A+2) N _ l _ (chosenSlot N core home color B) (chosenCenter N core home color B l)
    (colorPick_thin_src N core home color B) (native_centerAt N core home color B colors l)
    (native_coherent _ B _ _ _ l) (packAddress N core home color B col) (pack_room N core home color B col A positive cap)
    wires mates

theorem native_born_donor (A : ℕ) (positive : 0<B)
    (cap : ∀c,amount (live (nativeTraffic N core home)) (thinList home color c)≤A*B)
    (realized : ∀u,col (home u)=colonyCode N markCap near D a load markLimit position block u)
    (same : ∀e,block (N.src e)=block (N.dst e))
    (adj : ∀e,position (N.dst e)∈near (position (N.src e)) ∧ position (N.src e)∈near (position (N.dst e)))
    (colors : ∀e∈core,color (N.src e)=color (N.dst e)) (l : Bool) :
    let pk:=colorPick N core home color B
    let pack:=coloredPack N core home color B
    let addr:=nativeKey N core home color B col colors l
    ∀(i : NativePair N core home color B) (j : Fin 6),
      packAddress N core home color B col (pack (N.src (pk (i,0))))∈
        directory near D (A+2) 4 (addr (GadgetNetwork.newSite N pk l pack (.inr (i,j)))) := by
  obtain ⟨wires,mates⟩:=native_links N core home color B col near D a load markLimit position block
    A positive cap realized same adj
  exact born_donor_mem near D (A+2) N _ l _ (chosenSlot N core home color B) (chosenCenter N core home color B l)
    (colorPick_thin_src N core home color B) (native_centerAt N core home color B colors l)
    (native_coherent _ B _ _ _ l) (packAddress N core home color B col) (pack_room N core home color B col A positive cap)
    wires mates

theorem native_cables (A : ℕ) (positive : 0<B)
    (cap : ∀c,amount (live (nativeTraffic N core home)) (thinList home color c)≤A*B)
    (realized : ∀u,col (home u)=colonyCode N markCap near D a load markLimit position block u)
    (same : ∀e,block (N.src e)=block (N.dst e))
    (adj : ∀e,position (N.dst e)∈near (position (N.src e)) ∧ position (N.src e)∈near (position (N.dst e)))
    (sheet : Block k→Bool) (painted : ∀u,color u=sheet (block u))
    (l : Bool) (sw : NativePair N core home color B→Fin 8→ℕ) {d : ℕ}
    (pos : Merged N (colorPick N core home color B) l (coloredPack N core home color B)→EuclideanSpace ℝ (Fin d))
    (hpos : ∀q,‖pos q‖≤1) :
    let colors : ∀e∈core,color (N.src e)=color (N.dst e) := fun e _=>by rw [painted,painted,same e]
    let addr := nativeKey N core home color B col colors l
    let M := GadgetNetwork.merged N (colorPick N core home color B) sw l (coloredPack N core home color B) pos hpos
    ∀ e : M.Edge, addr (M.dst e)∈directory near D (A+2) 8 (addr (M.src e)) := by
  intro colors addr M e
  exact (native_cables_both N core home color B col near D a load markLimit position block A positive cap realized same adj sheet painted l sw pos hpos e).1

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
