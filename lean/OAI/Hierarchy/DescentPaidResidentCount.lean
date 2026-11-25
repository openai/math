import OAI.Hierarchy.DescentPackedActorMask
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Local charged particle counts from the old books and the six genuine birth roles -/
namespace Hierarchy.DescentPaidResidentCount
open DescentSIMDLookup DescentPackedZip DescentPackedActorMask
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {D cap b n H G M w : ℕ}
local notation "size" => actors D cap

def birthSlot (cap : ℕ) (j : Fin (D*(cap*6))) :=
  let p:=finProdFinEquiv.symm j
  bornAddress p.1 p.2

/-- The prior funded length at each old address and a single unit at each
born matched role. The target mask is indexed by actors, independent of
the number of external scalar nodes at that location. -/
def mass (D cap b : ℕ) (mask : Cell (1*actors D cap)) (count : Cell (b*D)) : ℕ :=
  let selected:=(encode 1 (actors D cap)).symm mask
  let old:=(encode b D).symm count
  (∑v : Fin D,if (selected (oldAddress cap v)).val=1 then (old v).val else 0)+
    ∑j : Fin (D*(cap*6)),if (selected (birthSlot cap j)).val=1 then 1 else 0

def counted (D cap b : ℕ) (mask : Cell (1*actors D cap)) (count : Cell (b*D)) : Cell b :=
  mass D cap b mask count

theorem empty (D cap b : ℕ) : counted D cap b 0 0=0 := by
  have zero : (encode 1 (actors D cap)).symm 0=fun _=>0 := by
    apply (encode 1 _).injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    change 0=(finFunctionFinEquiv (fun _ : Fin (actors D cap)=>(0:Cell 1))).val
    simp []
  simp [counted,mass,zero]

theorem seen (wanted : Cell n) (dest : Fin size→Cell n) (count : Fin D→Cell b) :
    mass D cap b (target n size wanted (encode n size dest)) (encode b D count)=
    (∑v : Fin D,if wanted≠0 ∧ dest (oldAddress cap v)=wanted then (count v).val else 0)+
      ∑j : Fin (D*(cap*6)),if wanted≠0 ∧ dest (birthSlot cap j)=wanted then 1 else 0 := by
  have bit (s : Fin size) :
      (((encode 1 size).symm (target n size wanted (encode n size dest))) s).val=1 ↔
        wanted≠0 ∧ dest s=wanted := by
    simp only [target,Equiv.symm_apply_apply]
    split <;> simp_all
  simp only [mass,Equiv.symm_apply_apply,bit]

theorem sum_image {α β : Type} [Fintype α] [Fintype β] (e : α↪β) (cost : α→ℕ)
    (flag : β→Prop) [decideFlag : DecidablePred flag] (get : β→ℕ) (present : ∀j,flag j ↔ ∃x,e x=j)
    (held : ∀x,get (e x)=cost x) :
    (∑j : β,if flag j then get j else 0)=∑x,cost x := by
  classical
  let occupied:=Finset.univ.map e
  have known (x : α) : flag (e x) := (present _).mpr ⟨x,rfl⟩
  calc
    _ = ∑j∈occupied,if flag j then get j else 0 := by
      apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro j _ outside
      have no : ¬flag j := by
        intro yes
        obtain ⟨x,rfl⟩:=(present _).mp yes
        exact outside (Finset.mem_map.mpr ⟨x,Finset.mem_univ _,rfl⟩)
      simp [no]
    _ = _ := by simp [occupied,known,held]

theorem paid {Old Born : Type} [Fintype Old] [Fintype Born] (oldSlot : Old↪Fin D)
    (bornSlot : Born↪Fin (D*(cap*6))) (cost : Old→ℕ) (wanted : Cell n) (dest : Fin size→Cell n)
    (count : Fin D→Cell b) (alive : wanted≠0)
    (oldSites : ∀j, dest (oldAddress cap j)=wanted ↔ ∃u,oldSlot u=j)
    (bornSites : ∀j, dest (birthSlot cap j)=wanted ↔ ∃u,bornSlot u=j)
    (read : ∀u,(count (oldSlot u)).val=cost u) :
    counted D cap b (target n size wanted (encode n size dest)) (encode b D count)=
      ((∑u,cost u)+Fintype.card Born:ℕ) := by
  apply congrArg (fun x : ℕ=>(x : Cell b))
  rw [seen]
  have old:=sum_image oldSlot cost (fun j=>wanted≠0 ∧ dest (oldAddress cap j)=wanted)
    (decideFlag:=fun j=>inferInstanceAs (Decidable (wanted≠0 ∧ dest (oldAddress cap j)=wanted)))
    (fun j=>(count j).val) (fun j=>⟨fun ok=>(oldSites j).mp ok.2,fun u=>⟨alive,(oldSites j).mpr u⟩⟩) read
  have born:=sum_image bornSlot (fun _=>1) (fun j=>wanted≠0 ∧ dest (birthSlot cap j)=wanted)
    (decideFlag:=fun j=>inferInstanceAs (Decidable (wanted≠0 ∧ dest (birthSlot cap j)=wanted)))
    (fun _=>1) (fun j=>⟨fun ok=>(bornSites j).mp ok.2,fun u=>⟨alive,(bornSites j).mpr u⟩⟩) (fun _=>rfl)
  have ones : (∑ _ : Born,(1:ℕ))=Fintype.card Born:=by simp
  rw [ones] at born
  exact congrArg₂ Nat.add old born

def instruction (maskTable sumTable : Tables) (wanted dest count : Expr) :=
  sumTable.read (maskTable.read wanted dest) count

/-- One program samples the actual previous funded counters and the captured
old and birth destinations, returning the two-table result without materializing a mask. -/
theorem run (maskTable sumTable : Tables) (query dest count : Expr) (out : Bank) (m : Memory w)
    (maskRoom : DescentPackedZip.Fits maskTable query dest n (n*size) M out.base w)
    (sumRoom : DescentPackedZip.Fits sumTable (maskTable.read query dest) count (1*size) (b*D) M out.base w)
    (maskFixed : Static maskTable (target n size) M m) (sumFixed : Static sumTable (counted D cap b) M m)
    (wanted : Fin H→Fin G→Cell n) (address : Fin H→Fin G→Fin size→Cell n)
    (funded : Fin H→Fin G→Fin D→Cell b)
    (wantedSource : Source query wanted M m)
    (destSource : Source dest (fun h g=>encode n _ (address h g)) M m)
    (oldSource : Source count (fun h g=>encode b _ (funded h g)) M m)
    (space : out.base+H*chunks G M<2^w) :
    let expr:=instruction maskTable sumTable query dest count
    let result:=image out.base (H*chunks G M) expr m
    (scan w out.base (H*chunks G M) expr).Exec m result (4+H*chunks G M*(2*expr.work+4)) ∧
    DescentPackedColony.Reads out (fun h g=>counted D cap b
      (target n size (wanted h g) (encode n _ (address h g))) (encode b D (funded h g))) M result ∧
    CheapCode (scan w out.base (H*chunks G M) expr) := by
  intro expr result
  have flags:=read_data maskTable query dest out.base maskRoom (target n size) (target_zero ..) m maskFixed
    wanted _ wantedSource destSource
  have held:=read_data sumTable (maskTable.read query dest) count out.base sumRoom (counted D cap b) (empty ..)
    m sumFixed _ _ flags oldSource
  have fits : expr.Fits w out.base :=by
    change (sumTable.read (maskTable.read query dest) count).Fits w out.base
    exact ⟨sumRoom.apply,sumRoom.right,sumRoom.shift,sumRoom.left⟩
  refine ⟨scan_exec out.base (H*chunks G M) expr m fits space,?_,scan_cheap w out.base (H*chunks G M) expr⟩
  intro j
  exact (ProtocolRAMGeneratedWrite.read_image out.base (H*chunks G M) expr m (row H G M j)).trans (held j)

end
end Hierarchy.DescentPaidResidentCount

end OAI
