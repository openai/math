import OAI.Hierarchy.ProtocolRAMCalendarBoot
import OAI.ThreeFlat.Diagonal.TraceWordOrder
import OAI.ThreeFlat.Diagonal.TraceBanks

namespace OAI
/-! # Fixed input wires for the actual calendar's native header -/

noncomputable section
namespace Hierarchy.Tagged.WideHeader
open ProtocolRAM ProtocolRAM.Calendar ProbeStage ProbeStage.Native PurchaseCT PurchaseFrozen
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ThreeFlat.Diagonal.TraceWords
open scoped Classical Fin.CommRing

/-- A ROM construction supplies an immutable word or forwards the original
word at that address. Its address decisions have no dependence on private
selector or permutation values. -/
def Public {A : Type*} (p : (ℕ→A)→ℕ→A) : Prop :=
  ∀ a,(∀ x,p x a=x a) ∨ ∃ c,∀ x,p x a=c

private theorem compose {A : Type*} {p q : (ℕ→A)→ℕ→A} (hp : Public p) (hq : Public q) :
    Public (fun x=>p (q x)) := by
  intro a
  rcases hp a with copy|⟨c,fix⟩
  · simpa only [copy] using hq a
  · exact Or.inr ⟨c,fun x=>fix (q x)⟩

private theorem extend {A I : Type*} (f : I→ℕ) (g : I→A) :
    Public (Function.extend f g) := by
  intro a
  by_cases hit : ∃i,f i=a
  · exact Or.inr ⟨g (Classical.choose hit),fun x=>by simp [Function.extend,hit]⟩
  · exact Or.inl (fun x=>by simp [Function.extend,hit])

private theorem segment {W : ℕ} (base size : ℕ) (data : ℕ→Word W) :
    Public (fillSegment base size data) := by
  intro a
  by_cases hit : base≤a ∧ a<base+size
  · exact Or.inr ⟨data a,fun x=>by simp [fillSegment,hit]⟩
  · exact Or.inl (fun x=>by simp [fillSegment,hit])

private theorem slabs {A : Type*} {n : ℕ} (lo hi : Fin n→ℕ) (f : Fin n→(ℕ→A)→ℕ→A)
    (hf : ∀ i,Public (f i)) :
    Public (fun x=>ProtocolRAMStaticSlabs.mounted lo hi (fun i=>f i x) x) := by
  intro a
  cases own : ProtocolRAMStaticSlabs.owner lo hi a with
  | none => exact Or.inl (fun x=>by simp [ProtocolRAMStaticSlabs.mounted,own])
  | some i => simpa only [ProtocolRAMStaticSlabs.mounted,own] using hf i a

private theorem allocation {W : ℕ} (L : ProtocolRAMPurchaseAllocation.Layout)
    (next : Fin L.sockets→List (Fin L.sockets)) (back : Fin L.sockets→Fin L.degree→Fin L.degree) :
    Public (L.data (w:=W) next back) := by
  let spec := ProtocolRAMPurchaseGateColumns.spec (R:=L.candidates) (H:=L.height+1)
    (L.rows+1) L.work L.first
  let sampler := ProtocolRAMPurchaseSampler.install (w:=W) L.start L.groups next back
  let digits := PurchaseDirectory.install (w:=W) L.directory L.rows L.degree L.height
  have gates : Public (GateColumns.mount (w:=W) L.gates spec) :=
    segment L.gates.base (6*L.gates.stride)
      (fun a=>(GateColumns.directoryWord L.gates spec (a-L.gates.base) : Word W))
  have dir : Public digits := segment _ _ _
  have samples : Public sampler := segment _ _ _
  exact compose (p:=GateColumns.mount L.gates spec) (q:=fun m=>digits (sampler m)) gates
    (compose (p:=digits) (q:=sampler) dir samples)

private theorem localData {z d k : ℕ} (v : Market z d k) :
    Public (Boot.localData v) := by
  apply compose (p:=v.shelf.mountROM v.sampler k v.depth) (q:=Boot.price v)
  · apply slabs
    intro i
    let L := v.shelf.L v.sampler v.depth i
    exact allocation L (v.sampler.rows L.sockets) (reverseDigits v.sampler L.sockets)
  · exact segment _ _ _

/-- All original calendar initialization tables, including the CT
subdivision ROM, produce literal public bits or fixed raw input bits. -/
theorem header {z d k jobs : ℕ} (markets : Fin jobs→Market z d k) (S : ℕ) :
    Public (Boot.header markets S) := by
  apply compose (p:=inputTape z d _)
    (q:=fun x=>Boot.controller markets (Computability.VPVNP.RAMMemory.initialMemory S x))
  · let f := ArrayCell.address (h:=z) (d:=d)
    let g := fun a : ArrayCell z d=>(arrayValue z d a.1.val a.2.1 a.2.2.val : Word (wordBits z d copies))
    exact compose (p:=Function.extend f g) (q:=geometryTape z d copies _)
      (extend f g) (extend (GeometryCell.address (h:=z) (d:=d) copies) _ )
  · apply compose (p:=Boot.controller markets)
        (q:=fun x=>Computability.VPVNP.RAMMemory.initialMemory S x)
    · exact slabs _ _ _ (fun i=>localData (markets i))
    · intro a
      by_cases hit : a<S
      · exact Or.inl (fun x=>by simp [Computability.VPVNP.RAMMemory.initialMemory,hit])
      · exact Or.inr ⟨0,fun x=>by simp [Computability.VPVNP.RAMMemory.initialMemory,hit]⟩

/-- Install real initialization in the chronology's binary pin map,
with no extra table gates and no guessed constants. -/
theorem header_wiring {z d k jobs : ℕ} {V : Type*} (markets : Fin jobs→Market z d k) (S : ℕ)
    (raw : (V→Bool)→Boot.Tape z d)
    (source : ℕ→Fin (wordBits z d copies)→V⊕Bool)
    (read : ∀ x a j,bits (raw x a) j=Sum.elim x id (source a j)) :
    ∃ wire : Fin S→Fin (wordBits z d copies)→V⊕Bool,
      ∀ x a j,bits (Boot.header markets S (raw x) a.val) j=Sum.elim x id (wire a j) := by
  classical
  have each (a : Fin S) (j : Fin (wordBits z d copies)) :
      ∃ pin : V⊕Bool,∀ x,bits (Boot.header markets S (raw x) a.val) j=Sum.elim x id pin := by
    rcases header markets S a.val with cp|⟨c,fix⟩
    · exact ⟨source a.val j,fun x=>(congrArg (fun t=>bits t j) (cp (raw x))).trans (read x _ _)⟩
    · exact ⟨.inr (bits c j),fun x=>congrArg (fun t=>bits t j) (fix (raw x))⟩
  exact ⟨fun a j=>(each a j).choose,fun x a j=>(each a j).choose_spec x⟩

/-- The sorted CPU log uses one additional bank bit. Every initialization
record lies in the public RAM bank, so its extra high bit is a fixed zero. -/
theorem cpu_wiring {z d k jobs : ℕ} {V : Type*} (markets : Fin jobs→Market z d k) (S : ℕ)
    (raw : (V→Bool)→Boot.Tape z d) (source : ℕ→Fin (wordBits z d copies)→V⊕Bool)
    (read : ∀ x a j,bits (raw x a) j=Sum.elim x id (source a j)) :
    ∃ wire : Fin S→Fin (wordBits z d copies+1)→V⊕Bool,
      ∀ x a j,bits (ThreeFlat.Diagonal.TraceBanks.wide
        (Boot.header markets S (raw x) a.val)) j=Sum.elim x id (wire a j) := by
  obtain ⟨pins,connect⟩ := header_wiring markets S raw source read
  let W := wordBits z d copies
  let wire (a : Fin S) (j : Fin (W+1)) : V⊕Bool :=
    if h : j.val<W then pins a ⟨j.val,h⟩ else .inr false
  refine ⟨wire,fun x a j=>?_⟩
  by_cases h : j.val<W
  · simpa [wire,h,bits,ThreeFlat.Diagonal.TraceBanks.wide] using
      connect x a ⟨j.val,h⟩
  · let v := Boot.header markets S (raw x) a.val
    have top := v.isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_not_gt h))
    simpa [wire,h,bits,ThreeFlat.Diagonal.TraceBanks.wide,v] using
      Nat.testBit_eq_false_of_lt top

end Hierarchy.Tagged.WideHeader

end
end OAI
