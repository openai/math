import OAI.Hierarchy.ProtocolRAMPurchaseMarketResult

namespace OAI
/-! # The physical rows, socket numbers and reverse digits left by a frozen market -/

namespace Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT ProtocolRAMPurchaseAllocation
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k : ℕ}

/-- All the input words used to encode the two endpoints of a purchased path. -/
structure PortData (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (i : Key z d k) (out : Mem z d) : Prop where
  tiles : ProtocolRAMPurchaseGateColumns.TileRows (sh.L S depth i).source (pathRows S π depth i) out
  directory : PurchaseDirectory.Loaded (sh.L S depth i).directory (2^z) S.degree depth out
  inputSocket : Resident (banks (stage i)).input out (fun r => ((advisedStage z d π (stage i)).input r).val)
  outputSocket : Resident (banks (stage i)).output out (fun r => ((advisedStage z d π (stage i)).output r).val)
  back : ∀ j : Fin S.degree,let L:=sh.L S depth i
    Resident (ProtocolRAMPurchaseSampler.backward L.start L.groups L.sockets S.degree j) out
      (fun o => (reverseDigits S L.sockets o j).val)

theorem portData (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (hd : 1≤d) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen fixture : Mem z d)
    (input : sh.Incoming (k:=k) S π depth phase T kind frozen)
    (prepared : ∀ i : Key z d k, sh.Prepared S depth fixture i frozen)
    (room : sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies)
    (i : Key z d k) : sh.PortData S π depth i (sh.result S k depth frozen) := by
  let L:=sh.L S depth i
  let t:=stage i
  let p:=advisedStage z d π t
  let f:=sh.result S k depth frozen
  obtain ⟨_,frame,views,_⟩:=sh.run S π depth hd phase T kind frozen fixture input prepared room
  have obs := views i
  have bounds := sh.end_le S depth i hd
  obtain ⟨s₀,s₁,s₂,s₃,s₄,s₅,s₆,s₇,s₈⟩ := L.regions
  have size := input.dimensions i
  obtain ⟨enc,ct⟩ := input.ct i
  have loaded := L.loaded_inside (banks t) p enc (S.rows L.sockets) (reverseDigits S L.sockets)
    fixture frozen (fun a lo hi => prepared i a lo (hi.trans_le bounds)) size.ct ct size.sockets size.room
  have keep (c : Fin 3) (r : Word _) : (stageBank z d (stageNumber t) c).read f r=
      (stageBank z d (stageNumber t) c).read frozen r := by
    apply frame
    exact Or.inl ((Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le
      ((stageBank_end z d (stageNumber t) c).trans input.afterCT))
  refine ⟨obs.tiles,?_,fun r=>(keep 1 _).trans (ct.input r),fun r=>(keep 2 _).trans (ct.output r),?_⟩
  · apply loaded.starts.of_frame
    intro a lo hi
    exact obs.rom a (Or.inl ⟨s₀.trans lo,hi.trans_le s₁.le⟩)
  · intro j
    let b := ProtocolRAMPurchaseSampler.backward L.start L.groups L.sockets S.degree j
    have limit : L.start+ProtocolRAMPurchaseSampler.words L.groups L.sockets L.degree<2^(wordBits z d copies) := by
      change L.directory<_
      have hi := size.room
      change L.endAddress<_ at hi
      omega
    have fit := ProtocolRAMPurchaseSampler.backward_fits L.start L.groups j limit
    have back := L.reverse_loaded (S.rows L.sockets) (reverseDigits S L.sockets) fixture j size.sockets size.room
    dsimp only
    intro o
    let index : Word (wordBits z d copies) := (o.val:ℕ)
    let a:=b.base+index.val%b.size
    have small : a<L.directory := (Nat.add_lt_add_left (Nat.mod_lt _ fit.1) _).trans_le fit.2.2
    have large : L.start≤a := by
      dsimp [a,b,ProtocolRAMPurchaseSampler.backward,ProtocolRAMPurchaseSampler.lane]
      omega
    have inner : a<L.signed.base := by omega
    have first := obs.rom a (Or.inl ⟨large,inner⟩)
    have stable := prepared i a large ((show a<L.endAddress by omega).trans_le bounds)
    exact (first.trans stable).trans (back o)

end
end Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

end OAI
