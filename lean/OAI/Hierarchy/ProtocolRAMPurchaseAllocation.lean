import OAI.Hierarchy.ProtocolRAMPurchaseROMData
import OAI.Hierarchy.ProtocolRAMPurchaseSourceLayout
import OAI.Hierarchy.ProtocolRAMPurchaseCTShape
import OAI.Hierarchy.ProtocolRAMPurchaseSampler
import OAI.Hierarchy.ProtocolRAMPurchaseFields

namespace OAI
/-! # Consecutive memory regions for one sampler purchase stage

The allocation starts above the live CT banks. Its directories depend only on
the stage geometry, the chosen sampler, and the ordinal of the first candidate.
A signed mark bank separates the immutable DFS directory from the owner writes.
-/

namespace Hierarchy.ProtocolRAMPurchaseAllocation

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

namespace Layout

def gatesCount (L : Layout) := ProtocolRAMPurchaseGateColumns.gates L.candidates (L.height+1)
theorem candidates_eq (L : Layout) : L.candidates=L.rows*L.degree^L.height := by
  simp [candidates,PurchaseTape.count,PurchaseDFS.length_layout]

theorem gatesCount_eq (L : Layout) : L.gatesCount=L.rows*(L.degree^L.height*(4*(L.height+1)+3)) := by
  rw [gatesCount,ProtocolRAMPurchaseGateColumns.gates,L.candidates_eq,Nat.mul_assoc]

def packed (L : Layout) := ProtocolRAMPurchaseGateColumns.packedBase L.source L.candidates (L.height+1)
def endAddress (L : Layout) := L.work+4+(L.rows+1)+L.first+L.candidates

def plan (L : Layout) (ct : CT) : PurchaseTape.Plan L.degree where
  columns := ⟨ct.group,ct.input,ct.output,ProtocolRAMPurchaseSampler.stride L.start L.groups,L.owner⟩
  neighbor := ProtocolRAMPurchaseSampler.neighbor L.start L.groups L.sockets
  ownerScratch := L.scratch
  directory := L.directory
  source := L.source
  gates := L.gates
  work := L.work
  first := L.first
  packed := L.packed

structure Regions (L : Layout) : Prop where
  start : L.start≤L.directory
  ids : L.directory+(L.height+1)*PurchaseDirectory.span L.rows L.degree L.height=L.signed.base
  mark : L.signed.base+L.signed.size=L.owner.base
  owner : L.owner.base+L.owner.size=L.scratch
  scatter : L.scratch+2*L.rows=L.source.base
  source : L.source.base+L.source.size=L.gates.base
  gateROM : L.gates.base+6*L.gates.stride=L.packed
  tape : L.packed+3*L.gatesCount=L.work
  limit : L.work+4+(L.rows+1)+L.first+L.candidates=L.endAddress

theorem regions (L : Layout) : Regions L :=
  ⟨Nat.le_add_right ..,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

structure CTFits (L : Layout) (ct : CT) (w : ℕ) : Prop where
  group : ct.group.Fits w L.start
  input : ct.input.Fits w L.start
  output : ct.output.Fits w L.start

private theorem fits_mono {b : Bank} {w a z : ℕ} (h : b.Fits w a) (lo : a≤z) :
    b.Fits w z := ⟨h.1,h.2.1,h.2.2.trans lo⟩

theorem fits {w : ℕ} (L : Layout) (ct : CT) (c : L.CTFits ct w) (wide : 0<w)
    (degree : L.degree≤2^w) (room : L.endAddress<2^w) :
    PurchaseTape.Fits (L.plan ct) w L.rows L.groups L.sockets L.height := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ := L.regions
  have inc : L.start≤L.owner.base := by omega
  have romRoom : L.start+ProtocolRAMPurchaseSampler.words L.groups L.sockets L.degree < 2^w := by
    change L.directory<2^w
    omega
  have groups := fits_mono c.group inc
  have inputs := fits_mono c.input inc
  have outputs := fits_mono c.output inc
  have stride := fits_mono (ProtocolRAMPurchaseSampler.stride_fits L.start L.groups L.sockets L.degree romRoom)
    (show L.directory≤L.owner.base by omega)
  have choices (j : Fin L.degree) := fits_mono (ProtocolRAMPurchaseSampler.neighbor_fits L.start L.groups j romRoom)
    (show L.directory≤L.owner.base by omega)
  have ownerCap : L.groups*L.sockets≤L.owner.size := (ProtocolRAMPurchaseSampler.lt_span _).le
  have ownerFits : L.owner.Fits w L.scratch := ⟨Nat.two_pow_pos _,by omega,h3.le⟩
  have scratchRoom : L.scratch+2*L.rows<2^w := by omega
  have sourceFits : L.source.Fits w L.packed := ⟨Nat.two_pow_pos _,by omega,by omega⟩
  have ctSource : L.owner.base≤L.source.base := by omega
  have dirSource : L.directory+(L.height+1)*PurchaseDirectory.span L.rows L.degree L.height≤L.source.base := by omega
  refine ⟨⟨groups,inputs,outputs,stride,ownerCap,ownerFits,scratchRoom⟩,by omega,degree,wide,
    choices,by change L.directory+_≤L.owner.base; omega,.inr ⟨by change L.scratch+2*L.rows≤L.gates.base; omega,h5.le⟩,
    ctSource,?_,(ProtocolRAMPurchaseSampler.lt_span _).le,sourceFits,?_,?_⟩
  · exact PurchaseTape.fields_below (L.plan ct) L.rows L.height
      (groups.2.2.trans ctSource) (stride.2.2.trans ctSource) (outputs.2.2.trans ctSource)
      (show L.owner.base+L.owner.size≤L.source.base by omega)
      (fun j => (choices j).2.2.trans ctSource) dirSource
  · intro j hj
    have endBound := Nat.mul_le_mul_right L.gates.stride hj
    rw [Nat.succ_mul] at endBound
    change 0<L.gates.stride ∧ L.gates.stride<2^w ∧ L.gates.base+j*L.gates.stride+L.gates.stride≤L.packed
    exact ⟨Nat.two_pow_pos _,by omega,by omega⟩
  · change L.packed+3*L.gatesCount<2^w
    omega

theorem signed_capacity (L : Layout) : L.rows+1≤L.signed.size :=
  (ProtocolRAMPurchaseSampler.lt_span _).le

theorem signed_fits {w : ℕ} (L : Layout) (room : L.endAddress<2^w) :
    L.signed.Fits w L.owner.base := by
  obtain ⟨_,_,h2,h3,h4,h5,h6,h7,h8⟩ := L.regions
  exact ⟨Nat.two_pow_pos _,by omega,h2.le⟩

private theorem after_sampler {w : ℕ} (L : Layout) (next : Fin L.sockets → List (Fin L.sockets))
    (back : Fin L.sockets → Fin L.degree → Fin L.degree) (mem : Memory w) (a : ℕ) (low : a<L.directory) :
    L.data next back mem a=ProtocolRAMPurchaseSampler.install L.start L.groups next back mem a := by
  obtain ⟨_,h1,h2,h3,h4,h5,_,_,_⟩ := L.regions
  exact (GateColumns.mount_frame _ _ _ (.inl (by omega))).trans
    (PurchaseDirectory.frame _ _ _ _ _ a (.inl low))

theorem data_prefix {w : ℕ} (L : Layout) (next : Fin L.sockets → List (Fin L.sockets))
    (back : Fin L.sockets → Fin L.degree → Fin L.degree) (mem : Memory w) (a : ℕ) (low : a<L.start) :
    L.data next back mem a=mem a :=
  (L.after_sampler next back mem a (low.trans_le L.regions.start)).trans
    (ProtocolRAMPurchaseSampler.frame _ _ _ _ _ _ (.inl low))

/-- The static tape can be installed once before any CT execution framed above
the allocation start. Reinstalling after that execution leaves all words intact. -/
theorem remount_eq {w : ℕ} (L : Layout) (next : Fin L.sockets → List (Fin L.sockets))
    (back : Fin L.sockets → Fin L.degree → Fin L.degree) (raw after : Memory w)
    (same : ∀ a,L.start≤a → after a=L.data next back raw a) :
    L.data next back after=after := by
  funext a
  by_cases low : a<L.start
  · exact L.data_prefix next back after a low
  · have stable := same a (by omega)
    simp only [data,GateColumns.mount,PurchaseDirectory.install,
      ProtocolRAMPurchaseSampler.install,fillSegment] at stable ⊢
    split_ifs <;> simp_all

theorem read_prefix {w : ℕ} (L : Layout) (next : Fin L.sockets → List (Fin L.sockets))
    (back : Fin L.sockets → Fin L.degree → Fin L.degree) (mem : Memory w) (b : Bank)
    (fit : b.Fits w L.start) (r : Word w) : b.read (L.data next back mem) r=b.read mem r := by
  exact L.data_prefix next back mem _ ((Nat.add_lt_add_left (Nat.mod_lt _ fit.1) b.base).trans_le fit.2.2)

theorem data_signed {w : ℕ} (L : Layout) (next : Fin L.sockets → List (Fin L.sockets))
    (back : Fin L.sockets → Fin L.degree → Fin L.degree) (mem : Memory w) (a : ℕ)
    (lo : L.signed.base≤a) (hi : a<L.owner.base) : L.data next back mem a=mem a := by
  obtain ⟨_,h1,h2,h3,h4,h5,_,_,_⟩ := L.regions
  exact ((GateColumns.mount_frame _ _ _ (.inl (by omega))).trans
    (PurchaseDirectory.frame _ _ _ _ _ a (.inr (by omega)))).trans
    (ProtocolRAMPurchaseSampler.frame _ _ _ _ _ _ (.inr (by change L.directory≤a; omega)))

/-- The reverse sampler digits survive both later public mounts in the same memory. -/
theorem reverse_loaded {w : ℕ} (L : Layout) (next : Fin L.sockets → List (Fin L.sockets))
    (back : Fin L.sockets → Fin L.degree → Fin L.degree) (mem : Memory w) (j : Fin L.degree)
    (sockets : L.sockets≤2^w) (room : L.endAddress<2^w) :
    Native.Resident (ProtocolRAMPurchaseSampler.backward L.start L.groups L.sockets L.degree j)
      (L.data next back mem) (fun o => (back o j).val) := by
  obtain ⟨_,h1,h2,h3,h4,h5,h6,h7,h8⟩ := L.regions
  have safe : L.start+ProtocolRAMPurchaseSampler.words L.groups L.sockets L.degree < 2^w := by
    change L.directory<2^w
    omega
  exact ProtocolRAMPurchaseOwners.resident_frame
    (ProtocolRAMPurchaseSampler.backward_fits L.start L.groups j safe) (L.after_sampler next back mem)
    (ProtocolRAMPurchaseSampler.reverse_resident L.start L.groups next back mem sockets j)

theorem loaded {w : ℕ} (L : Layout) (ct : CT) {G : Type*} (p : Tiles (Fin L.rows) G L.sockets)
    (e : G ↪ Fin L.groups) (next : Fin L.sockets → List (Fin L.sockets))
    (back : Fin L.sockets → Fin L.degree → Fin L.degree) (mem : Memory w)
    (c : L.CTFits ct w) (live : L.CTLoaded ct p e mem) (sockets : L.sockets≤2^w)
    (room : L.endAddress<2^w) :
    PurchaseTape.Loaded (L.plan ct) p e (fun o j => ProtocolRAMPurchaseSampler.sample next o j)
      L.height (L.data next back mem) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ := L.regions
  have romRoom : L.start+ProtocolRAMPurchaseSampler.words L.groups L.sockets L.degree<2^w := by
    change L.directory<2^w
    omega
  have groupRoom : L.groups≤2^w := by
    have below := ProtocolRAMPurchaseSampler.lt_span L.groups
    change L.start+(ProtocolRAMPurchaseSampler.span L.groups+_)<2^w at romRoom
    omega
  have rowsRoom : L.candidates≤2^w := by omega
  have stride := ProtocolRAMPurchaseSampler.stride_fits L.start L.groups L.sockets L.degree romRoom
  have goodChoices (j : Fin L.degree) := ProtocolRAMPurchaseSampler.neighbor_fits L.start L.groups j romRoom
  let sampler := ProtocolRAMPurchaseSampler.install L.start L.groups next back mem
  let digits := PurchaseDirectory.install L.directory L.rows L.degree L.height sampler
  refine ⟨⟨ProtocolRAMPurchaseOwners.resident_frame c.group (L.data_prefix next back mem) live.group,
    ProtocolRAMPurchaseOwners.resident_frame c.input (L.data_prefix next back mem) live.input,
    ProtocolRAMPurchaseOwners.resident_frame c.output (L.data_prefix next back mem) live.output,
    ProtocolRAMPurchaseOwners.resident_frame stride (L.after_sampler next back mem)
      (ProtocolRAMPurchaseSampler.stride_resident L.start L.groups next back mem groupRoom)⟩,?_,?_,?_⟩
  · apply (PurchaseDirectory.install_loaded L.directory sampler rowsRoom).of_frame
    intro a lo hi
    exact GateColumns.mount_frame _ _ _ (.inl (by omega))
  · intro j
    exact ProtocolRAMPurchaseOwners.resident_frame (goodChoices j) (L.after_sampler next back mem)
      (ProtocolRAMPurchaseSampler.neighbor_resident L.start L.groups next back mem sockets j)
  · exact GateColumns.mount_mounted L.gates _ digits (GateColumns.directory_capacity ..) (by omega)

/-- The generated CT columns and the original public advice are simultaneously
resident in the output memory of the framed CT computation. -/
theorem loaded_after {w : ℕ} (L : Layout) (ct : CT) {G : Type*} (p : Tiles (Fin L.rows) G L.sockets)
    (e : G ↪ Fin L.groups) (next : Fin L.sockets → List (Fin L.sockets))
    (back : Fin L.sockets → Fin L.degree → Fin L.degree) (raw after : Memory w)
    (same : ∀ a,L.start≤a → after a=L.data next back raw a) (c : L.CTFits ct w)
    (live : L.CTLoaded ct p e after) (sockets : L.sockets≤2^w) (room : L.endAddress<2^w) :
    PurchaseTape.Loaded (L.plan ct) p e (fun o j => ProtocolRAMPurchaseSampler.sample next o j)
      L.height after := by
  simpa only [L.remount_eq next back raw after same] using L.loaded ct p e next back after c live sockets room

/-- Execute the canonical purchase-tape compiler from the three actual tile columns. -/
theorem run {w : ℕ} (L : Layout) (ct : CT) {G : Type*} (p : Tiles (Fin L.rows) G L.sockets)
    (e : G ↪ Fin L.groups) (next : Fin L.sockets → List (Fin L.sockets))
    (back : Fin L.sockets → Fin L.degree → Fin L.degree) (mem : Memory w)
    (c : L.CTFits ct w) (live : L.CTLoaded ct p e mem) (wide : 0<w)
    (deg : L.degree≤2^w) (sockets : L.sockets≤2^w) (room : L.endAddress<2^w) :
    let s := L.plan ct
    let initial := L.data next back mem
    let out := PurchaseTape.output s p e L.height initial
    (PurchaseTape.code s w L.rows L.groups L.sockets L.height).Exec initial out
      (PurchaseTape.ticks s L.rows L.groups L.sockets L.height) ∧
    MarkTape.Packed s.packed (MarkTape.compilePaths (L.rows+1) s.work s.first
      (PurchaseTape.paths (D:=L.degree) p e (fun o j => ProtocolRAMPurchaseSampler.sample next o j) L.height)) out :=
  PurchaseTape.run (L.plan ct) p e _ L.height _ (L.fits ct c wide deg room)
    (L.loaded ct p e next back mem c live sockets room)

/-- Full address bound, including the mark interpreter's decision array. -/
theorem end_bound (L : Layout) :
    L.endAddress ≤ L.start+(2*(L.groups+1)+4*L.degree*(L.sockets+1))+
      (L.height+1)*(2*(L.rows*L.degree^L.height+1))+2*(L.rows+2)+2*(L.groups*L.sockets+1)+2*L.rows+
      2*((L.height+1)*L.candidates+1)+15*(L.gatesCount+1)+4+(L.rows+1)+L.first+L.candidates := by
  obtain ⟨_,h1,h2,h3,h4,_,_,_,h8⟩ := L.regions
  have d : L.directory≤L.start+(2*(L.groups+1)+4*L.degree*(L.sockets+1)) :=
    Nat.add_le_add_left (ProtocolRAMPurchaseSampler.words_bound ..) _
  have digit := Nat.mul_le_mul_left (L.height+1) (PurchaseDirectory.span_le (n:=L.rows) (D:=L.degree) (h:=L.height))
  have mark : L.signed.size≤2*(L.rows+1+1) := ProtocolRAMPurchaseSampler.span_le _
  have own : L.owner.size≤2*(L.groups*L.sockets+1) := ProtocolRAMPurchaseSampler.span_le _
  have src : L.source.size≤2*((L.height+1)*L.candidates+1) := ProtocolRAMPurchaseSampler.span_le _
  have gate : L.work≤L.source.base+L.source.size+15*(L.gatesCount+1) := ProtocolRAMPurchaseGateColumns.markBase_le ..
  omega

theorem end_linear (L : Layout) (K : ℕ) (rows : 0<L.rows) (groups : 1≤L.groups)
    (sockets : 1≤L.sockets) (first : L.first=0) (slots : L.groups*L.sockets≤K*L.rows) :
    L.endAddress≤L.start+linearFactor K L.degree L.height*L.rows := by
  let H := L.height+1
  let p := L.degree^L.height
  have bump {a b : ℕ} (small : a≤b*L.rows) : a+1≤(b+1)*L.rows := by
    rw [Nat.add_mul,Nat.one_mul]
    omega
  have gr : L.groups≤L.groups*L.sockets := by simpa using Nat.mul_le_mul_left L.groups sockets
  have so : L.sockets≤L.groups*L.sockets := by simpa using Nat.mul_le_mul_right L.sockets groups
  have groupBound := bump (gr.trans slots)
  have socketBound := bump (so.trans slots)
  have slotBound := bump slots
  have candidateBound : L.rows*p+1 ≤ (p+1)*L.rows := bump (Nat.mul_comm _ _).le
  have fieldBound : H*L.candidates+1 ≤ (H*p+1)*L.rows := by
    apply bump
    rw [L.candidates_eq]
    dsimp [p]
    exact le_of_eq (by ring)
  have gateBound : L.gatesCount+1 ≤ (p*(4*H+3)+1)*L.rows := by
    apply bump
    rw [L.gatesCount_eq]
    exact (Nat.mul_comm ..).le
  have tupleCount : L.candidates=p*L.rows := L.candidates_eq.trans (Nat.mul_comm ..)
  have size := L.end_bound
  rw [first,Nat.add_zero] at size
  calc
    _ ≤ _ := size
    _ ≤ L.start+(2*((K+1)*L.rows)+4*L.degree*((K+1)*L.rows))+
        H*(2*((p+1)*L.rows))+2*(3*L.rows)+2*((K+1)*L.rows)+2*L.rows+
        2*((H*p+1)*L.rows)+15*((p*(4*H+3)+1)*L.rows)+4*L.rows+2*L.rows+p*L.rows := by
      gcongr <;> first | assumption | exact tupleCount.le | omega
    _ = _ := by dsimp [linearFactor,p,H]; ring

theorem end_linear_of_start (L : Layout) (K S : ℕ) (rows : 0<L.rows) (groups : 1≤L.groups)
    (sockets : 1≤L.sockets) (first : L.first=0) (slots : L.groups*L.sockets≤K*L.rows)
    (start : L.start≤S*L.rows) : L.endAddress≤(S+linearFactor K L.degree L.height)*L.rows := by
  rw [Nat.add_mul]
  exact (L.end_linear K rows groups sockets first slots).trans (Nat.add_le_add_right start _)

theorem end_lt_word (L : Layout) (K S rowBits extra : ℕ) (dyadic : L.rows=2^rowBits)
    (groups : 1≤L.groups) (sockets : 1≤L.sockets) (first : L.first=0)
    (slots : L.groups*L.sockets≤K*L.rows) (start : L.start≤S*L.rows)
    (budget : S+linearFactor K L.degree L.height<2^extra) :
    L.endAddress<2^(rowBits+extra) := by
  have pos : 0<L.rows := by rw [dyadic]; exact Nat.two_pow_pos _
  have size := L.end_linear_of_start K S pos groups sockets first slots start
  rw [dyadic,Nat.mul_comm (S+_)] at size
  rw [pow_add]
  exact size.trans_lt (Nat.mul_lt_mul_of_pos_left budget (Nat.two_pow_pos _))

/-- Dyadically many CT rows use the row width plus a constant determined by the stage parameters. -/
theorem end_lt_word_of_dyadic (L : Layout) (K S rowBits : ℕ) (dyadic : L.rows=2^rowBits)
    (groups : 1≤L.groups) (sockets : 1≤L.sockets) (first : L.first=0)
    (slots : L.groups*L.sockets≤K*L.rows) (start : L.start≤S*L.rows) :
    L.endAddress<2^(rowBits+(S+linearFactor K L.degree L.height)) := by
  exact L.end_lt_word K S rowBits _ dyadic groups sockets first slots start Nat.lt_two_pow_self


end Layout
end Hierarchy.ProtocolRAMPurchaseAllocation

end OAI
