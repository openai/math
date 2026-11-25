import OAI.Hierarchy.ProtocolRAMPurchaseSignedAllocation

namespace OAI
/-! # Memory preservation outside a whole sampler-purchase block -/

namespace Hierarchy.ProtocolRAMPurchaseAllocation.Layout
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {w k : ℕ}

/-- Each finite public table lies entirely inside the assigned slab. -/
theorem data_outside (L : ProtocolRAMPurchaseAllocation.Layout)
    (next : Fin L.sockets → List (Fin L.sockets)) (back : Fin L.sockets → Fin L.degree → Fin L.degree)
    (mem : Memory w) (a : ℕ) (away : a<L.start ∨ L.endAddress≤a) : L.data next back mem a=mem a := by
  rcases away with early|late
  · exact L.data_prefix next back mem a early
  · obtain ⟨_,h1,h2,h3,h4,h5,h6,h7,h8⟩ := L.regions
    exact ((GateColumns.mount_frame _ _ _ (.inr (by omega))).trans
      (PurchaseDirectory.frame _ _ _ _ _ a (.inr (by omega)))).trans
      (ProtocolRAMPurchaseSampler.frame _ _ _ _ _ _ (.inr (by change L.directory≤a; omega)))

/-- Static residency only has to be preserved at addresses inside the selected slab. -/
theorem remount_inside (L : ProtocolRAMPurchaseAllocation.Layout)
    (next : Fin L.sockets → List (Fin L.sockets)) (back : Fin L.sockets → Fin L.degree → Fin L.degree)
    (raw after : Memory w) (same : ∀ a,L.start≤a → a<L.endAddress → after a=L.data next back raw a) :
    L.data next back after=after := by
  funext a
  by_cases inside : L.start≤a ∧ a<L.endAddress
  · have stable := same a inside.1 inside.2
    simp only [data,GateColumns.mount,PurchaseDirectory.install,
      ProtocolRAMPurchaseSampler.install,fillSegment] at stable ⊢
    split_ifs <;> simp_all
  · exact L.data_outside next back after a (by omega)

theorem loaded_inside (L : ProtocolRAMPurchaseAllocation.Layout) (ct : CT) {G : Type*}
    (p : Tiles (Fin L.rows) G L.sockets) (e : G ↪ Fin L.groups)
    (next : Fin L.sockets → List (Fin L.sockets)) (back : Fin L.sockets → Fin L.degree → Fin L.degree)
    (raw after : Memory w) (same : ∀ a,L.start≤a → a<L.endAddress → after a=L.data next back raw a)
    (c : L.CTFits ct w) (live : L.CTLoaded ct p e after) (sockets : L.sockets≤2^w)
    (room : L.endAddress<2^w) :
    PurchaseTape.Loaded (L.plan ct) p e (fun o j => ProtocolRAMPurchaseSampler.sample next o j)
      L.height after := by
  simpa only [L.remount_inside next back raw after same] using
    L.loaded ct p e next back after c live sockets room

private theorem path_range (tiles work i : ℕ) (p : List (Fin tiles))
    (g : MarkTape.Gate) (hg : g∈MarkTape.compilePath tiles work i p) :
    work≤g.dst ∧ g.dst<work+4+tiles+i+1 := by
  simp only [MarkTape.compilePath,List.mem_append,List.mem_singleton,List.mem_flatMap] at hg
  rcases hg with (((root|⟨v,_,test⟩)|keep)|⟨v,_,clear⟩)|last
  · subst g; simp; omega
  · simp only [MarkTape.test,MarkTape.both,List.mem_cons,List.not_mem_nil,or_false] at test
    rcases test with rfl|rfl <;> simp <;> omega
  · subst g; simp; omega
  · simp only [MarkTape.clear,MarkTape.both,List.mem_cons,List.not_mem_nil,or_false] at clear
    rcases clear with rfl|rfl <;> simp <;> have := v.isLt <;> omega
  · subst g; simp; omega

private theorem paths_range (tiles work first : ℕ) (ps : List (List (Fin tiles)))
    (g : MarkTape.Gate) (hg : g∈MarkTape.compilePaths tiles work first ps) :
    work≤g.dst ∧ g.dst<work+4+tiles+first+ps.length := by
  induction ps generalizing first with
  | nil => simp [MarkTape.compilePaths] at hg
  | cons p ps ih =>
    rw [MarkTape.compilePaths,List.mem_append] at hg
    rcases hg with head|tail
    · have ⟨lo,hi⟩ := path_range tiles work first p g head
      simp only [List.length_cons]
      omega
    · have ⟨lo,hi⟩ := ih (first+1) tail
      simp only [List.length_cons]
      omega

private theorem dispatch_frame (L : PurchaseStage.Dispatch)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (mem : Memory w) (a : ℕ)
    (tape : a<L.tape ∨ L.tape+3*(L.candidates*(4*L.depth+3))≤a)
    (work : a<L.work ∨ L.work+4+L.tiles+L.first+L.candidates≤a) :
    PurchaseStage.dispatchMemory L rows mem a=mem a := by
  let paths := PurchaseStage.paths L rows
  have count : paths.length=L.candidates := by simp [paths,PurchaseStage.paths]
  let gates := MarkTape.compilePaths L.tiles L.work L.first paths
  have away (g : MarkTape.Gate) (hg : g∈gates) : a≠g.dst := by
    have ⟨lo,hi⟩ := paths_range L.tiles L.work L.first paths g hg
    rw [count] at hi
    omega
  let built := ProtocolRAMPurchaseGateColumns.output L.candidates L.depth L.source L.directory L.work L.tape mem
  let init := MarkTape.loaded L.tiles L.work L.first L.candidates L.marks built
  calc
    MarkTape.eval gates init a = init a := MarkTape.frame gates init a away
    _ = built a := ProtocolRAMGeneratedWrite.frame_image L.work (4+L.tiles+L.first+L.candidates)
      (MarkTape.loadTerm L.tiles L.marks) built a (by omega)
    _ = mem a := GateColumns.frame _ L.source L.directory L.work L.tape mem a tape

private theorem framed_cells (L : ProtocolRAMPurchaseAllocation.Layout) (ct : CT)
    (threshold : Bank) (stock : Fin (2*k) → Bank) (j : Fin (2*k))
    {G : Type*} (p : Tiles (Fin L.rows) G L.sockets) (enc : G ↪ Fin L.groups)
    (rows : Fin L.candidates → Fin (L.height+1) → Fin (L.rows+1))
    (mem : Memory w) (a : ℕ) (away : a<L.signed.base ∨ (L.gates.base≤a ∧ a<L.packed) ∨ L.endAddress≤a) :
    PurchaseStage.dispatchMemory L.dispatchLayout rows
      (PurchaseTape.signedOut (L.plan ct) (L.signedInputs threshold stock) j p enc L.height mem) a=mem a := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ := L.regions
  let s := L.plan ct
  let b := L.signedInputs threshold stock
  let own := ProtocolRAMPurchaseOwners.image L.scratch s.columns p enc mem
  let exprs := List.ofFn (PurchaseColumns.field L.directory L.rows L.height (PurchaseTape.edge s))
  let afterRows := result (ProbeStage.Native.columns L.candidates L.source.base exprs) own
  let marked := PurchaseTape.signedOut s b j p enc L.height mem
  have capOwner : L.groups*L.sockets≤L.owner.size := (ProtocolRAMPurchaseSampler.lt_span _).le
  have capRows : (L.height+1)*L.candidates≤L.source.size := (ProtocolRAMPurchaseSampler.lt_span _).le
  have exprLen : exprs.length=L.height+1 := List.length_ofFn
  have ownerFrame : own a=mem a := ProtocolRAMPurchaseOwners.frame L.scratch s.columns p enc mem a
    (by change a<L.owner.base ∨ L.owner.base+L.groups*L.sockets≤a; omega) (by omega)
  have sourceFrame : afterRows a=own a := ProbeStage.Native.columns_frame exprs own (by rw [exprLen]; omega)
  have marksCap := L.signed_capacity
  have markFrame : marked a=afterRows a := ProtocolRAMGeneratedWrite.frame_image L.signed.base
    (L.rows+1) (PurchaseMarks.markExpr L.rows threshold stock j) afterRows a (by omega)
  have tail : PurchaseStage.dispatchMemory L.dispatchLayout rows marked a=marked a :=
    dispatch_frame L.dispatchLayout rows marked a
      (by change a<L.packed ∨ L.packed+3*L.gatesCount≤a; omega)
      (by change a<L.work ∨ L.work+4+(L.rows+1)+L.first+L.candidates≤a; omega)
  exact ((tail.trans markFrame).trans sourceFrame).trans ownerFrame

/-- All writes, from owner generation through the greedy interpreter, lie within the slab. -/
theorem block_frame (L : ProtocolRAMPurchaseAllocation.Layout) (ct : CT)
    (threshold : Bank) (stock : Fin (2*k) → Bank) (j : Fin (2*k))
    {G : Type*} (p : Tiles (Fin L.rows) G L.sockets) (enc : G ↪ Fin L.groups)
    (rows : Fin L.candidates → Fin (L.height+1) → Fin (L.rows+1))
    (mem : Memory w) (a : ℕ) (away : a<L.start ∨ L.endAddress≤a) :
    PurchaseStage.dispatchMemory L.dispatchLayout rows
      (PurchaseTape.signedOut (L.plan ct) (L.signedInputs threshold stock) j p enc L.height mem) a=mem a := by
  apply framed_cells L ct threshold stock j p enc rows mem a
  have start := L.regions.start
  have ids := L.regions.ids
  omega

/-- The sampler, reverse digits and DFS table preceding the signed bank, and the
six gate-shape columns between the path bank and the packed tape, are immutable. -/
theorem block_static (L : ProtocolRAMPurchaseAllocation.Layout) (ct : CT)
    (threshold : Bank) (stock : Fin (2*k) → Bank) (j : Fin (2*k))
    {G : Type*} (p : Tiles (Fin L.rows) G L.sockets) (enc : G ↪ Fin L.groups)
    (rows : Fin L.candidates → Fin (L.height+1) → Fin (L.rows+1))
    (mem : Memory w) (a : ℕ) (place : (L.start≤a ∧ a<L.signed.base) ∨ (L.gates.base≤a ∧ a<L.packed)) :
    PurchaseStage.dispatchMemory L.dispatchLayout rows
      (PurchaseTape.signedOut (L.plan ct) (L.signedInputs threshold stock) j p enc L.height mem) a=mem a := by
  apply framed_cells L ct threshold stock j p enc rows mem a
  omega

private theorem source_before_gates (L : ProtocolRAMPurchaseAllocation.Layout)
    (j : Fin (L.height+1)) (r : Fin L.candidates) :
    L.source.base+(j.val*L.candidates+r.val)<L.gates.base := by
  have cap : (L.height+1)*L.candidates≤L.source.size := (ProtocolRAMPurchaseSampler.lt_span _).le
  have mul := Nat.mul_le_mul_right L.candidates j.isLt
  rw [Nat.succ_mul] at mul
  have row := r.isLt
  have region := L.regions.source
  omega

theorem source_range (L : ProtocolRAMPurchaseAllocation.Layout) (i : Fin L.candidates) (j : Fin (L.height+1)) :
    L.start≤L.source.base+(j.val*L.candidates+i.val) ∧
      L.source.base+(j.val*L.candidates+i.val)<L.endAddress := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ := L.regions
  have upper := source_before_gates L j i
  omega

/-- Dispatch compiles the NAND tape after the source and only mutates its own
workspace, so every materialized candidate row remains readable. -/
theorem dispatch_rows (L : ProtocolRAMPurchaseAllocation.Layout)
    (rows : Fin L.candidates → Fin (L.height+1) → Fin (L.rows+1)) (mid : Memory w)
    (bits : ProtocolRAMPurchaseGateColumns.TileRows L.source rows mid) :
    ProtocolRAMPurchaseGateColumns.TileRows L.source rows
      (PurchaseStage.dispatchMemory L.dispatchLayout rows mid) := by
  intro r j
  let a := L.source.base+(j.val*L.candidates+r.val)
  have early : a<L.gates.base := source_before_gates L j r
  have rom := L.regions.gateROM
  have tape := L.regions.tape
  exact (dispatch_frame L.dispatchLayout rows mid a
    (.inl (by change a<L.packed; omega)) (.inl (by change a<L.work; omega))).trans (bits r j)


end Hierarchy.ProtocolRAMPurchaseAllocation.Layout

end OAI
