import OAI.Computability.VPVNP.PairSimulationVertexJobs
import OAI.Computability.VPVNP.PairPendingArguments
import OAI.Computability.VPVNP.PairTraversalDisjoint

/-!
# Half-wire packets in the selected vertex traversal

At a visit the input packet names the current row and contains its actual
outgoing and incoming half-wire bits. Its children receive the old halves
chosen by this occurrence, in placement-fiber order. Running the resulting
jobs in preorder consumes the root and preserves every pending suffix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open NetworkKernel Compression NodeArguments
open scoped Fin.CommRing

variable {L : Type}

/-- A visit guesses all child half-wires before reading the local kernel bits.
At a cursor leaf, the local bits are the original validator's private choices. -/
structure TypedVertexJob (L : Type) where
  /-- The pending input packet consumed by this typed vertex job. -/
  input : Packet
  /-- Child argument packets produced by the job in the order expected by the DFS traversal. -/
  children : List Packet
  /-- Additional choice bits consumed locally by this job after its children's argument fields. -/
  localBits : List Bool
  /-- Histogram increment per parameter label contributed by this typed vertex job. -/
  increment : L → ℕ

/-- Erase the packet types to a plain vertex job while preserving the input node, concatenated
child and local bits, and label increments. -/
def TypedVertexJob.erase (j : TypedVertexJob L) : VertexJob L where
  address := j.input.node
  bits := j.children.flatMap Packet.bits ++ j.localBits
  increment := j.increment

/-- Consume the packet at the head of the frontier and prepend that visit's
child packets. Equality of packets includes every bit of the old half-wires. -/
inductive PacketVisits {L : Type} : List Packet → List (TypedVertexJob L) → List Packet → Prop
  | nil (pending) : PacketVisits pending [] pending
  | cons (j : TypedVertexJob L) {rest jobs final}
      (tail : PacketVisits (j.children ++ rest) jobs final) :
    PacketVisits (j.input :: rest) (j :: jobs) final

theorem PacketVisits.append {u v w : List Packet} {xs ys : List (TypedVertexJob L)}
    (h : PacketVisits u xs v) (g : PacketVisits v ys w) : PacketVisits u (xs ++ ys) w := by
  induction h with
  | nil => exact g
  | cons j _ ih => exact .cons j (ih g)

private theorem PacketVisits.forest {I : Type} (indices : List I) (packet : I → Packet)
    (run : I → List (TypedVertexJob L))
    (h : ∀ i rest, PacketVisits (packet i :: rest) (run i) rest) (suffix : List Packet) :
    PacketVisits (indices.map packet ++ suffix) (indices.flatMap run) suffix := by
  induction indices with
  | nil => exact .nil _
  | cons i rest ih => exact (h i _).append ih

/-- Every currently pending packet occurs in order among the unvisited jobs
and the untouched final suffix. -/
theorem PacketVisits.pending_sublist {pending final : List Packet} {jobs : List (TypedVertexJob L)}
    (h : PacketVisits pending jobs final) :
    pending.Sublist (jobs.map TypedVertexJob.input ++ final) := by
  induction h with
  | nil => exact List.Sublist.refl _
  | @cons j rest jobs final tail ih =>
    exact .cons_cons _ ((List.sublist_append_right j.children rest).trans ih)

/-- Readiness of the typed inputs before the corresponding native updates. -/
def StoredVisits {w endAddr : ℕ} (A : Arena)
    (update : TypedVertexJob L → DFS.Scratch w endAddr → DFS.Scratch w endAddr) :
    List (TypedVertexJob L) → DFS.Scratch w endAddr → Prop
  | [], _ => True
  | j :: js, s => j.input.Stored A s ∧ StoredVisits A update js (update j s)

/-- A hook may change any other private cells. Its updates agree with the
child writes precisely on the intervals that are live after each visit. -/
def PacketVisits.WritesAgree {w endAddr : ℕ} (A : Arena)
    (update : TypedVertexJob L → DFS.Scratch w endAddr → DFS.Scratch w endAddr)
    {pending final : List Packet} {jobs : List (TypedVertexJob L)}
    (h : PacketVisits pending jobs final) (s : DFS.Scratch w endAddr) : Prop :=
  match jobs, pending with
  | [], _ => True
  | j :: js, _ :: rest =>
    (∀ q ∈ j.children ++ rest, ∀ i : Fin q.bits.length,
      rawScratch (update j s) ((A.base q.node + i.val : ℕ) : BurstRAM.Word w) =
        rawScratch (writePackets A j.children s) ((A.base q.node + i.val : ℕ) : BurstRAM.Word w)) ∧
      @WritesAgree w endAddr A update (j.children ++ rest) final js
        (by cases h with | cons _ tail => exact tail) (update j s)
  | _ :: _, [] => False

/-- The native update reads the exact input at every job and preserves the
stored values of all pending siblings, including the final suffix. -/
theorem PacketVisits.preparedAlong {pending final : List Packet} {jobs : List (TypedVertexJob L)}
    {w endAddr : ℕ} (h : PacketVisits pending jobs final) (A : Arena)
    (update : TypedVertexJob L → DFS.Scratch w endAddr → DFS.Scratch w endAddr)
    (s : DFS.Scratch w endAddr) (format : Packet → Prop)
    (hf : ∀ q ∈ jobs.map TypedVertexJob.input ++ final, format q ∧ q.Fits A w endAddr)
    (hn : ((jobs.map TypedVertexJob.input ++ final).map Packet.node).Nodup)
    (hs : PreparedPackets A format pending s) (ha : h.WritesAgree A update s) :
    StoredVisits A update jobs s ∧
      PreparedPackets A format final (jobs.foldl (fun old j => update j old) s) := by
  induction h generalizing s with
  | nil => exact ⟨trivial, hs⟩
  | @cons j rest jobs final tail ih =>
    have fit := fun q (hq : q ∈ jobs.map TypedVertexJob.input ++ final) =>
      hf q (List.mem_cons_of_mem _ hq)
    have nd := (List.nodup_cons.mp hn).2
    have front := tail.pending_sublist
    have childFit (q : Packet) (hq : q ∈ j.children) :=
      fit q (front.subset (List.mem_append_left _ hq))
    have next := preparedPackets_push A format j.input j.children rest s (update j s)
      hs childFit ((front.map Packet.node).nodup nd) ha.1
    obtain ⟨steps, last⟩ := ih (update j s) fit nd next ha.2
    exact ⟨⟨(hs.2 _ List.mem_cons_self).2.2, steps⟩, last⟩

variable {A : Type*} [CommRing A] [Fintype L] {κ : L → A} {N Y : Network}

/-- Encode one old vertex's half-wires in the term parser's slot order. -/
noncomputable def TermParsers.halfBits {t : Term A N} (r : TermParsers κ t) (u : N.Site)
    (z : N.Half u) : List Bool :=
  (half N u (r.order.outgoing u) (r.order.incoming u) r.payload).encode z

/-- A packet for each old site in this particular placement fiber. The halves
in the packet are those selected by this visit's placed assignment. -/
noncomputable def TermParsers.childPackets {t : Term A N} (r : TermParsers κ t)
    (previous : N.Site → ℕ) (v : t.output.Site) (a : Placed t.place N.Half v) : List Packet :=
  List.ofFn fun j => let u := (r.order.children v).entries j
    ⟨previous u.val, r.halfBits u.val (a u.val u.prop)⟩

theorem TermParsers.childPackets_nodes {t : Term A N} (r : TermParsers κ t)
    (previous : N.Site → ℕ) (v : t.output.Site) (a : Placed t.place N.Half v) :
    (r.childPackets previous v a).map Packet.node =
      List.ofFn fun j => previous ((r.order.children v).entries j).val := by
  simp [TermParsers.childPackets, Function.comp_def]

/-- For a state-indexed term parser this is the private arena's outgoing-then-
incoming bit layout, with each incoming width taken at its matched source. -/
theorem TermParsers.childPackets_state {d g : ℕ} (X : State d g) {t : Term A X.network}
    (r : TermParsers κ t) (hp : r.payload = statePayload X)
    (ho : ∀ u, r.order.outgoing u = outgoingOrder X u)
    (hi : ∀ u, r.order.incoming u = incomingOrder X u)
    (previous : X.network.Site → ℕ) (v : t.output.Site) (a : Placed t.place X.network.Half v) :
    r.childPackets previous v a = List.ofFn fun j =>
      let u := (r.order.children v).entries j
      ⟨previous u.val, packed X u.val (a u.val u.prop)⟩ := by
  unfold childPackets
  congr 1
  funext j
  simp only [halfBits, hp, ho, hi, packed_eq_encode]

open private fiber_encode from OAI.Computability.VPVNP.PairNodeArguments

theorem TermParsers.nodeBits_eq_childPackets {t : Term A N} (r : TermParsers κ t)
    (previous : N.Site → ℕ) (v : t.output.Site) (a : Placed t.place N.Half v)
    (z : t.output.Half v) (x : (r.witness v a z).Choice) :
    r.nodeBits v a z x =
      (r.childPackets previous v a).flatMap Packet.bits ++ (r.read v a z).encode x := by
  rw [TermParsers.nodeBits, fiber_encode]
  simp [childPackets, halfBits, List.flatMap_def, Function.comp_def]

/-- The supplied bits at the root of a subtree come from the parent or from the
shared final wires. All internal packets are constructed from the selected halves. -/
abbrev TypedJobsFor (P : SiteParsers κ N) :=
  ∀ v z, List Bool → (P.witnesses v z).Choice → List (TypedVertexJob L)

private def typedLeafJobs (P : SiteParsers κ N) (ptr : N.Site → ℕ × ℕ) : TypedJobsFor P :=
  fun v z input p =>
    [⟨⟨(ptr v).1, input⟩, [], (P.read v z).encode p, (P.witnesses v z).exponents p⟩]

private noncomputable def typedPushJobs {t : Term A N} (r : TermParsers κ t)
    (previous : N.Site → ℕ) (ptr : t.output.Site → ℕ × ℕ)
    (P : SiteParsers κ N) (jobs : TypedJobsFor P) : TypedJobsFor (r.push P) :=
  fun v z input p =>
    let q := t.pushChoice P.factors P.witnesses r.witness v z p
    ⟨⟨(ptr v).1, input⟩, r.childPackets previous v q.1, (r.read v q.1 z).encode q.2.2,
      (r.witness v q.1 z).exponents q.2.2⟩ ::
      (List.ofFn fun j => let u := (r.order.children v).entries j
        let h := q.1 u.val u.prop
        jobs u.val h (r.halfBits u.val h) (q.2.1 u)).flatten

private structure TypedJobsSpec (P : SiteParsers κ N) (addr : N.Site → ℕ)
    (typed : TypedJobsFor P) (jobs : JobsFor P) : Prop where
  erases : ∀ v z input p, (typed v z input p).map TypedVertexJob.erase = jobs v z p
  visits : ∀ v z input p suffix, PacketVisits (⟨addr v, input⟩ :: suffix) (typed v z input p) suffix

private theorem typedLeafJobs_spec (P : SiteParsers κ N) (ptr : N.Site → ℕ × ℕ) :
    TypedJobsSpec P (fun v => (ptr v).1) (typedLeafJobs P ptr) (leafJobs P ptr) where
  erases _ _ _ _ := rfl
  visits v z input p suffix :=
    .cons ⟨⟨(ptr v).1, input⟩, [], (P.read v z).encode p, (P.witnesses v z).exponents p⟩
      (.nil suffix)

private theorem typedPushJobs_spec {t : Term A N} (r : TermParsers κ t)
    (previous : N.Site → ℕ) (ptr : t.output.Site → ℕ × ℕ) (P : SiteParsers κ N)
    (typed : TypedJobsFor P) (jobs : JobsFor P) (h : TypedJobsSpec P previous typed jobs) :
    TypedJobsSpec (r.push P) (fun v => (ptr v).1) (typedPushJobs r previous ptr P typed)
      (pushJobs r ptr P jobs) where
  erases v z input p := by
    simp only [typedPushJobs, pushJobs, List.map_cons, TypedVertexJob.erase,
      ← r.nodeBits_eq_childPackets previous, List.map_flatten, List.map_ofFn, Function.comp_def,
      h.erases]
  visits v z input p suffix := by
    let q := t.pushChoice P.factors P.witnesses r.witness v z p
    let u := (r.order.children v).entries
    let packet : Fin (r.order.children v).length → Packet := fun j =>
      ⟨previous (u j).val, r.halfBits (u j).val (q.1 (u j).val (u j).prop)⟩
    let run := fun j => typed (u j).val (q.1 (u j).val (u j).prop) (packet j).bits (q.2.1 (u j))
    apply PacketVisits.cons ⟨⟨(ptr v).1, input⟩, List.ofFn packet, (r.read v q.1 z).encode q.2.2,
      (r.witness v q.1 z).exponents q.2.2⟩
    have result := PacketVisits.forest (List.ofFn id) packet run
      (fun j rest => h.visits (u j).val _ _ _ rest) suffix
    simpa only [List.flatMap_def, List.map_ofFn, Function.comp_id] using result

private noncomputable def chainTypedJobs (c : TermChain A N Y) (r : ChainParsers κ c)
    (ptr : RowPointers c) (P : SiteParsers κ N) (addr : N.Site → ℕ) (typed : TypedJobsFor P) :
    TypedJobsFor (finalParsers c r P) := by
  induction c with
  | done => exact typed
  | more _ _ _ ih =>
    exact ih r.2 ptr.2 (r.1.push P) (fun v => (ptr.1 v).1) (typedPushJobs r.1 addr ptr.1 P typed)

/-- Addresses of the last selected rows, including the zero-step case. -/
def lastRowAddresses {N Y : Network} (c : TermChain A N Y) (ptr : RowPointers c)
    (initial : N.Site → ℕ) : Y.Site → ℕ :=
  match c with
  | .done _ => initial
  | .more _ _ tail => lastRowAddresses tail ptr.2 (fun v => (ptr.1 v).1)

private theorem chainTypedJobs_spec (c : TermChain A N Y) (r : ChainParsers κ c)
    (ptr : RowPointers c) (P : SiteParsers κ N) (addr : N.Site → ℕ)
    (typed : TypedJobsFor P) (jobs : JobsFor P) (h : TypedJobsSpec P addr typed jobs) :
    TypedJobsSpec (finalParsers c r P) (lastRowAddresses c ptr addr)
      (chainTypedJobs c r ptr P addr typed) (chainJobs c r ptr P jobs) := by
  induction c with
  | done => exact h
  | more _ _ _ ih => exact ih r.2 ptr.2 _ _ _ _ (typedPushJobs_spec r.1 addr ptr.1 P typed jobs h)

/-- Construct the selected branch's typed vertex jobs by composing the cursor leaf jobs with
all scheduled term layers and their row pointers. -/
noncomputable def typedVertexJobs (c : TermChain A N Y) (r : ChainParsers κ c)
    (ptr : RowPointers c) (P : SiteParsers κ N) (leaves : N.Site → ℕ × ℕ) :
    TypedJobsFor (finalParsers c r P) :=
  chainTypedJobs c r ptr P (fun u => (leaves u).1) (typedLeafJobs P leaves)

theorem typedVertexJobs_erases (c : TermChain A N Y) (r : ChainParsers κ c)
    (ptr : RowPointers c) (P : SiteParsers κ N) (leaves : N.Site → ℕ × ℕ) (v z input p) :
    (typedVertexJobs c r ptr P leaves v z input p).map TypedVertexJob.erase =
      vertexJobs c r ptr P leaves v z p :=
  (chainTypedJobs_spec c r ptr P _ _ _ (typedLeafJobs_spec P leaves)).erases v z input p

theorem typedVertexJobs_visits (c : TermChain A N Y) (r : ChainParsers κ c)
    (ptr : RowPointers c) (P : SiteParsers κ N) (leaves : N.Site → ℕ × ℕ) (v z input p suffix) :
    PacketVisits (⟨lastRowAddresses c ptr (fun u => (leaves u).1) v, input⟩ :: suffix)
      (typedVertexJobs c r ptr P leaves v z input p) suffix :=
  (chainTypedJobs_spec c r ptr P _ _ _ (typedLeafJobs_spec P leaves)).visits v z input p suffix

theorem typedVertexJobs_addresses (c : TermChain A N Y) (r : ChainParsers κ c)
    (ptr : RowPointers c) (P : SiteParsers κ N) (leaves : N.Site → ℕ × ℕ) (v z input p) :
    (typedVertexJobs c r ptr P leaves v z input p).map (fun j => j.input.node) =
      (chainTrees c r ptr (fun u => leafTree (leaves u)) v).preorder := by
  have h := (vertexJobs_spec c r ptr P leaves).addresses v z p
  rw [← typedVertexJobs_erases c r ptr P leaves v z input p, List.map_map] at h
  exact h

open private addTree from OAI.Computability.VPVNP.PairTraversalHistory

theorem lastRowAddresses_eq_address (c : TermChain A N Y) (r : ChainParsers κ c)
    (ptr : RowPointers c) (trees : N.Site → DFS.VertexTree) (v : Y.Site) :
    lastRowAddresses c ptr (fun u => (trees u).address) v =
      (chainTrees c r ptr trees v).address := by
  induction c with
  | done => rfl
  | more _ _ _ ih => exact ih r.2 ptr.2 (addTree r.1 ptr.1 trees) v

/-- With the actual stage-row addresses the native readiness theorem needs
only disjointness from the externally supplied suffix. Within the selected
tree all row addresses are distinct by the placement partition. -/
theorem selectedTypedJobs_prepared {k : Type*} [Field k] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f) {lanes : ℕ}
    (T : ℕ) (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute f hf T hT X).Choices) (base : ℕ) (P : SiteParsers f X.network) :
    let E := B.execute f hf T hT X
    let data := B.records f hf T hT X
    let c := E.termChain data z
    let r := selectedParsers B f hf T hT X z
    let ptr := TraversalRows.chainPointers B.recordLimit c (branchOrders E data z)
      (TraversalRows.address B.recordLimit base (siteOrder X).length)
    let leaves := TraversalRows.sitePointers B.recordLimit base (siteOrder X)
    ∀ v h, let bytes := packed (E.finalState z) v h
      let tree := chainTrees c r ptr (fun u => leafTree (leaves u)) v
      ∀ (p : ((finalParsers c r P).witnesses v h).Choice) (suffix : List Packet),
        let jobs := typedVertexJobs c r ptr P leaves v h bytes p
        let run := typedVertexJobs_visits c r ptr P leaves v h bytes p suffix
        ∀ {w endAddr : ℕ} (A : Arena)
          (update : TypedVertexJob B.Entry → DFS.Scratch w endAddr → DFS.Scratch w endAddr)
          (s : DFS.Scratch w endAddr) (format : Packet → Prop),
          List.Disjoint tree.preorder (suffix.map Packet.node) →
          (∀ q ∈ jobs.map TypedVertexJob.input ++ suffix, format q ∧ q.Fits A w endAddr) →
          PreparedPackets A format (⟨tree.address, bytes⟩ :: suffix) s →
          run.WritesAgree A update s →
          StoredVisits A update jobs s ∧
            PreparedPackets A format suffix (jobs.foldl (fun old j => update j old) s) := by
  intro E data c r ptr leaves v h bytes tree p suffix jobs run w endAddr arena update s fmt
    hd hv hs ha
  have same := lastRowAddresses_eq_address c r ptr (fun u => leafTree (leaves u)) v
  change lastRowAddresses c ptr (fun u => (leaves u).1) v = tree.address at same
  rw [← same] at hs
  apply run.preparedAlong arena update s fmt hv _ hs ha
  rw [List.map_append, List.map_map]
  change (jobs.map (fun j => j.input.node) ++ suffix.map Packet.node).Nodup
  rw [typedVertexJobs_addresses]
  exact ((TraversalRows.selected_preorders B f hf T hT X z base).1 v).append
    (List.nodup_cons.mp hs.1).2 hd

section Cursor

open CursorNetwork CursorRouting BurstRAM BurstRAM.PrivateRAM

variable {k : Type*} [Field k] {S : BlockSchedule k} {D e w p r k' base lanes : ℕ} [NeZero D]
    (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
    (M : Machine w p r k') (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w)
    (labels : Fin D ≃ Fin base ⊕ Fin lanes) (hD : 1 < D)
    (T : ℕ) (hT : T * S.laneBits ≤ lanes)

/-- The final network supplies one common payload per edge. Each final
site starts with its actual packed halves, and thereafter each child uses
exactly the old halves its own parent guessed. -/
theorem selectedCursor_typedJobs :
    let hpad := Nat.add_sub_of_le S.degree_bounds.1
    let X := cursorState labels hD hpad (ramFieldBits (2 ^ e) w : RAMSystem D → ℕ)
    let E := B.execute f hf T hT X
    let P := cursorSiteParsers M fuel initial header hw hc labels hD hpad f
    ∀ z : E.Choices, let c := E.termChain (B.records f hf T hT X) z
      let r := selectedParsers B f hf T hT X z
      let Y := E.finalState z
      ∀ (ptr : RowPointers c) (leaves : X.network.Site → ℕ × ℕ)
        (edges : ∀ e : Y.network.Edge, Y.network.Payload e) (v : Y.network.Site),
        let h := WireTensor.edgeAssignment Y.network.src Y.network.dst edges v
        let bytes := packed Y v h
        let tree := chainTrees c r ptr (fun u => leafTree (leaves u)) v
        ∀ p : ((finalParsers c r P).witnesses v h).Choice,
          let jobs := typedVertexJobs c r ptr P leaves v h bytes p
          jobs.map TypedVertexJob.erase = vertexJobs c r ptr P leaves v h p ∧
            ∀ suffix, PacketVisits (⟨tree.address, bytes⟩ :: suffix) jobs suffix := by
  intro hpad X E P z c r Y ptr leaves edges v h bytes tree p jobs
  refine ⟨typedVertexJobs_erases c r ptr P leaves v h bytes p, fun suffix => ?_⟩
  rw [← lastRowAddresses_eq_address c r ptr (fun u => leafTree (leaves u)) v]
  exact typedVertexJobs_visits c r ptr P leaves v h bytes p suffix

end Cursor
end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
