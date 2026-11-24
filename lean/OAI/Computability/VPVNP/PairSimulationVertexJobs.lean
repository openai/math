import OAI.Computability.VPVNP.PairTraversalHistory
import OAI.Computability.VPVNP.PairSimulationDFSHooks

/-!
# Local choices and exponent increments in DFS visit order

For a fixed final vertex and a choice in its expansion, each descriptor
visit consumes the old half-wire choices and the local kernel choices
once. Its children then use those very half-wires. Splitting the binary
stream this way aligns the row addresses with native depth-first traversal
and the local parameter increments with the final vertex's monomial.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open NetworkKernel CompressorRecords Compression DFS
open scoped Classical
open private addTree from OAI.Computability.VPVNP.PairTraversalHistory

variable {A : Type*} [CommRing A] {L : Type} [Fintype L] {κ : L → A} {N Y : Network}

/-- One depth-first descriptor visit, carrying its row address, the local witness tape it
consumes, and its contribution to each parameter exponent. -/
structure VertexJob (L : Type) where
  /-- Address of the descriptor row visited by this job. -/
  address : ℕ
  /-- The segment of the vertex choice stream consumed at this descriptor visit. -/
  bits : List Bool
  /-- The contribution of this visit's local witness to the exponent of each parameter label. -/
  increment : L → ℕ

/-- Per-site jobs indexed by the incoming half-wires and the selected
local monomial occurrence. -/
abbrev JobsFor (P : SiteParsers κ N) :=
  ∀ v z, (P.witnesses v z).Choice → List (VertexJob L)

private theorem order_encode {I : Type} (o : Order I) {α : I → Type} (read : ∀ i, ChoiceReader (α i))
    (x : ∀ i, α i) : ((o.reader read).encode x) = (List.ofFn fun j => (read (o.entries j)).encode (x (o.entries j))).flatten := by
  unfold Order.reader ChoiceReader.reindex
  dsimp only
  rw [ChoiceReader.vector_encode]
  rfl

/-- The old halves of every child and the local kernel assignment in the
same order in which the push reader consumes them. -/
noncomputable def TermParsers.nodeBits {t : Term A N} (r : TermParsers κ t) (v : t.output.Site)
    (a : Placed t.place N.Half v) (z : t.output.Half v) (x : (r.witness v a z).Choice) : List Bool :=
  (fiber t.place v (r.order.children v) (fun u => half N u (r.order.outgoing u) (r.order.incoming u) r.payload)).encode a ++
    (r.read v a z).encode x

private theorem push_encode {t : Term A N} (r : TermParsers κ t) (P : SiteParsers κ N)
    (v : t.output.Site) (z : t.output.Half v) (x : ((r.push P).witnesses v z).Choice) :
    let q := t.pushChoice P.factors P.witnesses r.witness v z x
    let o := r.order.children v
    ((r.push P).read v z).encode x = r.nodeBits v q.1 z q.2.2 ++
      (List.ofFn fun j => let u := o.entries j; (P.read u.val (q.1 u.val u.prop)).encode (q.2.1 u)).flatten := by
  intro q o
  change _ ++ (_ ++ (o.reader (fun u => P.read u.val (q.1 u.val u.prop))).encode q.2.1) = (_ ++ _) ++ _
  rw [order_encode, List.append_assoc]
  rfl

/-- Each input vertex makes one visit. Its job carries precisely the
factor witness supplied by that input parser. -/
def leafJobs (P : SiteParsers κ N) (ptr : N.Site → ℕ × ℕ) : JobsFor P :=
  fun v z p => [⟨(ptr v).1, (P.read v z).encode p, (P.witnesses v z).exponents p⟩]

/-- Build the pushed site's jobs by emitting its own descriptor visit first, then the chosen
child jobs in the term parser's child order. -/
noncomputable def pushJobs {t : Term A N} (r : TermParsers κ t) (ptr : t.output.Site → ℕ × ℕ)
    (P : SiteParsers κ N) (jobs : JobsFor P) : JobsFor (r.push P) :=
  fun v z p =>
    let q := t.pushChoice P.factors P.witnesses r.witness v z p
    let children := r.order.children v
    ⟨(ptr v).1, r.nodeBits v q.1 z q.2.2, (r.witness v q.1 z).exponents q.2.2⟩ ::
      (List.ofFn fun j => let u := children.entries j; jobs u.val (q.1 u.val u.prop) (q.2.1 u)).flatten

/-- Agreement of a site's jobs with its tree and parser. The addresses follow preorder, the
concatenated tapes encode the witness, and the increments sum to its exponents. -/
structure JobsSpec (P : SiteParsers κ N) (trees : N.Site → VertexTree) (jobs : JobsFor P) : Prop where
  addresses : ∀ v z p, (jobs v z p).map VertexJob.address = (trees v).preorder
  bits : ∀ v z p, (jobs v z p).flatMap VertexJob.bits = (P.read v z).encode p
  increments : ∀ v z p l, ((jobs v z p).map (fun j => j.increment l)).sum = (P.witnesses v z).exponents p l

private theorem leafJobs_spec (P : SiteParsers κ N) (ptr : N.Site → ℕ × ℕ) :
    JobsSpec P (fun v => leafTree (ptr v)) (leafJobs P ptr) where
  addresses v z p := rfl
  bits v z p := by simp [leafJobs]
  increments v z p l := by simp [leafJobs]

private theorem flatten_flatMap_eq {I J : Type} (ls : List (List I)) (f : I → List J) :
    ls.flatten.flatMap f = (ls.map fun xs => xs.flatMap f).flatten := by
  induction ls with
  | nil => rfl
  | cons xs ls ih => simp [List.flatMap_append, ih]

private theorem pushJobs_spec {t : Term A N} (r : TermParsers κ t) (ptr : t.output.Site → ℕ × ℕ)
    (P : SiteParsers κ N) (trees : N.Site → VertexTree) (jobs : JobsFor P) (h : JobsSpec P trees jobs) :
    JobsSpec (r.push P) (addTree r ptr trees) (pushJobs r ptr P jobs) where
  addresses v z p := by
    simp only [pushJobs, List.map_cons, List.map_flatten, List.map_ofFn, Function.comp_def, h.addresses,
      addTree, VertexTree.preorder]
  bits v z p := by
    rw [push_encode]
    simp only [pushJobs, List.flatMap_cons, flatten_flatMap_eq, List.map_ofFn, Function.comp_def, h.bits]
  increments v z p l := by
    let q := t.pushChoice P.factors P.witnesses r.witness v z p
    let o := r.order.children v
    simp only [pushJobs, List.map_cons, List.sum_cons, List.map_flatten, List.map_ofFn, List.sum_flatten,
      Function.comp_def, List.sum_ofFn, h.increments]
    change (r.witness v q.1 z).exponents q.2.2 l + (∑ j, (P.witnesses (o.entries j).val
      (q.1 (o.entries j).val (o.entries j).prop)).exponents (q.2.1 (o.entries j)) l) =
      (∑ u : t.Preimage v, (P.witnesses u.val (q.1 u.val u.prop)).exponents (q.2.1 u) l) + _
    rw [Nat.add_comm]
    exact congrArg (· + _) (o.entries.sum_comp (fun u => (P.witnesses u.val (q.1 u.val u.prop)).exponents (q.2.1 u) l))

/-- Follow the selected terms, retaining the local split into descriptor
visits at every stage. -/
noncomputable def chainJobs {N Y : Network} (c : TermChain A N Y) (r : ChainParsers κ c)
    (ptr : RowPointers c) (P : SiteParsers κ N) (jobs : JobsFor P) : JobsFor (finalParsers c r P) := by
  induction c with
  | done => exact jobs
  | more _ _ _ ih => exact ih r.2 ptr.2 (r.1.push P) (pushJobs r.1 ptr.1 P jobs)

private theorem chainJobs_spec (c : TermChain A N Y) (r : ChainParsers κ c) (ptr : RowPointers c)
    (P : SiteParsers κ N) (trees : N.Site → VertexTree) (jobs : JobsFor P) (h : JobsSpec P trees jobs) :
    JobsSpec (finalParsers c r P) (chainTrees c r ptr trees) (chainJobs c r ptr P jobs) := by
  induction c with
  | done => exact h
  | more _ _ _ ih => exact ih r.2 ptr.2 _ _ _ (pushJobs_spec r.1 ptr.1 P trees jobs h)

/-- Jobs for each final site of a selected term chain, obtained by starting with one visit per
input leaf and applying the successive term parsers. -/
noncomputable def vertexJobs (c : TermChain A N Y) (r : ChainParsers κ c) (ptr : RowPointers c)
    (P : SiteParsers κ N) (leaves : N.Site → ℕ × ℕ) : JobsFor (finalParsers c r P) :=
  chainJobs c r ptr P (leafJobs P leaves)

theorem vertexJobs_spec (c : TermChain A N Y) (r : ChainParsers κ c) (ptr : RowPointers c)
    (P : SiteParsers κ N) (leaves : N.Site → ℕ × ℕ) :
    JobsSpec (finalParsers c r P) (chainTrees c r ptr (fun v => leafTree (leaves v))) (vertexJobs c r ptr P leaves) :=
  chainJobs_spec c r ptr P _ _ (leafJobs_spec P leaves)

section Cursor

open CursorNetwork CursorRouting BurstRAM BurstRAM.PrivateRAM

variable {k : Type*} [Field k] {S : BlockSchedule k} {D e w p r k' base lanes : ℕ} [NeZero D]
    (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
    (M : Machine w p r k') (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2^D * 2^e < 2^w) (labels : Fin D ≃ Fin base ⊕ Fin lanes) (hD : 1 < D)
    (T : ℕ) (hT : T * S.laneBits ≤ lanes)

/-- The selected cursor leaves consume their validator strings and add zero
to every parameter count. -/
theorem cursor_leafJobs (hd : 2 + (S.baseDegree - 2) = 2 ^ S.degreeExponent 0)
    (leaves : (cursorState labels hD hd (ramFieldBits (2^e) w : RAMSystem D → ℕ)).network.Site → ℕ × ℕ) :
    let P := cursorSiteParsers M fuel initial header hw hc labels hD hd f
    ∀ v z p, leafJobs P leaves v z p = [⟨(leaves v).1, (P.read v z).encode p, fun _ => 0⟩] := fun _ _ _ => rfl

/-- The visit lists for the original machine specialize all three
identities to the compressor's actual records and branch choice. -/
theorem selectedCursor_jobs :
    let hpad := Nat.add_sub_of_le S.degree_bounds.1
    let X := cursorState labels hD hpad (ramFieldBits (2^e) w : RAMSystem D → ℕ)
    let E := B.execute f hf T hT X
    let P := cursorSiteParsers M fuel initial header hw hc labels hD hpad f
    ∀ z : E.Choices, let c := E.termChain (B.records f hf T hT X) z
      let r := selectedParsers B f hf T hT X z
      ∀ (ptr : RowPointers c) (leaves : X.network.Site → ℕ × ℕ),
        JobsSpec (finalParsers c r P) (chainTrees c r ptr (fun v => leafTree (leaves v)))
          (vertexJobs c r ptr P leaves) := by
  intro hpad X E P z c r ptr leaves
  exact vertexJobs_spec c r ptr P leaves

end Cursor

section Native

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing
open private copyRegs from OAI.Computability.VPVNP.PairSimulationDFS

variable {w endAddr : ℕ}

/-- The observable obligations for the native path of a single visit.
The extracted histogram may depend on the private scratch layout. -/
structure RealizesJob (hist : Scratch w endAddr → L → ℕ) (semantic : VertexJob L)
    (native : VisitPath w endAddr) : Prop where
  address : native.node = (semantic.address : Word w)
  bits : choiceBits native.trace = semantic.bits
  counts : ∀ s, native.enabled s → ∀ l, hist (native.update s) l = hist s l + semantic.increment l

omit [Fintype L] in
private theorem realized_addresses {hist : Scratch w endAddr → L → ℕ} {js ps}
    (h : List.Forall₂ (RealizesJob hist) js ps) : ps.map VisitPath.node = js.map (fun j => (j.address : Word w)) := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h.address, ih]

omit [Fintype L] in
private theorem realized_bits {hist : Scratch w endAddr → L → ℕ} {js ps}
    (h : List.Forall₂ (RealizesJob hist) js ps) :
    ps.flatMap (fun p => choiceBits p.trace) = js.flatMap VertexJob.bits := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h.bits, ih]

omit [Fintype L] in
private theorem realized_counts {hist : Scratch w endAddr → L → ℕ} {js ps}
    (h : List.Forall₂ (RealizesJob hist) js ps) (s : Scratch w endAddr) (ready : Ready ps s) (l : L) :
    hist (ps.foldl (fun t p => p.update t) s) l = hist s l + (js.map (fun j => j.increment l)).sum := by
  induction h generalizing s with
  | nil => simp
  | cons h _ ih =>
    rw [List.foldl_cons, ih _ ready.2, h.counts _ ready.1]
    simp [Nat.add_assoc]

/-- Link a native path at each listed job to one complete final-site
expansion. The resulting burst reads exactly that witness's binary code
and increments each histogram component by that witness's exponent. -/
theorem execute_vertexJobs {p r k : ℕ} {M : Machine w p r k} {pc : Fin 9 → Fin p} {arcPC : Fin 5 → Fin p}
    {reg : Fin 9 ↪ Fin r} {visit done : Fin p}
    (hl : DFS.Linked M pc reg visit (arcPC 0) done) (ha : EndpointBits.Linked M arcPC (copyRegs reg) (pc 0))
    (P : SiteParsers κ N) (trees : N.Site → VertexTree) (jobs : JobsFor P) (hs : JobsSpec P trees jobs)
    (v : N.Site) (z : N.Half v) (x : (P.witnesses v z).Choice)
    {m : Memory w} {pending : List (Word w)} {control : List (Event w)}
    (visits : Visits m endAddr pending ((trees v).preorder.map (fun a : ℕ => (a : Word w))) control)
    (native : List (VisitPath w endAddr)) (hist : Scratch w endAddr → L → ℕ)
    (realized : List.Forall₂ (RealizesJob hist) (jobs v z x) native)
    (hook : ∀ j ∈ native, j.Linked M visit (pc 3) reg m)
    (c : Config w p r) (hc : c.pc = pc 0) (top : ℕ) (hstack : Represents c.privateMem top pending)
    (hptr : top + pending.length = endAddr) (ht : c.reg (reg 5) = (top : Word w))
    (he : c.reg (reg 6) = (endAddr : Word w)) (h1 : c.reg (reg 3) = 1)
    (ready : Ready native (scratch endAddr c.privateMem)) :
    ∃ out es, out.pc = done ∧ out.persistent = c.persistent ∧
      choiceBits es = (P.read v z).encode x ∧
      (∀ l, hist (scratch endAddr out.privateMem) l = hist (scratch endAddr c.privateMem) l + (P.witnesses v z).exponents x l) ∧
      es.length = control.length + (native.map fun j => j.trace.length).sum ∧
      countProbes es = countProbes control + (native.map fun j => countProbes j.trace).sum ∧
      ∀ fuel bs, execute M.program (fuel + es.length) c m ((P.read v z).encode x ++ bs) =
        (execute M.program fuel out m bs).map (fun q => ⟨es ++ q.events, q.result⟩) := by
  have nodes : native.map VisitPath.node = (trees v).preorder.map (fun a : ℕ => (a : Word w)) := by
    rw [← hs.addresses v z x, List.map_map]
    exact realized_addresses realized
  obtain ⟨out, es, hpc, hst, hout, hbs, hlen, hp, hrun⟩ :=
    DFS.execute_linked_visits hl ha visits native nodes hook c hc top hstack hptr ht he h1 ready
  have bits := hbs.trans ((realized_bits realized).trans (hs.bits v z x))
  refine ⟨out, es, hpc, hst, bits, fun l => ?_, hlen, hp, ?_⟩
  · rw [hout, realized_counts realized _ ready l, hs.increments v z x l]
  · rw [← bits]
    exact hrun

end Native
end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
