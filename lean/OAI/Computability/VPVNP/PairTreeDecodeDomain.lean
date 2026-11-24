import OAI.Computability.VPVNP.PairTreeNodeReaders

/-! # Reachability of every role visit on arbitrary private streams -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open BurstRAM PrivateRAM DFS NetworkKernel CompressorRecords LocalHistory NodeArguments
open scoped Fin.CommRing
open private addTree from OAI.Computability.VPVNP.PairTraversalHistory
open private push_subtrees from OAI.Computability.VPVNP.PairTreeDecoder

variable {W endAddr : ℕ} (hook : HookParser W endAddr)
    (valid : List Packet → Scratch W endAddr → Prop)
    (domain : Word W → Scratch W endAddr → Prop)

/-- A failing visit can stop the stream in the middle of any one child.
The later siblings need to be prepared only after that entire child succeeds. -/
private theorem valid_append (xs ys : List (Word W)) (s : Scratch W endAddr) (bits : List Bool)
    (first : hook.ValidAlong domain xs s bits)
    (later : ∀ mid tail, hook.decode xs s bits = some (mid,tail) → hook.ValidAlong domain ys mid tail) :
    hook.ValidAlong domain (xs++ys) s bits := by
  induction xs generalizing s bits with
  | nil => exact later s bits rfl
  | cons node ns ih =>
    refine ⟨first.1,?_⟩
    intro job more hit
    exact ih (job.update s) more (first.2 job more hit) (fun mid tail run =>
      later mid tail (by simp only [HookParser.decode,hit]; exact run))

/-- The decoder remains in its admitted domain at every node of this block when the block's
argument packets precede the pending suffix. -/
def AlongBlock (args : List Packet) (nodes : List (Word W)) : Prop :=
  ∀ pending s bits, valid (args++pending) s → hook.ValidAlong domain nodes s bits

private theorem forest_along (n : ℕ) (α : Fin n → Type) (packet : Fin n → Packet)
    (nodes : Fin n → List (Word W)) (code : ∀ i, α i → List Bool)
    (child : ∀ i, ExactBlock hook valid [packet i] (nodes i) (code i))
    (along : ∀ i, AlongBlock hook valid domain [packet i] (nodes i)) :
    AlongBlock hook valid domain (List.ofFn packet) (List.ofFn nodes).flatten := by
  induction n with
  | zero =>
    intro _ _ _ _
    simp [HookParser.ValidAlong]
  | succ n ih =>
    intro pending s bits prepared
    let rest := List.ofFn (fun i : Fin n => packet i.succ)
    let ns := (List.ofFn fun i : Fin n => nodes i.succ).flatten
    have pkts : List.ofFn packet = packet 0 :: rest := List.ofFn_succ
    have addresses : (List.ofFn nodes).flatten = nodes 0 ++ ns := by rw [List.ofFn_succ]; rfl
    rw [pkts] at prepared
    rw [addresses]
    apply valid_append hook domain _ _ _ _ (along 0 (rest++pending) s bits prepared)
    intro mid tail success
    have next := ((child 0).sound (rest++pending) s bits mid tail prepared success).2
    exact ih (fun i => α i.succ) (fun i => packet i.succ) (fun i => nodes i.succ)
      (fun i => code i.succ) (fun i => child i.succ) (fun i => along i.succ) pending mid tail next

variable {R : Type*} [CommRing R] {L : Type} [Fintype L] {f : L → R} {N Y : Network}

/-- The prepared frontier entails the native role domain of its first
packet. The domain may retain geometry words, old half-wires and headers. -/
def HeadDomain : Prop :=
  ∀ (q : Packet) pending s, valid (q::pending) s → domain (q.node : Word W) s

/-- The admitted-domain condition holds along each selected subtree's full word-encoded
preorder starting from its root packet. -/
def SubtreeAlong (trees : N.Site → VertexTree) (pack : Packets N) : Prop :=
  ∀ v z, AlongBlock hook valid domain [pack v z] ((trees v).preorder.map (fun n : ℕ => (n : Word W)))

theorem leaf_along (ptr : N.Site → ℕ × ℕ) (pack : Packets N)
    (address : ∀ v z, (pack v z).node = (ptr v).1) (head : HeadDomain valid domain) :
    SubtreeAlong hook valid domain (fun v => leafTree (ptr v)) pack := by
  intro v z pending s bits prepared
  have h := head (pack v z) pending s prepared
  rw [address] at h
  exact ⟨h,fun _ _ _ => trivial⟩

private theorem push_along {t : Term R N} (r : TermParsers f t) (ptr : t.output.Site → ℕ × ℕ)
    (P : SiteParsers f N) (trees : N.Site → VertexTree) (before : Packets N) (next : Packets t.output)
    (old : Subtrees hook valid P trees before) (along : SubtreeAlong hook valid domain trees before)
    (step : NodeStep hook valid r ptr before next) (address : ∀ v z, (next v z).node = (ptr v).1)
    (head : HeadDomain valid domain) :
    SubtreeAlong hook valid domain (addTree r ptr trees) next := by
  intro v z pending s bits prepared
  let o := r.order.children v
  let ns (i : Fin o.length) := (trees (o.entries i).val).preorder.map (fun n : ℕ => (n : Word W))
  have order : ((addTree r ptr trees v).preorder.map (fun n : ℕ => (n : Word W))) =
      ((ptr v).1 : Word W) :: (List.ofFn ns).flatten := by
    change List.map _ ((ptr v).1 :: (List.ofFn fun i => (trees (o.entries i).val).preorder).flatten) = _
    simp [ns,List.map_flatten,Function.comp_def]
  rw [order]
  have dom := head (next v z) pending s prepared
  rw [address] at dom
  refine ⟨dom,?_⟩
  intro job more hit
  obtain ⟨a,_,_,frame⟩ := step.sound v z pending s bits job more prepared hit
  let α := fun i : Fin o.length => let u := o.entries i; (P.witnesses u.val (a u.val u.prop)).Choice
  let code (i : Fin o.length) (x : α i) := let u := o.entries i; (P.read u.val (a u.val u.prop)).encode x
  let ch := fun i : Fin o.length => let u := o.entries i; before u.val (a u.val u.prop)
  exact forest_along hook valid domain o.length α ch ns code (fun i => old _ _) (fun i => along _ _)
    pending (job.update s) more frame

/-- The address component of each level's half-wire packet is the numeric
header pointer of that level. -/
def PointerLayers {N Y : Network} (c : TermChain R N Y) (ptr : RowPointers c)
    (layers : PacketLayers c) : Prop :=
  match c with
  | .done _ => True
  | .more _ _ tail => (∀ v z, (layers.1 v z).node = (ptr.1 v).1) ∧ PointerLayers tail ptr.2 layers.2

/-- All native calls visited before the first failed read have their actual
input domain. This includes malformed, short, and extra incoming streams. -/
theorem chain_along {N Y : Network} (c : TermChain R N Y) (r : ChainParsers f c) (ptr : RowPointers c)
    (layers : PacketLayers c) (P : SiteParsers f N) (trees : N.Site → VertexTree) (input : Packets N)
    (initial : Subtrees hook valid P trees input) (along : SubtreeAlong hook valid domain trees input)
    (steps : StepLayers hook valid c r ptr layers input) (addr : PointerLayers c ptr layers)
    (head : HeadDomain valid domain) :
    SubtreeAlong hook valid domain (chainTrees c r ptr trees) (finalPackets c layers input) := by
  induction c with
  | done => exact along
  | more t rec tail ih =>
    exact ih r.2 ptr.2 layers.2 (r.1.push P) (addTree r.1 ptr.1 trees) layers.1
      (push_subtrees hook valid r.1 ptr.1 P trees input layers.1 initial steps.1)
      (push_along hook valid domain r.1 ptr.1 P trees input layers.1 initial along steps.1 addr.1 head)
      steps.2 addr.2

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
