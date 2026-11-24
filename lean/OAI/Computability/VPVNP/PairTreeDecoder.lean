import OAI.Computability.VPVNP.PairTypedVertexJobs

/-!
# Exact private-bit decoding through the selected term tree

A term visit selects its placed half-wires and a local kernel occurrence.
Its children then run on these precise half-wires, in the stored order.
Every successful subtree consumes the code of a factor occurrence, and
every occurrence runs with any following suffix. Both statements maintain
the argument packets belonging to the other pending visits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open BurstRAM PrivateRAM DFS NetworkKernel CompressorRecords LocalHistory NodeArguments
open scoped Fin.CommRing
open private push_encode from OAI.Computability.VPVNP.PairSimulationVertexJobs
open private addTree from OAI.Computability.VPVNP.PairTraversalHistory

variable {W endAddr : ℕ} (hook : HookParser W endAddr)
variable (valid : List Packet → Scratch W endAddr → Prop)

private theorem decode_append (xs ys : List (Word W)) (s : Scratch W endAddr) (bits : List Bool) :
    hook.decode (xs++ys) s bits = (hook.decode xs s bits).bind fun pair =>
      hook.decode ys pair.1 pair.2 := by
  induction xs generalizing s bits with
  | nil => rfl
  | cons x xs ih =>
    cases h : hook.read x s bits with
    | none => simp [HookParser.decode,h]
    | some pair => simp [HookParser.decode,h,ih]

/-- A list of prepared packet arguments and native addresses realizes one
prefix code. On success the older pending suffix is still prepared. -/
structure ExactBlock {α : Type*} (args : List Packet) (nodes : List (Word W)) (encode : α → List Bool) : Prop where
  sound : ∀ pending s bits out tail, valid (args++pending) s →
    hook.decode nodes s bits = some (out,tail) → (∃ x, bits = encode x ++ tail) ∧ valid pending out
  complete : ∀ pending s x tail, valid (args++pending) s →
    ∃ out, hook.decode nodes s (encode x ++ tail) = some (out,tail)

theorem ExactBlock.iff {α : Type*} {args nodes} {encode : α → List Bool}
    (h : ExactBlock hook valid args nodes encode) {pending s} (prepared : valid (args++pending) s)
    (bits tail : List Bool) :
    (∃ out, hook.decode nodes s bits = some (out,tail)) ↔ ∃ x, bits = encode x ++ tail := by
  constructor
  · rintro ⟨out,hr⟩
    exact (h.sound pending s bits out tail prepared hr).1
  · rintro ⟨x,rfl⟩
    exact h.complete pending s x tail prepared

/-- Decode all children in order, including an empty fiber, passing along
the scratch produced by each preceding child. -/
private theorem forest (n : ℕ) (α : Fin n → Type) (packet : Fin n → Packet)
    (nodes : Fin n → List (Word W)) (code : ∀ i, α i → List Bool)
    (child : ∀ i, ExactBlock hook valid [packet i] (nodes i) (code i)) :
    ExactBlock hook valid (List.ofFn packet) (List.ofFn nodes).flatten
      (fun x : ∀ i, α i => (List.ofFn fun i => code i (x i)).flatten) := by
  induction n with
  | zero =>
    constructor
    · intro pending s bits out tail prepared run
      have pair : s = out ∧ bits = tail := by simpa [HookParser.decode] using run
      obtain ⟨rfl,rfl⟩ := pair
      exact ⟨⟨fun i => i.elim0,by simp⟩,by simpa using prepared⟩
    · intro pending s x tail _
      exact ⟨s,by simp [HookParser.decode]⟩
  | succ n ih =>
    let rest := List.ofFn (fun i : Fin n => packet i.succ)
    let tailNodes := (List.ofFn (fun i : Fin n => nodes i.succ)).flatten
    let tailCode (x : ∀ i : Fin n, α i.succ) := (List.ofFn fun i => code i.succ (x i)).flatten
    have tailRun : ExactBlock hook valid rest tailNodes tailCode :=
      ih (fun i => α i.succ) (fun i => packet i.succ) (fun i => nodes i.succ)
        (fun i => code i.succ) (fun i => child i.succ)
    have packets : List.ofFn packet = packet 0 :: rest := List.ofFn_succ
    have addresses : (List.ofFn nodes).flatten = nodes 0 ++ tailNodes := by rw [List.ofFn_succ]; rfl
    have codes (x : ∀ i, α i) :
        (List.ofFn fun i => code i (x i)).flatten = code 0 (x 0) ++ tailCode (fun i => x i.succ) := by
      rw [List.ofFn_succ]; rfl
    constructor
    · intro pending s bits out tail prepared run
      rw [packets] at prepared
      rw [addresses,decode_append] at run
      obtain ⟨⟨mid,more⟩,first,later⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨⟨x,hx⟩,frame⟩ := (child 0).sound (rest++pending) s bits mid more prepared first
      obtain ⟨⟨xs,hxs⟩,done⟩ := tailRun.sound pending mid more out tail frame later
      refine ⟨⟨Fin.cons x xs,?_⟩,done⟩
      rw [codes,hx,hxs]
      simp only [Fin.cons_zero,Fin.cons_succ,List.append_assoc]
    · intro pending s x tail prepared
      rw [packets] at prepared
      rw [addresses,codes,List.append_assoc,decode_append]
      let more := tailCode (fun i => x i.succ) ++ tail
      obtain ⟨mid,first⟩ := (child 0).complete (rest++pending) s (x 0) more prepared
      have frame := ((child 0).sound (rest++pending) s _ mid more prepared first).2
      obtain ⟨out,later⟩ := tailRun.complete pending mid (fun i => x i.succ) tail frame
      exact ⟨out,Option.bind_eq_some_iff.mpr ⟨(mid,more),first,later⟩⟩

variable {R : Type*} [CommRing R] {L : Type} [Fintype L] {f : L → R} {N Y : Network}

/-- The concrete pointer and ordered private half-wire words for a site. -/
abbrev Packets (N : Network) := ∀ v, N.Half v → Packet

/-- Each selected subtree decodes precisely the corresponding site's encoded choice tape while
preserving the pending packet suffix. -/
def Subtrees (P : SiteParsers f N) (trees : N.Site → VertexTree) (pack : Packets N) : Prop :=
  ∀ v z, ExactBlock hook valid [pack v z] ((trees v).preorder.map (fun n : ℕ => (n : Word W)))
    (P.read v z).encode

/-- Child packets of a selected term at one output site, enumerated in the parser's order of
the placement preimage. -/
noncomputable def children {t : Term R N} (r : TermParsers f t) (pack : Packets N)
    (v : t.output.Site) (a : Placed t.place N.Half v) : List Packet :=
  List.ofFn fun i => let u := (r.order.children v).entries i; pack u.val (a u.val u.prop)

/-- The only term-specific obligations concern the single popped row.
Its successful reads determine the placed half-wires and local factor,
and its native updates prepare the genuine child buffers. -/
structure NodeStep {t : Term R N} (r : TermParsers f t) (ptr : t.output.Site → ℕ × ℕ)
    (before : Packets N) (next : Packets t.output) : Prop where
  sound : ∀ v z pending s bits job tail, valid (next v z :: pending) s →
    hook.read ((ptr v).1 : Word W) s bits = some (job,tail) →
    ∃ a k, bits = r.nodeBits v a z k ++ tail ∧ valid (children r before v a ++ pending) (job.update s)
  complete : ∀ v z pending s a k tail, valid (next v z :: pending) s →
    ∃ job, hook.read ((ptr v).1 : Word W) s (r.nodeBits v a z k ++ tail) = some (job,tail) ∧
      valid (children r before v a ++ pending) (job.update s)

private theorem push_subtrees {t : Term R N} (r : TermParsers f t) (ptr : t.output.Site → ℕ × ℕ)
    (P : SiteParsers f N) (trees : N.Site → VertexTree) (before : Packets N) (next : Packets t.output)
    (old : Subtrees hook valid P trees before) (step : NodeStep hook valid r ptr before next) :
    Subtrees hook valid (r.push P) (addTree r ptr trees) next := by
  intro v z
  let o := r.order.children v
  let address := ((ptr v).1 : Word W)
  let ns (i : Fin o.length) := (trees (o.entries i).val).preorder.map (fun n : ℕ => (n : Word W))
  have order : ((addTree r ptr trees v).preorder.map (fun n : ℕ => (n : Word W))) =
      address :: (List.ofFn ns).flatten := by
    change List.map _ ((ptr v).1 :: (List.ofFn fun i => (trees (o.entries i).val).preorder).flatten) = _
    simp [ns,address,List.map_flatten,Function.comp_def]
  let alpha (a : Placed t.place N.Half v) (i : Fin o.length) :=
    let u := o.entries i; (P.witnesses u.val (a u.val u.prop)).Choice
  let code (a : Placed t.place N.Half v) (i : Fin o.length) (x : alpha a i) :=
    let u := o.entries i; (P.read u.val (a u.val u.prop)).encode x
  let ch (a : Placed t.place N.Half v) := fun i : Fin o.length =>
    let u := o.entries i; before u.val (a u.val u.prop)
  let codes (a : Placed t.place N.Half v) (x : ∀ i, alpha a i) := (List.ofFn fun i => code a i (x i)).flatten
  have sub (a : Placed t.place N.Half v) :
      ExactBlock hook valid (children r before v a) (List.ofFn ns).flatten (codes a) :=
    forest hook valid o.length (alpha a) (ch a) ns (code a) (fun i => old _ _)
  let e := t.pushChoice P.factors P.witnesses r.witness v z
  let fam (a : Placed t.place N.Half v) := fun u : t.Preimage v => (P.witnesses u.val (a u.val u.prop)).Choice
  let index (a : Placed t.place N.Half v) := Equiv.piCongrLeft (fam a) o.entries
  have split (x : ((r.push P).witnesses v z).Choice) :
      ((r.push P).read v z).encode x = r.nodeBits v (e x).1 z (e x).2.2 ++
        codes (e x).1 (fun i => (e x).2.1 (o.entries i)) := push_encode r P v z x
  constructor
  · intro pending s bits out tail prepared run
    rw [order,HookParser.decode] at run
    obtain ⟨⟨job,more⟩,atNode,below⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨a,k,head,frame⟩ := step.sound v z pending s bits job more prepared atNode
    obtain ⟨⟨xs,tailBits⟩,after⟩ := (sub a).sound pending _ more out tail frame below
    let selected : ((r.push P).witnesses v z).Choice := e.symm ⟨a,(index a xs,k)⟩
    have selected_eq : e selected = ⟨a,(index a xs,k)⟩ := e.apply_symm_apply _
    refine ⟨⟨selected,?_⟩,after⟩
    rw [split selected,selected_eq,head,tailBits,List.append_assoc]
    congr 2
    change codes a xs = codes a (fun i => (index a xs) (o.entries i))
    apply congrArg (codes a)
    funext i
    exact (Equiv.piCongrLeft_apply_apply (fam a) o.entries xs i).symm
  · intro pending s x tail prepared
    let a := (e x).1
    let xs := fun i => (e x).2.1 (o.entries i)
    let more := codes a xs ++ tail
    obtain ⟨job,atNode,frame⟩ := step.complete v z pending s a (e x).2.2 more prepared
    obtain ⟨out,below⟩ := (sub a).complete pending _ xs tail frame
    refine ⟨out,?_⟩
    rw [order,HookParser.decode,split x,List.append_assoc]
    exact Option.bind_eq_some_iff.mpr ⟨(job,more),atNode,below⟩

/-- The sequence of packet assignments to output sites along a selected term chain. -/
def PacketLayers {N Y : Network} : TermChain R N Y → Type
  | .done _ => PUnit
  | .more t _ tail => Packets t.output × PacketLayers tail

/-- Propagate the packet assignments down the selected chain and return the packets at the
final output sites. -/
def finalPackets {N Y : Network} (c : TermChain R N Y) (layers : PacketLayers c) (input : Packets N) :
    Packets Y :=
  match c with
  | .done _ => input
  | .more _ _ tail => finalPackets tail layers.2 layers.1

/-- Node-step correctness holds at each selected layer, relating the incoming packets to that
layer's output packets and row pointers. -/
def StepLayers {N Y : Network} (c : TermChain R N Y) (r : ChainParsers f c) (ptr : RowPointers c)
    (layers : PacketLayers c) (input : Packets N) : Prop :=
  match c with
  | .done _ => True
  | .more _ _ tail => NodeStep hook valid r.1 ptr.1 input layers.1 ∧
      StepLayers tail r.2 ptr.2 layers.2 layers.1

/-- Exact decoding, including failure, for every selected term chain.
Local implementation proofs are needed only for individual role rows. -/
theorem chain_exact {N Y : Network} (c : TermChain R N Y) (r : ChainParsers f c) (ptr : RowPointers c)
    (layers : PacketLayers c) (P : SiteParsers f N) (trees : N.Site → VertexTree) (input : Packets N)
    (initial : Subtrees hook valid P trees input) (steps : StepLayers hook valid c r ptr layers input) :
    Subtrees hook valid (finalParsers c r P) (chainTrees c r ptr trees) (finalPackets c layers input) := by
  induction c with
  | done => exact initial
  | more t rec tail ih =>
    exact ih r.2 ptr.2 layers.2 (r.1.push P) (addTree r.1 ptr.1 trees) layers.1
      (push_subtrees hook valid r.1 ptr.1 P trees input layers.1 initial steps.1) steps.2

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
