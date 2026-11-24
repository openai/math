import OAI.Computability.VPVNP.PairTreeNodeReaders

/-!
# Realizing each compressed occurrence by its physical preorder jobs

The local native map path contributes the selected kernel's label counts.
The remaining paths are supplied by the old sites in the real placement
fiber. The construction preserves pending arguments and any required
property of each native trace, including its linkage and read footprint.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open BurstRAM PrivateRAM DFS NetworkKernel CompressorRecords LocalHistory NodeArguments
open scoped Fin.CommRing

variable {W endAddr : ℕ} {L : Type}
    (valid : List Packet → Scratch W endAddr → Prop) (hist : Scratch W endAddr → L → ℕ)
    (guard : VisitPath W endAddr → Prop)

private theorem ready_append (xs ys : List (VisitPath W endAddr)) (s : Scratch W endAddr)
    (first : Ready xs s) (later : Ready ys (xs.foldl (fun old j => j.update old) s)) :
    Ready (xs++ys) s := by
  induction xs generalizing s with
  | nil => exact later
  | cons x xs ih => exact ⟨first.1,ih _ first.2 later⟩

/-- Actual local paths with the specified exponent increments and private
word codes. The guard can include the exact native link and all allowed
external reads, so these facts hold for each path in the produced list. -/
structure Effects (s : Scratch W endAddr) (pending : List Packet) (semantic : List (VertexJob L))
    (native : List (VisitPath W endAddr)) : Prop where
  realized : List.Forall₂ (RealizesJob hist) semantic native
  ready : Ready native s
  framed : ∀ j ∈ native, guard j
  remaining : valid pending (native.foldl (fun old j => j.update old) s)

private theorem Effects.join {s : Scratch W endAddr} {pending mid : List Packet}
    {a b : List (VertexJob L)} {x y : List (VisitPath W endAddr)}
    (first : Effects valid hist guard s mid a x)
    (second : Effects valid hist guard (x.foldl (fun old j => j.update old) s) pending b y) :
    Effects valid hist guard s pending (a++b) (x++y) := by
  refine ⟨List.rel_append first.realized second.realized,ready_append _ _ _ first.ready second.ready,?_,?_⟩
  · intro j hj
    exact (List.mem_append.mp hj).elim (first.framed j) (second.framed j)
  · simpa only [List.foldl_append] using second.remaining

private theorem forest_effects (n : ℕ) (pack : Fin n → Packet) (jobs : Fin n → List (VertexJob L))
    (child : ∀ i pending s, valid (pack i::pending) s →
      ∃ xs, Effects valid hist guard s pending (jobs i) xs)
    (pending : List Packet) (s : Scratch W endAddr) (ready : valid (List.ofFn pack ++ pending) s) :
    ∃ xs, Effects valid hist guard s pending (List.ofFn jobs).flatten xs := by
  induction n generalizing pending s with
  | zero =>
    exact ⟨[],⟨by simp, trivial,by simp,by simpa using ready⟩⟩
  | succ n ih =>
    let rest := List.ofFn (fun i : Fin n => pack i.succ)
    have ps : List.ofFn pack = pack 0 :: rest := List.ofFn_succ
    rw [ps] at ready
    obtain ⟨xs,first⟩ := child 0 (rest++pending) s ready
    obtain ⟨ys,later⟩ := ih (fun i => pack i.succ) (fun i => jobs i.succ) (fun i => child i.succ)
      pending _ first.remaining
    exact ⟨xs++ys,by rw [List.ofFn_succ]; exact first.join valid hist guard later⟩

variable {R : Type*} [CommRing R] [Fintype L] {f : L → R} {N Y : Network}

/-- Each occurrence is realized by the ordered path list supplied by this
layer, on every scratch preparing its packet and every pending suffix. -/
def Emits (P : SiteParsers f N) (input : Packets N) (jobs : JobsFor P) : Prop :=
  ∀ v z x pending s, valid (input v z::pending) s →
    ∃ native, Effects valid hist guard s pending (jobs v z x) native

/-- One visit supplies its own monomial increment and the old packets for
its children. No claim about the later subtree is a local hypothesis. -/
def EmitsNode {t : Term R N} (r : TermParsers f t) (ptr : t.output.Site → ℕ × ℕ)
    (before : Packets N) (next : Packets t.output) : Prop :=
  ∀ v z a k pending s, valid (next v z::pending) s →
    ∃ job, RealizesJob hist ⟨(ptr v).1,r.nodeBits v a z k,(r.witness v a z).exponents k⟩ job ∧
      job.enabled s ∧ guard job ∧ valid (children r before v a++pending) (job.update s)

/-- The concrete term-row reader and its label effect give the native
per-node path used by the positive induction. -/
theorem emitsNode_of_read {t : Term R N} (hook : HookParser W endAddr) (r : TermParsers f t)
    (ptr : t.output.Site → ℕ × ℕ) (before : Packets N) (next : Packets t.output)
    (steps : NodeStep hook valid r ptr before next)
    (effect : ∀ v z a k pending s job, valid (next v z::pending) s →
      hook.read ((ptr v).1 : Word W) s (r.nodeBits v a z k) = some (job,[]) →
      RealizesJob hist ⟨(ptr v).1,r.nodeBits v a z k,(r.witness v a z).exponents k⟩ job ∧
        job.enabled s ∧ guard job) :
    EmitsNode valid hist guard r ptr before next := by
  intro v z a k pending s h
  obtain ⟨j,hit,frame⟩ := steps.complete v z pending s a k [] h
  rw [List.append_nil] at hit
  obtain ⟨real,en,g⟩ := effect v z a k pending s j h hit
  exact ⟨j,real,en,g,frame⟩

theorem leaf_emits (P : SiteParsers f N) (input : Packets N) (ptr : N.Site → ℕ × ℕ)
    (each : ∀ v z x pending s, valid (input v z::pending) s → ∃ j,
      RealizesJob hist ⟨(ptr v).1,(P.read v z).encode x,(P.witnesses v z).exponents x⟩ j ∧
        j.enabled s ∧ guard j ∧ valid pending (j.update s)) :
    Emits valid hist guard P input (leafJobs P ptr) := by
  intro v z x pending s h
  obtain ⟨j,real,en,g,remaining⟩ := each v z x pending s h
  exact ⟨[j],⟨.cons real .nil,⟨en,trivial⟩,fun _ m => (List.mem_singleton.mp m) ▸ g,remaining⟩⟩

private theorem push_emits {t : Term R N} (r : TermParsers f t) (ptr : t.output.Site → ℕ × ℕ)
    (P : SiteParsers f N) (before : Packets N) (next : Packets t.output) (jobs : JobsFor P)
    (old : Emits valid hist guard P before jobs) (step : EmitsNode valid hist guard r ptr before next) :
    Emits valid hist guard (r.push P) next (pushJobs r ptr P jobs) := by
  intro v z x pending s ready
  let q := t.pushChoice P.factors P.witnesses r.witness v z x
  let o := r.order.children v
  let ch (i : Fin o.length) := let u := o.entries i; before u.val (q.1 u.val u.prop)
  let below (i : Fin o.length) := let u := o.entries i; jobs u.val (q.1 u.val u.prop) (q.2.1 u)
  obtain ⟨head,real,en,g,prep⟩ := step v z q.1 q.2.2 pending s ready
  obtain ⟨rest,eff⟩ := forest_effects valid hist guard o.length ch below
    (fun i => old _ _ _) pending (head.update s) prep
  refine ⟨head::rest,⟨.cons real eff.realized,⟨en,eff.ready⟩,?_,eff.remaining⟩⟩
  intro j hj
  rcases List.mem_cons.mp hj with eqn | later
  · exact eqn ▸ g
  · exact eff.framed j later

/-- Each selected layer's node visits emit the required histogram increments under the guard
and pending-packet invariant. -/
def EmissionLayers {N Y : Network} (c : TermChain R N Y) (r : ChainParsers f c) (ptr : RowPointers c)
    (layers : PacketLayers c) (input : Packets N) : Prop :=
  match c with
  | .done _ => True
  | .more _ _ tail => EmitsNode valid hist guard r.1 ptr.1 input layers.1 ∧
      EmissionLayers tail r.2 ptr.2 layers.2 layers.1

/-- From the actual leaf paths and individual term-row paths, produce the
entire ordered native job list for any selected final-site occurrence. -/
theorem chain_emits {N Y : Network} (c : TermChain R N Y) (r : ChainParsers f c) (ptr : RowPointers c)
    (layers : PacketLayers c) (P : SiteParsers f N) (input : Packets N) (jobs : JobsFor P)
    (initial : Emits valid hist guard P input jobs) (steps : EmissionLayers valid hist guard c r ptr layers input) :
    Emits valid hist guard (finalParsers c r P) (finalPackets c layers input) (chainJobs c r ptr P jobs) := by
  induction c with
  | done => exact initial
  | more t rec tail ih =>
    exact ih r.2 ptr.2 layers.2 (r.1.push P) layers.1 (pushJobs r.1 ptr.1 P jobs)
      (push_emits valid hist guard r.1 ptr.1 P input layers.1 jobs initial steps.1) steps.2

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
