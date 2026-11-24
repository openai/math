import OAI.Computability.VPVNP.PairVertexDispatch
import OAI.Computability.VPVNP.PairVertexSelectedReport
import OAI.Computability.VPVNP.RAMProcessorReportPrefix

/-!
# Local row effects under the physical vertex dispatcher

Each term pass and each cursor leaf selects its role by a tag lookup.
The router adds this lookup to the role trace and preserves the returned
suffix, the role's scratch update and its histogram increment. This lifts
the role-specific decoder and emission proofs to the common DFS entry.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM DFS LocalHistory NetworkKernel NodeArguments TreeDecode CompressorRecords
open CompressorRecords.SourceTransport (Reads)
open scoped Fin.CommRing

variable {W endAddr : ℕ} {m : Memory W} {offset node : Word W}
    {saved : Scratch W endAddr} {role : NodeDispatch.Role}
    {handlers : NodeDispatch.Role → HookParser W endAddr}

/-- Inverting a successful dispatch recovers the selected role's job and
the very same suffix. Conversely, each role success gives this wrapped job. -/
theorem dispatcher_read_iff (tag : NodeDispatch.role (m (offset + node).val) = role)
    {bits tail : List Bool} {job : VisitPath W endAddr} :
    (dispatcher handlers m offset).read node saved bits = some (job, tail) ↔
      ∃ body, (handlers role).read node saved bits = some (body, tail) ∧
        job = dispatchJob m offset node saved body := by
  simp only [dispatcher, tag, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨body, rest⟩, hit, h⟩
    cases h
    exact ⟨body, hit, rfl⟩
  · rintro ⟨body, hit, rfl⟩
    exact ⟨(body, tail), hit, rfl⟩

/-- All role tags use one probe at the tag address. The branches differ
only in their number of ticks. -/
theorem dispatchEvents_footprint (allow : ℕ → Prop) (tagCell : allow (offset + node).val) :
    after m (dispatchEvents m offset node) = m ∧ Reads allow (dispatchEvents m offset node) := by
  by_cases tag : m (offset + node).val = 0
  all_goals
    constructor
    · simp only [dispatchEvents, NodeDispatch.events, tag, ite_true, ite_false]
      rfl
    · intro a v h
      simp only [dispatchEvents, NodeDispatch.events, tag, ite_true, ite_false, List.mem_append,
        List.mem_replicate, List.mem_cons, List.not_mem_nil, reduceCtorEq, and_false,
        false_or, or_false, Event.read.injEq] at h
      exact h.1 ▸ tagCell

theorem dispatchJob_cost (body : VisitPath W endAddr) :
    countProbes (dispatchJob m offset node saved body).trace = countProbes body.trace + 1 ∧
      (dispatchJob m offset node saved body).trace.length ≤ body.trace.length + 9 := by
  obtain ⟨p, t, _⟩ := dispatchEvents_cost m offset node
  simp only [dispatchJob, countProbes_append, List.length_append, p]
  omega

theorem dispatchJob_realizes {L : Type} {hist : Scratch W endAddr → L → ℕ}
    {semantic : VertexJob L} {body : VisitPath W endAddr} (real : RealizesJob hist semantic body) :
    RealizesJob hist semantic (dispatchJob m offset node saved body) := by
  refine ⟨real.address, ?_, fun s h => real.counts s h.2⟩
  simp only [dispatchJob, PrimedInputRAM.Flow.choiceBits_append,
    (dispatchEvents_cost m offset node).2.2,
    List.nil_append, real.bits]

variable {geometry rootFields leaf shrink refresh : Segment} {p regs : ℕ}
    {A : Placement (segments geometry rootFields leaf shrink refresh) p regs}
    {M : Machine W p regs 11}

/-- The role body starts at its own entry and returns to the common DFS
header. Its cost may use a different allowance from the full job's cost. -/
def RoleJobGuard (A : Placement (segments geometry rootFields leaf shrink refresh) p regs)
    (M : Machine W p regs 11) (m : Memory W) (role : NodeDispatch.Role) (allow : ℕ → Prop)
    (cost : VisitPath W endAddr → Prop) (body : VisitPath W endAddr) : Prop :=
  body.Linked M (A.entry (rolePart role)) (A.dfsPC 3) A.dfs m ∧ after m body.trace = m ∧
    Reads allow body.trace ∧ cost body

theorem dispatchJob_guard (linked : Contains A M) {G histBase : Word W}
    {allow : ℕ → Prop} {rawCost cost : VisitPath W endAddr → Prop}
    {body : VisitPath W endAddr} (resident : ResidentGeometry saved G offset histBase)
    (tag : NodeDispatch.role (m (offset + node).val) = role) (tagCell : allow (offset + node).val)
    (addr : body.node = node) (raw : RoleJobGuard A M m role allow rawCost body)
    (charge : rawCost body → cost (dispatchJob m offset node saved body)) :
    JobGuard A M m allow cost (dispatchJob m offset node saved body) := by
  obtain ⟨noWrite, reads⟩ := dispatchEvents_footprint (m := m) allow tagCell
  refine ⟨dispatchJob_linked linked resident tag addr raw.1, ?_, ?_, charge raw.2.2.2⟩
  · change after m (dispatchEvents m offset node ++ body.trace) = m
    simp only [after, List.foldl_append] at noWrite ⊢
    rw [noWrite]
    exact raw.2.1
  · intro a v h
    exact (List.mem_append.mp h).elim (reads a v) (raw.2.2.1 a v)

variable {R : Type*} [CommRing R] {L : Type} [Fintype L] {f : L → R} {N : Network}
    {valid : List Packet → Scratch W endAddr → Prop} {hist : Scratch W endAddr → L → ℕ}

section Term

variable {t : Term R N} {r : TermParsers f t} {ptr : t.output.Site → ℕ × ℕ}
    {before : Packets N} {next : Packets t.output}
    (tag : ∀ v, NodeDispatch.role (m (offset + ((ptr v).1 : Word W)).val) = role)

include tag

theorem dispatcher_nodeStep (raw : NodeStep (handlers role) valid r ptr before next) :
    NodeStep (dispatcher handlers m offset) valid r ptr before next := by
  constructor
  · intro v z pending s bits job tail ready hit
    obtain ⟨body, read, rfl⟩ := (dispatcher_read_iff (tag v)).mp hit
    exact raw.sound v z pending s bits body tail ready read
  · intro v z pending s a k tail ready
    obtain ⟨body, read, frame⟩ := raw.complete v z pending s a k tail ready
    exact ⟨_, (dispatcher_read_iff (tag v)).mpr ⟨body, read, rfl⟩, frame⟩

/-- At a known role row, only the body must be matched against the term
reader, and only its writes have to be checked against the child packets. -/
theorem dispatcher_nodeStep_of_suffix
    (suffix : ∀ v z pending s bits, valid (next v z :: pending) s →
      ((handlers role).read ((ptr v).1 : Word W) s bits).map Prod.snd =
        ((nodeReader r v z).read bits).map Prod.snd)
    (write : ∀ v z pending s bits job tail a k, valid (next v z :: pending) s →
      (handlers role).read ((ptr v).1 : Word W) s bits = some (job, tail) →
      bits = r.nodeBits v a z k ++ tail → valid (children r before v a ++ pending) (job.update s)) :
    NodeStep (dispatcher handlers m offset) valid r ptr before next :=
  dispatcher_nodeStep tag (nodeStep_of_suffix (handlers role) valid r ptr before next suffix write)

variable {G histBase : Word W} {allow : ℕ → Prop} {rawCost cost : VisitPath W endAddr → Prop}
    (linked : Contains A M) (tagCell : ∀ v, allow (offset + ((ptr v).1 : Word W)).val)
    (resident : ∀ v z pending s, valid (next v z :: pending) s →
      ResidentGeometry s G offset histBase)
    (charge : ∀ v s body, rawCost body → cost (dispatchJob m offset ((ptr v).1 : Word W) s body))

include linked tagCell resident charge

theorem dispatcher_emitsNode
    (raw : EmitsNode valid hist (RoleJobGuard A M m role allow rawCost) r ptr before next) :
    EmitsNode valid hist (JobGuard A M m allow cost) r ptr before next := by
  intro v z a k pending s ready
  obtain ⟨body, real, en, guard, frame⟩ := raw v z a k pending s ready
  exact ⟨_, dispatchJob_realizes real, ⟨rfl, en⟩,
    dispatchJob_guard linked (resident v z pending s ready) (tag v) (tagCell v) real.address guard
      (charge v s body), frame⟩

theorem dispatcher_emitsNode_of_read (steps : NodeStep (handlers role) valid r ptr before next)
    (effect : ∀ v z a k pending s body, valid (next v z :: pending) s →
      (handlers role).read ((ptr v).1 : Word W) s (r.nodeBits v a z k) = some (body, []) →
      RealizesJob hist ⟨(ptr v).1, r.nodeBits v a z k, (r.witness v a z).exponents k⟩ body ∧
        body.enabled s ∧ RoleJobGuard A M m role allow rawCost body) :
    EmitsNode valid hist (JobGuard A M m allow cost) r ptr before next :=
  dispatcher_emitsNode tag linked tagCell resident charge
    (emitsNode_of_read valid hist _ (handlers role) r ptr before next steps effect)

end Term

section Leaf

variable {P : SiteParsers f N} {ptr : N.Site → ℕ × ℕ} {input : Packets N}
    (tag : ∀ v, NodeDispatch.role (m (offset + ((ptr v).1 : Word W)).val) = .leaf)

include tag

/-- The singleton cursor subtree returns exactly the body's scratch and
suffix, for successful and rejected input streams alike. -/
theorem dispatcher_leaf_subtrees
    (raw : Subtrees (handlers .leaf) valid P (fun v => leafTree (ptr v)) input) :
    Subtrees (dispatcher handlers m offset) valid P (fun v => leafTree (ptr v)) input := by
  have same (v : N.Site) (s : Scratch W endAddr) (bits : List Bool) :
      (dispatcher handlers m offset).decode [((ptr v).1 : Word W)] s bits =
        (handlers .leaf).decode [((ptr v).1 : Word W)] s bits := by
    simp only [HookParser.decode, dispatcher, tag v]
    cases hit : (handlers .leaf).read ((ptr v).1 : Word W) s bits <;> rfl
  intro v z
  have old := raw v z
  constructor
  · intro pending s bits out tail ready hit
    apply old.sound pending s bits out tail ready
    exact (same v s bits).symm.trans hit
  · intro pending s x tail ready
    obtain ⟨out, hit⟩ := old.complete pending s x tail ready
    exact ⟨out, (same v s _).trans hit⟩

variable {G histBase : Word W} {allow : ℕ → Prop} {rawCost cost : VisitPath W endAddr → Prop}
    (linked : Contains A M) (tagCell : ∀ v, allow (offset + ((ptr v).1 : Word W)).val)
    (resident : ∀ v z pending s, valid (input v z :: pending) s →
      ResidentGeometry s G offset histBase)
    (charge : ∀ v s body, rawCost body → cost (dispatchJob m offset ((ptr v).1 : Word W) s body))

include linked tagCell resident charge

/-- A leaf emits one occurrence. Adding the tag lookup preserves that
occurrence's bit code and increments, and links its path at the DFS entry. -/
theorem dispatcher_leaf_emits
    (raw : Emits valid hist (RoleJobGuard A M m .leaf allow rawCost) P input (leafJobs P ptr)) :
    Emits valid hist (JobGuard A M m allow cost) P input (leafJobs P ptr) := by
  apply leaf_emits valid hist _ P input ptr
  intro v z x pending s ready
  obtain ⟨jobs, paths⟩ := raw v z x pending s ready
  have hs := paths.realized
  simp only [leafJobs, List.forall₂_cons_left_iff, List.forall₂_nil_left_iff] at hs
  obtain ⟨body, rest, real, rfl, rfl⟩ := hs
  have guard := paths.framed body List.mem_cons_self
  exact ⟨_, dispatchJob_realizes real, ⟨rfl, paths.ready.1⟩,
    dispatchJob_guard linked (resident v z pending s ready) (tag v) (tagCell v) real.address guard
      (charge v s body), paths.remaining⟩

end Leaf

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
