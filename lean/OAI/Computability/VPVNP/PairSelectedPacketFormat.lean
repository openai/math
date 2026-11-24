import OAI.Computability.VPVNP.PairIndexedLevelChecks
import OAI.Computability.VPVNP.PairShrinkRoleDirectory

/-!
# Typed packets at all rows of a selected traversal

A genuine packet consists of an actual row header and a half-wire value
encoded in that row's state. This remains a finite union of genuine row
formats when the tape after the current vertex is arbitrary.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open NetworkKernel CompressorRecords LocalHistory NodeArguments
open Compression TraversalRows TraversalRoles
open private collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels
open private row_address from OAI.Computability.VPVNP.PairShrinkRoleDirectory
open private ptr_bounds from OAI.Computability.VPVNP.PairTraversalDisjoint

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
    {B : S.Templates} {f : B.Entry → R} {hf : B.IsSolution f}

/-- The packet pairs a site's row-header address in the supplied order with the encoded bits of
a half-wire assignment at that same site. -/
def AtRow {N : Network} (cap base : ℕ) (o : Order N.Site) (bits : ∀ v, N.Half v → List Bool)
    (q : Packet) : Prop := ∃ u z, q = ⟨(sitePointers cap base o u).1, bits u z⟩

private theorem atRow_cast {N Y : Network} (e : N = Y) (cap base : ℕ) (o : Order Y.Site)
    (bits : ∀ v, Y.Half v → List Bool) (q : Packet) :
    AtRow cap base (e.symm ▸ o : Order N.Site) (pullBits e bits) q ↔ AtRow cap base o bits q := by
  cases e; rfl

/-- Each packet witnesses a concrete site and half assignment in the
initial state or the true output state of one selected pass. -/
def PacketFormat {a g : ℕ} (X : State a g) (cap base : ℕ) (leaf : TaggedLayer)
    (passes : List (SelectedLevel B f hf)) (q : Packet) : Prop :=
  AtRow cap base (siteOrder X) (packed X) q ∨
    ∃ i : Fin passes.length, let v := passes[i]
      let p := v.pass.next v.term
      AtRow cap (layerBase cap base (leaf :: ShrinkRoleDirectory.outputTags passes) (i.val + 1))
        (siteOrder p) (packed p) q

theorem PacketFormat.output {a g : ℕ} (X : State a g) (cap base : ℕ) (leaf : TaggedLayer)
    (passes : List (SelectedLevel B f hf)) (i : Fin passes.length) :
    let v := passes[i]
    let pos := layerBase cap base (leaf :: ShrinkRoleDirectory.outputTags passes) (i.val + 1)
    ∀ u z, PacketFormat X cap base leaf passes
      ⟨(sitePointers cap pos (ShrinkRoleDirectory.outputOrder v) u).1,
        pullBits (v.pass.output_eq v.term) (packed (v.pass.next v.term)) u z⟩ := by
  intro v pos u z
  exact Or.inr ⟨i,(atRow_cast (v.pass.output_eq v.term) cap pos _ _ _).mp ⟨u,z,rfl⟩⟩

/-- The format provides the exact typed input of a heterogeneous physical
row parser. In the second case the dependent pair identifies both the pass
occurrence and its site, using the shared directory's native address. -/
theorem PacketFormat.cases {a g : ℕ} {X : State a g} {cap base : ℕ} {leaf : TaggedLayer}
    {passes : List (SelectedLevel B f hf)} {q : Packet}
    (h : PacketFormat X cap base leaf passes q) :
    AtRow cap base (siteOrder X) (packed X) q ∨
      ∃ x : ShrinkRoleDirectory.Site passes,
        ∃ z : (passes[x.1].pass.step.term passes[x.1].term).output.Half x.2,
        q = ⟨ShrinkRoleDirectory.address cap base leaf passes x,
          pullBits (passes[x.1].pass.output_eq passes[x.1].term)
            (packed (passes[x.1].pass.next passes[x.1].term)) x.2 z⟩ := by
  rcases h with h | ⟨i,h⟩
  · exact Or.inl h
  · let v := passes[i]
    obtain ⟨u,z,e⟩ := (atRow_cast (v.pass.output_eq v.term) cap _ _ _ q).mpr h
    exact Or.inr ⟨⟨i,u⟩,z,e⟩

/-- All formatted packets fit in the published row region. This is an
address bound before converting the natural header to a machine word. -/
theorem PacketFormat.node_lt {a g : ℕ} {X : State a g} {cap base : ℕ} {leaf : TaggedLayer}
    {passes : List (SelectedLevel B f hf)} {q : Packet} (h : PacketFormat X cap base leaf passes q)
    (count : leaf.layer.count = (siteOrder X).length) :
    q.node < layerBase cap base (leaf :: ShrinkRoleDirectory.outputTags passes)
      (passes.length + 1) := by
  let outs := ShrinkRoleDirectory.outputTags passes
  rcases h.cases with ⟨u,z,rfl⟩ | ⟨x,z,rfl⟩
  · have low := (ptr_bounds (siteOrder X) cap base u).2
    have eqn : layerBase cap base (leaf::outs) 1 = address cap base (siteOrder X).length := by
      rw [layerBase_cons,layerBase_zero,endPos,count]
    exact low.trans_le (eqn ▸ VertexLevelBounds.layerBase_mono cap base (leaf::outs)
      (Nat.le_add_left 1 passes.length))
  · have below := OutputRowDirectory.rowAddress_lt_end cap base leaf outs
      (ShrinkRoleDirectory.siteRows passes x)
    rw [row_address] at below
    simpa only [outs,ShrinkRoleDirectory.outputTags,List.length_map] using below

private theorem extendFormat {a g : ℕ} {X : State a g} (cap base : ℕ) (leaf : TaggedLayer)
    (cur : SelectedLevel B f hf) (rest : List (SelectedLevel B f hf)) {q : Packet}
    (h : PacketFormat (cur.pass.next cur.term) cap (endPos cap base leaf.layer)
      ⟨levelLayer B f hf cur, tagLevel B f hf cur⟩ rest q) :
    PacketFormat X cap base leaf (cur::rest) q := by
  rcases h with h | ⟨i,h⟩
  · refine Or.inr ⟨0,?_⟩
    change AtRow cap (layerBase cap base
      (leaf :: ShrinkRoleDirectory.outputTags (cur::rest)) (0+1)) _ _ q
    rw [layerBase_cons,layerBase_zero]
    exact h
  · refine Or.inr ⟨i.succ,?_⟩
    simpa only [Fin.getElem_fin,Fin.val_succ,List.getElem_cons_succ,layerBase_cons,
      ShrinkRoleDirectory.outputTags,List.map_cons] using h

private def stateRow {a g : ℕ} (X : State a g) (cap base : ℕ) (q : Packet) : Prop :=
  AtRow (N := X.network) cap base (siteOrder X) (packed X) q

private def formatInputs {a g b n : ℕ} (X : State a g) (Y : State b n) (cap base : ℕ)
    (leaf : TaggedLayer)
    (passes : List (SelectedLevel B f hf)) : Prop :=
  let pos := layerBase cap base (leaf :: ShrinkRoleDirectory.outputTags passes)
  (∀ i : Fin passes.length, ∀ q, stateRow passes[i].input cap (pos i.val) q →
    PacketFormat X cap base leaf passes q) ∧
    ∀ q, stateRow Y cap (pos passes.length) q → PacketFormat X cap base leaf passes q

section

attribute [local irreducible] stateRow

private theorem prependInputs {b n : ℕ} (Y : State b n) (cap base : ℕ) (leaf : TaggedLayer)
    (cur : SelectedLevel B f hf) (vs : List (SelectedLevel B f hf))
    (later : formatInputs (cur.pass.next cur.term) Y cap (endPos cap base leaf.layer)
      ⟨levelLayer B f hf cur, tagLevel B f hf cur⟩ vs) :
    formatInputs cur.input Y cap base leaf (cur::vs) := by
  constructor
  · intro i
    cases i using Fin.cases with
    | zero =>
      intro q h
      rw [Fin.val_zero,layerBase_zero] at h
      exact Or.inl (by unfold stateRow at h; exact h)
    | succ i =>
      intro q h
      apply extendFormat cap base leaf cur vs
      apply later.1 i q
      simpa only [Fin.val_succ,Fin.getElem_fin,List.getElem_cons_succ,layerBase_cons,
        ShrinkRoleDirectory.outputTags,List.map_cons] using h
  · intro q h
    apply extendFormat cap base leaf cur vs
    apply later.2 q
    simpa only [List.length_cons,layerBase_cons,ShrinkRoleDirectory.outputTags,
      List.map_cons] using h

private theorem collect_format {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (K : E.MapWitnesses f) (r : ExecutionReaders E K) (o : PassOrigins B f hf E) (z : E.Choices)
    (cap base : ℕ) (leaf : TaggedLayer) :
    formatInputs X (E.finalState z) cap base leaf (collectLevels B f hf E K r o z) := by
  induction E generalizing leaf base with
  | done =>
    cases z
    refine ⟨fun i => Fin.elim0 i,fun q h => Or.inl ?_⟩
    simp only [collectLevels,List.length_nil,layerBase_zero,StateExecution.finalState] at h
    unfold stateRow at h
    exact h
  | @more a g a' g' X p tail ih =>
    let cur : SelectedLevel B f hf := ⟨a,g,a',g',X,p,o.1,z.1,r.1.select.encode z.1⟩
    exact prependInputs ((tail z.1).finalState z.2) cap base leaf cur _
      (ih z.1 (K.2 z.1) (r.2 z.1) (o.2 z.1) z.2 (endPos cap base leaf.layer) _)

end

variable (B f hf) {n : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute f hf T hT X).Choices) (base : ℕ)

/-- Packet format for the chosen execution branch at the template's record limit. Its row and
payload come from either the initial cursor layer or an output layer of a selected pass. -/
abbrev SelectedPacketFormat := PacketFormat X B.recordLimit base ⟨leafLayer (siteOrder X),.cursor⟩
  (executeLevels B f hf T hT X z)

/-- Both the old half packets guessed at a physical level and the real
terminal root packet at the final layer have the selected format. -/
theorem selected_format :
    let passes := executeLevels B f hf T hT X z
    let tags := selected B f hf T hT X z
    let Y := (B.execute f hf T hT X).finalState z
    (∀ i : Fin passes.length, ∀ q, AtRow B.recordLimit (layerBase B.recordLimit base tags i.val)
      (siteOrder passes[i].input) (packed passes[i].input) q →
        SelectedPacketFormat B f hf T hT X z base q) ∧
    ∀ q, AtRow B.recordLimit (layerBase B.recordLimit base tags passes.length)
      (siteOrder Y) (packed Y) q →
      SelectedPacketFormat B f hf T hT X z base q :=
  collect_format (B := B) (f := f) (hf := hf) (B.execute f hf T hT X) _
    (repeatReaders (blockReaders B f hf) _ T n (Nat.add_sub_of_le hT).symm X)
    (executeOrigins B f hf T hT X) z B.recordLimit base ⟨leafLayer (siteOrder X),.cursor⟩

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
