import OAI.Computability.VPVNP.PairSimulationLeafPlacement
import OAI.Computability.VPVNP.PrivateRAMRegisterOperands

/-! # The eleven-public-word leaf segment of the final-vertex program -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafRole

open BurstRAM PrivateRAM RegisterOperands
open scoped Classical

set_option maxRecDepth 4000

variable {p r w : ℕ} (pc : Label → Fin p) (dfs : Fin 9 ↪ Fin r) (priv : Private ↪ Fin r)
  (apart : Apart dfs priv) (ret : Fin p)

/-- The ten operand values appear in private registers on the native machine.
The caller's original eleven public words occupy the other side of the
verification machine's public bank. -/
def operands : Fin (10+11) → Operand r 11 :=
  Fin.addCases (fun i => .register (values priv i)) Operand.public

/-- The position of a leaf operand in the ten geometry slots preceding the eleven original
vertex operands. -/
def pubSlot (j : LeafImage.Pub) : Fin (10+11) := (LeafGeometryLoad.slot j).castAdd 11

/-- A verifier body instruction with its registers placed in the host, calls directed to leaf
body labels and returns directed to the caller. -/
noncomputable def body (j : LeafImage.Label) : Instr 5 (p+p) r (10+11) :=
  LeafImage.instruction (enter ∘ bodyPC pc) (bodyReg dfs priv apart) pubSlot (caller ret) j

/-- Physical rows emit only register copies for the ten geometry fields. -/
noncomputable def instruction : Label → Instr 5 p r 11
  | .inl j => LeafGeometryLoad.instruction (loadPC pc) dfs (ports priv) (priv .cursor) (bodyPC pc (.address 0)) j
  | .inr j => translate fold (operands priv) (body pc dfs priv apart ret j)

attribute [local irreducible] labelCount privateCount
private noncomputable def segmentRow (place : Fin labelCount → Fin p) (dfs : Fin 9 ↪ Fin r)
    (fresh : Fin privateCount ↪ Fin r) (ret : Fin p) (i : Fin labelCount) : Instr 5 p r 11 :=
  let priv := privateIndex.toEmbedding.trans fresh
  if h : Apart dfs priv then instruction (place ∘ labelIndex) dfs priv h ret (labelIndex.symm i) else .reject

/-- The actual disjoint placement supplied by the vertex table uses the body
and geometry rows. An aliased placement outside that ABI rejects. -/
noncomputable abbrev segment : VertexImage.Segment where
  count := labelCount
  privateRegs := privateCount
  entry := labelIndex (.inl (.inl ()))
  row place dfs _ fresh ret i := segmentRow place dfs fresh ret i

private theorem segment_count : segment.count = labelCount := rfl

private theorem segment_regs : segment.privateRegs = privateCount := rfl

-- Explicit transports let the type checker compare the segment bounds directly,
-- without enumerating the finite types of leaf labels and registers.
theorem segment_row (place : Fin labelCount → Fin p) (saved : VertexImage.Saved ↪ Fin r)
    (fresh : Fin privateCount ↪ Fin r) (h : Apart dfs (privateIndex.toEmbedding.trans fresh))
    (j : Label) :
    segment.row (p := p) (r := r) (place ∘ Fin.cast segment_count) dfs saved
      ((finCongr segment_regs).toEmbedding.trans fresh) ret
      (Fin.cast segment_count.symm (labelIndex j)) =
      instruction (place ∘ labelIndex) dfs (privateIndex.toEmbedding.trans fresh) h ret j := by
  change segmentRow place dfs fresh ret (labelIndex j) = _
  unfold segmentRow
  rw [dite_eq_left h,labelIndex.symm_apply_apply]

/-- The eleven-operand host machine contains every leaf instruction at the chosen label and
resized to its word width. -/
def Contains (A : Machine w p r 11) : Prop :=
  ∀ j, A.code (pc j) = (instruction pc dfs priv apart ret j).resize w

theorem load_linked {A : Machine w p r 11} (h : Contains pc dfs priv apart ret A)
    (i : LeafGeometryLoad.Label) :
    A.code (loadPC pc i) = LeafGeometryLoad.instruction (loadPC pc) dfs (ports priv) (priv .cursor)
      (bodyPC pc (.address 0)) i :=
  (h (.inl i)).trans (LeafGeometryLoad.resize_instruction ..)

/-- Host addresses of the leaf body, after its geometry reload. -/
def inside := Set.range (bodyPC pc)

noncomputable instance : DecidablePred (inside pc) := fun _ => Classical.propDecidable _

/-- Verifier body code at a placed leaf-body label, with rejection at indices outside that
body. -/
noncomputable def text (i : Fin p) : Instr w (p+p) r (10+11) :=
  if h : inside pc i then (body pc dfs priv apart ret h.choose).resize w else .reject

theorem text_at (inj : Function.Injective pc) (j : LeafImage.Label) :
    text pc dfs priv apart ret (bodyPC pc j) = (body pc dfs priv apart ret j).resize w := by
  have h : inside pc (bodyPC pc j) := ⟨j,rfl⟩
  have eqn : h.choose = j := Sum.inr.inj (inj h.choose_spec)
  simp [text,h,eqn]

variable (A : Machine w p r 11) (data : Fin 10 → Word w)

/-- Prepend the ten loaded geometry words to the eleven public operands of the host vertex
machine. -/
def publicData : Fin (10+11) → Word w := Fin.addCases data A.publicData

/-- The shadow machine that executes the leaf body using the extended operand table and
preserves access to the host caller. -/
noncomputable def verification : Machine w (p+p) r (10+11) :=
  shadow A (inside pc) (text pc dfs priv apart ret) (publicData A data) (Fin.natAdd 10)

theorem verification_linked (inj : Function.Injective pc) :
    LeafImage.Linked (enter ∘ bodyPC pc) (bodyReg dfs priv apart) pubSlot (caller ret)
      (verification pc dfs priv apart ret A data) := by
  apply LeafImage.linked
  intro j
  change (shadow ..).code (enter (bodyPC pc j)) = _
  rw [shadow_code_enter _ _ _ _ _ _ (show inside pc (bodyPC pc j) from ⟨j,rfl⟩)]
  exact text_at pc dfs priv apart ret inj j

theorem physical_rows (inj : Function.Injective pc) (h : Contains pc dfs priv apart ret A)
    (i : Fin p) (hi : inside pc i) :
    A.code i = translate fold (operands priv) (text pc dfs priv apart ret i) := by
  rcases hi with ⟨j,rfl⟩
  rw [text_at pc dfs priv apart ret inj j]
  exact (h (.inr j)).trans (translate_resize ..)

theorem agreement (c : Config w p r) (h : ∀ i, c.reg (values priv i) = data i) :
    Agrees (operands priv) (publicData A data) A.publicData c.reg := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [operands,publicData,Fin.addCases_left,Operand.value] using h j
  · simp only [operands,publicData,Fin.addCases_right,Operand.value]

end PairSimulation.LeafRole

end VPVNP
end Computability
end OAI
