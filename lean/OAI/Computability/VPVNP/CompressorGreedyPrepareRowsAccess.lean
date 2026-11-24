import OAI.Computability.VPVNP.CompressorRecordGreedyInit
import OAI.Computability.VPVNP.CompressorSourceTransport

/-!
# External addresses of greedy row preparation

Each row reads the chosen incidence's mate and then writes the operand
addresses in order. The addresses written into the row may name shifts or
labels. The preparer itself only accesses the two mate arrays and its own
consecutive destination cells.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Greedy.PrepareAccess

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression SourceTransport

open private valueCode packed_eq mate_trace emit_trace emit_list regValue next_val from
  OAI.Computability.VPVNP.CompressorRecordGreedyInit

variable {V : Type*} {N w d : ℕ}

private theorem split_trace {r k : ℕ} {pub : Fin k → Word w} {s : Word w} {left right : List (Op r k)}
    {rs mid last : Regs w r} {m midMem finalMem : Memory w} {es logs : List (Event w)}
    (h₁ : trace pub s left rs m = some (es,mid,midMem))
    (h : trace pub s (left++right) rs m = some (logs,last,finalMem)) :
    ∃ fs, trace pub s right mid midMem = some (fs,last,finalMem) ∧ logs = es++fs := by
  rw [trace_append,h₁] at h
  simp only [Option.bind_some, Option.map_eq_some_iff] at h
  obtain ⟨⟨fs,last',final'⟩,ht,he⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj he
  exact ⟨fs,ht,rfl⟩

private theorem operand (s : Word w) (m : Memory w) (rs : Regs w 13) (a : Operand d)
    (rd : ℕ → Prop) {es out m'} (run : trace (slotNumbers w d) s (emitOperand a) rs m = some (es,out,m')) :
    Reads rd es ∧ Writes (fun z ↦ z = (rs 1).val) es := by
  have ht := congrArg (Option.map Prod.fst) run
  cases a
  case' increment remote i => cases remote
  all_goals simp (config := {decide := true}) [trace, Op.effect, valueCode, emitOperand,
    BinaryOp.eval, Function.update] at ht
  all_goals rw [← ht]
  all_goals simp [Reads, Writes, List.mem_cons, Event.write.injEq]

private theorem operands (s : Word w) (m : Memory w) (rs : Regs w 13) (one : rs 11 = 1)
    (args : List (Operand d)) (rd : ℕ → Prop) (fit : (rs 1).val+args.length < 2^w)
    {es out m'} (run : trace (slotNumbers w d) s (args.flatMap emitOperand) rs m = some (es,out,m')) :
    Reads rd es ∧ Writes (fun z ↦ (rs 1).val ≤ z ∧ z < (rs 1).val+args.length) es := by
  induction args generalizing m rs es out m' with
  | nil =>
    have h : es = [] := (Prod.mk.inj (Option.some.inj run)).1.symm
    simp [h, Reads, Writes]
  | cons a args ih =>
    obtain ⟨head,mid,hh,_,_,hd,keep⟩ := emit_trace s m rs one a
    obtain ⟨tail,ht,rfl⟩ := split_trace hh run
    have hv : (mid 1).val = (rs 1).val+1 := hd ▸ next_val (rs 1) (by simp at fit; omega)
    have h₁ := operand s m rs a rd hh
    have h₂ := ih _ mid ((keep 11 (by decide) (by decide) (by decide)).trans one)
      (by simp only [List.length_cons] at fit; omega) ht
    constructor
    · intro x v h
      exact (List.mem_append.mp h).elim (h₁.1 x v) (h₂.1 x v)
    · intro x v h
      simp only [List.length_cons]
      rcases List.mem_append.mp h with hx | hx
      · have := h₁.2 x v hx
        omega
      · have := h₂.2 x v hx
        omega

private theorem mate (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N)
    (s : Word w) (x : V) (t : Bool × Fin d) (m : Memory w) (dest : Word w) (rs : Regs w 13)
    (h : RowInput T (vertexNumber order x) dest rs) (rep : T.Represents G order m)
    (rd wr : ℕ → Prop)
    (cells : ∀ e : V × Fin d, ∀ b ∈ [T.outgoing,T.incoming], rd (b+portNumber order e).val)
    {es out m'} (run : trace (slotNumbers w d) s (loadMate t.1 t.2) rs m = some (es,out,m')) :
    Reads rd es ∧ Writes wr es := by
  have ht := congrArg (Option.map Prod.fst) run
  obtain ⟨b,i⟩ := t
  have packed := packed_eq rep x i
  cases b
  all_goals simp (config := {decide := true}) [loadMate, trace, Op.effect, BinaryOp.eval,
    Function.update, h.vertex, h.degree, h.outgoing, h.incoming, packed] at ht
  all_goals rw [← ht]
  all_goals constructor
  all_goals intro a v ha
  all_goals simp only [List.mem_cons, List.not_mem_nil, Event.read.injEq, reduceCtorEq,
    false_or, or_false] at ha
  all_goals first
    | exact ha.elim
    | obtain ⟨ha,_⟩ := ha; subst a; exact cells (x,i) _ (by simp)

private theorem row (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N) (s : Word w)
    (x : V) (t : Bool × Fin d) (args : List (Operand d)) (m : Memory w) (dest : Word w) (rs : Regs w 13)
    (h : RowInput T (vertexNumber order x) dest rs) (rep : T.Represents G order m)
    (fit : dest.val+args.length < 2^w) (rd : ℕ → Prop)
    (cells : ∀ e : V × Fin d, ∀ b ∈ [T.outgoing,T.incoming], rd (b+portNumber order e).val)
    {es out m'} (run : trace (slotNumbers w d) s (initRow t args) rs m = some (es,out,m')) :
    Reads rd es ∧ Writes (fun z ↦ dest.val ≤ z ∧ z < dest.val+args.length) es := by
  obtain ⟨head,mid,hh,_,_,hi,h₁,_⟩ := mate_trace T G order m rep s dest rs x t h
  obtain ⟨tail,ht,rfl⟩ := split_trace hh run
  let wr := fun z ↦ dest.val ≤ z ∧ z < dest.val+args.length
  have hhead := mate T G order s x t m dest rs h rep rd wr cells hh
  have htail := operands s m mid h₁ args rd (hi.dest ▸ fit) ht
  rw [hi.dest] at htail
  exact ⟨fun a v ha ↦ (List.mem_append.mp ha).elim (hhead.1 a v) (htail.1 a v),
    fun a v ha ↦ (List.mem_append.mp ha).elim (hhead.2 a v) (htail.2 a v)⟩

/-- The complete initializer reads only at directed mate cells and writes
only in the half-open interval of the actual row words. -/
theorem rows (T : PortTables w) (G : SlotGraph V d) (order : V ≃ Fin N) (s : Word w)
    (x : V) (rows : OperandRows d) (m : Memory w) (dest : Word w) (rs : Regs w 13)
    (h : RowInput T (vertexNumber order x) dest rs) (rep : T.Represents G order m)
    (fit : dest.val+(rowWords T G order x rows).length < 2^w)
    (free : T.Free (d := d) order dest.val (rowWords T G order x rows).length)
    (rd : ℕ → Prop) (cells : ∀ e : V × Fin d, ∀ b ∈ [T.outgoing,T.incoming], rd (b+portNumber order e).val)
    {es out m'} (run : trace (slotNumbers w d) s (initRows rows) rs m = some (es,out,m')) :
    Reads rd es ∧ Writes (fun z ↦ dest.val ≤ z ∧ z < dest.val+(rowWords T G order x rows).length) es := by
  induction rows generalizing m dest rs es out m' with
  | nil =>
    have hnil : es = [] := (Prod.mk.inj (Option.some.inj run)).1.symm
    simp [hnil, Reads, Writes]
  | cons one tail ih =>
    obtain ⟨t,args⟩ := one
    let words := args.map (operandAddress T G order x t)
    let rest := rowWords T G order x tail
    have hwords : (rowWords T G order x ((t,args)::tail)).length = words.length+rest.length :=
      List.length_append
    rw [hwords] at fit free ⊢
    have len : words.length = args.length := List.length_map _
    have hd : (advance dest words.length).val = dest.val+words.length := advance_val _ _ (by omega)
    have left : T.Free (d := d) order dest.val words.length := by
      intro e b hb
      have := free e b hb
      omega
    have right : T.Free (d := d) order (advance dest words.length).val rest.length := by
      intro e b hb
      have := free e b hb
      omega
    obtain ⟨head,mid,hh,_,_,hmid⟩ := initRow_trace T G order m rep s dest rs x t h args
    obtain ⟨next,ht,rfl⟩ := split_trace hh run
    have hhead := row T G order s x t args m dest rs h rep (by omega) rd cells hh
    have htail := ih (writeRow m dest words) (advance dest words.length) mid (len ▸ hmid)
      (keep_tables T G order m dest words (by omega) rep left)
      (by change (advance dest words.length).val+rest.length < _; omega) right ht
    constructor
    · intro a v ha
      exact (List.mem_append.mp ha).elim (hhead.1 a v) (htail.1 a v)
    · intro a v ha
      rcases List.mem_append.mp ha with h₁ | h₂
      · have := hhead.2 a v h₁
        omega
      · have hv := htail.2 a v h₂
        change (advance dest words.length).val ≤ a.val ∧ a.val < (advance dest words.length).val+rest.length at hv
        omega

end CompressorRecords.Greedy.PrepareAccess

end VPVNP
end Computability
end OAI
