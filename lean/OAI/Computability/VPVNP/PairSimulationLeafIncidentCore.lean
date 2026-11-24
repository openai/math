import OAI.Computability.VPVNP.PairSimulationLeafSuccessorFields
import OAI.Computability.VPVNP.PairSimulationLeafSuccessorBits
import OAI.Computability.VPVNP.PairSimulationLeafSortStream

/-!
# The full native incident decoder for a cursor-zero leaf

The two chain fields are loaded first. Two arithmetic rows switch the
source offset and field width to the sorting layout, followed by the
triangular layer scan. All three subgraphs share a descending destination
cursor, so the resulting stack has the logical order of the virtual RAM
validator even when the supplied halves disagree.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafIncidentCore

open BurstRAM PrivateRAM CursorRouting CursorNetwork RAMLayout PrimedCounter.GuessWord
open LeafFieldCopy (word)
open scoped Fin.CommRing

variable {W D H w p r k : ℕ}

/-- Successor-field stages, setup instructions and sorting-field stages. -/
abbrev Stage := LeafSuccessorFields.Stage ⊕ (Fin 2 ⊕ LeafSortFields.Stage)

/-- Embed the successor loader in the thirty-register incident machine. -/
def successorRegs (reg : Fin 30 ↪ Fin r) : Fin 20 ↪ Fin r := (Fin.castAddEmb 10).trans reg

/-- Sorting counters reuse the three successor-class temporaries. -/
def sortMap : Fin 17 ↪ Fin 30 := ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,17,18,19,16], by decide⟩
/-- Embed the sorting loader in the thirty-register incident machine. -/
def sortRegs (reg : Fin 30 ↪ Fin r) := sortMap.trans reg

/-- The row that loads the indicated successor or sorting field. -/
def instruction (pc : Stage → Fin p) (reg : Fin 30 ↪ Fin r) (done : Fin p) : Stage → Instr W p r k
  | .inl s => LeafSuccessorFields.instruction (pc ∘ Sum.inl) (successorRegs reg) (pc (.inr (.inl 0))) s
  | .inr (.inl i) =>
    (![.binary .mul (reg 6) (reg 11) (reg 5) (pc (.inr (.inl 1))),
       .copy (reg 5) (reg 25) (pc (.inr (.inr .resetPhase)))] : Fin 2 → Instr W p r k) i
  | .inr (.inr s) => LeafSortFields.instruction (pc ∘ Sum.inr ∘ Sum.inr) (sortRegs reg) done s

theorem resize_instruction (pc : Stage → Fin p) (reg : Fin 30 ↪ Fin r) (done : Fin p) (s : Stage) :
    (instruction (W := 1) (k := k) pc reg done s).resize W = instruction pc reg done s := by
  rcases s with s | i | s
  · exact LeafSuccessorFields.resize_instruction ..
  · fin_cases i <;> rfl
  · exact LeafSortFields.resize_instruction ..

/-- The incident core's relocatable instruction rows occur in the host table. -/
def Linked (M : Machine W p r k) (pc : Stage → Fin p) (reg : Fin 30 ↪ Fin r) (done : Fin p) :=
  ∀ s, M.code (pc s) = instruction pc reg done s

/-- Registers that the incident core may write. -/
def changed : List (Fin 30) := [0,1,2,4,5,6,17,18,19]
/-- Equality of every register outside the core's write footprint. -/
def Frame (reg : Fin 30 ↪ Fin r) (c out : Config W p r) :=
  ∀ i, (∀ j ∈ changed, i ≠ reg j) → out.reg i = c.reg i

private theorem successor_change : ∀ j ∈ LeafSuccessorFields.changed, Fin.castAdd 10 j ∈ changed := by decide
private theorem sort_change : ∀ j ∈ LeafSortFields.changed, sortMap j ∈ changed := by decide

/-- Instruction count for the successor and sorting field loads at this site. -/
def ticks (v : Site D) (H w : ℕ) :=
  LeafSuccessorFields.ticks v w+2+(3+LeafSortFields.streamTicks D H w 0 (layerCount D) (by simp))

variable [NeZero D]

theorem stream_eq (v : Site D) (buf : Buffers D H w) :
    (LeafSuccessorFields.succBits false v buf ++ LeafSuccessorFields.succBits true v buf) ++
        LeafSortFields.stream buf 0 (layerCount D) (by simp) = List.ofFn (incidentBuffer (0,v) buf) := by
  rw [LeafSuccessorFields.succBits_eq,LeafSuccessorFields.succBits_eq,
    LeafSortFields.stream_eq_fields, ← RAMTape.SortSchedule.exchangeNumbers 0 D]
  exact (RAMTape.SortSchedule.incident_stream 0 (incidentBuffer (0,v) buf)).symm

/-- The materialized incident stack and exact physical continuation of the core. -/
structure Result (reg : Fin 30 ↪ Fin r) (done : Fin p) (lo : ℕ) (v : Site D) (buf : Buffers D H w)
    (c out : Config W p r) : Prop where
  pc : out.pc = done
  cursor : out.reg (reg 2) = word W lo
  frame : Frame reg c out
  memory : out.privateMem = LeafFieldCopy.place lo (List.ofFn (incidentBuffer (0,v) buf)) c.privateMem
  persistent : out.persistent = c.persistent

theorem run (M : Machine W p r k) (pc : Stage → Fin p) (reg : Fin 30 ↪ Fin r) (done : Fin p)
    (hl : Linked M pc reg done) (base : LocalPort → ℕ) (buf : Buffers D H w)
    (v : Site D) (lo : ℕ) (c : Config W p r) (hc : c.pc = pc (.inl .sendNext))
    (hf : LeafSuccessorFields.Fixed (successorRegs reg) base v w c)
    (hblock : c.reg (reg 25) = word W (blockBits H w)) (hDW : D < W)
    (hd : c.reg (reg 2) = word W (lo+width D H w)) (stored : LeafIncidentLoad.Stored base buf c.privateMem)
    (fit : lo+width D H w < 2^W) (sourceFit : ∀ a, base a+ramPayloadWidth D H w ≤ 2^W)
    (apart : ∀ a, base a+ramPayloadWidth D H w ≤ lo ∨ lo+width D H w ≤ base a) :
    (ticks v H w ≤ 80*w+6*D+29+layerCount D*(10*blockBits H w+14)) ∧
      ∃ out, Prefix M c (List.replicate (ticks v H w) .tick) out ∧ Result reg done lo v buf c out := by
  let lower := lo+layerCount D*(2*blockBits H w)
  have split : lower+16*w = lo+width D H w := by dsimp [lower,width]; ring
  have lower_le : lo ≤ lower := Nat.le_add_right ..
  obtain ⟨a,first,ra⟩ := LeafSuccessorFields.pair_run (fun s => hl (.inl s)) base buf v lower c hc hf hDW
    (split ▸ hd) stored (split ▸ fit) sourceFit (fun x => by have := apart x; omega)
  have fa := hf.of_frame ra.frame
  have keepA (i : Fin r) (hi : ∀ j ∈ changed, i ≠ reg j) : a.reg i = c.reg i :=
    ra.frame i (fun j hj => hi _ (successor_change j hj))
  have ba : a.reg (reg 25) = word W (blockBits H w) := (keepA _ (by
    intro j hj; apply reg.injective.ne; intro eq; exact (show (25 : Fin 30) ∉ changed by decide) (eq ▸ hj))).trans hblock
  let b := a.put (pc (.inr (.inl 1))) (reg 6) (word W (D*(8*w)))
  let d := b.put (pc (.inr (.inr .resetPhase))) (reg 5) (word W (blockBits H w))
  have s₀ : M.program.step a = .localStep b := by
    change (M.code a.pc).run M.publicData a = _
    rw [ra.pc,hl (.inr (.inl 0))]
    have dim : a.reg (reg 11) = word W D := fa.dims
    have len : a.reg (reg 5) = word W (8*w) := fa.len
    simp [instruction,Instr.run,BinaryOp.eval,b,dim,len,word]
  have s₁ : M.program.step b = .localStep d := by
    change (M.code (pc (.inr (.inl 1)))).run M.publicData b = _
    rw [hl (.inr (.inl 1))]
    simp [instruction,Instr.run,d,b,Config.put,ba]
  have middle : Prefix M a (List.replicate 2 .tick) d := .tick s₀ (.tick s₁ (.nil _))
  have keepD (i : Fin 30) (h5 : i ≠ 5) (h6 : i ≠ 6) : d.reg (reg i) = a.reg (reg i) := by
    simp [d,b,Config.put,Function.update_of_ne (reg.injective.ne h5),Function.update_of_ne (reg.injective.ne h6)]
  have fixed : LeafSortFields.Fixed (sortRegs reg) base D H w d := by
    refine ⟨(keepD 3 (by decide) (by decide)).trans fa.one, Config.put_same .., ?_,
      (keepD 11 (by decide) (by decide)).trans fa.dims, (keepD 12 (by decide) (by decide)).trans fa.last,
      (keepD 16 (by decide) (by decide)).trans fa.zero⟩
    intro x
    have hx := fa.bases x
    cases x with
    | outgoing s | incoming s => cases s <;> exact (keepD _ (by decide) (by decide)).trans hx
  have stored' : LeafIncidentLoad.Stored base buf d.privateMem := by
    change LeafIncidentLoad.Stored base buf a.privateMem
    rw [ra.memory]
    apply LeafSortFields.stored_place _ _ _ _ _ stored _ sourceFit
    · intro x; have := apart x; simp only [List.length_append,LeafSuccessorFields.length_succBits]; omega
    · simp only [List.length_append,LeafSuccessorFields.length_succBits]; omega
  obtain ⟨n,hn,out,last,hpc,hcur,frame,hm,hper,nticks⟩ := LeafSortFields.sort_run
    (fun s => hl (.inr (.inr s))) base buf lo d rfl fixed (Nat.pos_of_ne_zero (NeZero.ne D))
    (hDW.trans Nat.lt_two_pow_self) (by change d.reg (reg 6) = _; simp [d,b,Config.put])
    ((keepD 2 (by decide) (by decide)).trans ra.cursor) stored' (by omega) sourceFit
    (fun x => by have := apart x; omega)
  have clock := LeafSuccessorFields.ticks_le v w
  refine ⟨by dsimp [ticks]; omega,out, ?_,hpc,hcur, ?_, ?_,hper.trans ra.persistent⟩
  · simpa only [ticks,← nticks,List.replicate_add,List.append_assoc] using first.append (middle.append last)
  · intro i hi
    rw [frame i (fun j hj => hi _ (sort_change j hj))]
    simp [d,b,Config.put,Function.update_of_ne (hi 5 (by decide)),Function.update_of_ne (hi 6 (by decide)),keepA i hi]
  · rw [hm]
    change LeafFieldCopy.place lo _ a.privateMem = _
    rw [ra.memory]
    conv_rhs => rw [← stream_eq v buf, LeafIncidentLoad.place_append,LeafSortFields.stream_length]

end PairSimulation.LeafIncidentCore

end VPVNP
end Computability
end OAI
