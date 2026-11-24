import OAI.Computability.VPVNP.PairSimulationLeafIncidentLoad
import OAI.Computability.VPVNP.PrimedInputRAMPortCode

/-!
# Native triangular scan of the sorting fields at cursor zero

Phase and step count upwards. Each step reads one outgoing and one incoming
block from the common arc offset. Both selections depend on the cross-site
bit, equal to phase minus step. The incoming selection tests that bit against
the last cursor. Every row below is independent of the number of phases.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafSortFields

open BurstRAM PrivateRAM PrimedCounter.GuessWord CursorRouting CursorNetwork RAMLayout
open LeafIncidentLoad (Field Stored)
open LeafFieldCopy (word)
open scoped Fin.CommRing

variable {W w D H p r k : ℕ}

/-- Control locations of the triangular sorting-field traversal and its copy loops. -/
inductive Stage where
  | resetPhase | phaseTest | resetStep | stride | outgoing | incoming
  | advance | stepTest | nextStep | nextPhase
  | prepare (receive side : Bool) (i : Fin 2)
  | move (receive side : Bool) (i : Fin 5)
  deriving DecidableEq, Fintype

/-- Select an outgoing or incoming half-wire by the endpoint bit. -/
def port (receive side : Bool) : LocalPort := if receive then .incoming side else .outgoing side

/-- Place the field loader's eleven registers inside the sorting traversal. -/
def subRegs (reg : Fin 17 ↪ Fin r) : Fin 11 ↪ Fin r := (Fin.castAddEmb 6).trans reg

/-- The shared mover uses registers 0–10. The remaining registers hold D,
D−1, phase, step, stride bit and zero. -/
def instruction (pc : Stage → Fin p) (reg : Fin 17 ↪ Fin r) (done : Fin p) :
    Stage → Instr W p r k
  | .resetPhase => .constant (reg 13) 0 (pc .phaseTest)
  | .phaseTest => .jumpLt (reg 13) (reg 11) (pc .resetStep) done
  | .resetStep => .constant (reg 14) 0 (pc .stride)
  | .stride => .binary .sub (reg 15) (reg 13) (reg 14) (pc .outgoing)
  | .outgoing => .jumpEq (reg 15) (reg 16) (pc (.prepare false true 0)) (pc (.prepare false false 0))
  | .incoming => .jumpEq (reg 15) (reg 12) (pc (.prepare true true 0)) (pc (.prepare true false 0))
  | .advance => .binary .add (reg 6) (reg 6) (reg 5) (pc .stepTest)
  | .stepTest => .jumpLt (reg 14) (reg 13) (pc .nextStep) (pc .nextPhase)
  | .nextStep => .binary .add (reg 14) (reg 14) (reg 3) (pc .stride)
  | .nextPhase => .binary .add (reg 13) (reg 13) (reg 3) (pc .phaseTest)
  | .prepare recv side i =>
    LeafIncidentLoad.prepare (some (port recv side)) (pc ∘ Stage.prepare recv side)
      (subRegs reg) (pc (.move recv side 0)) i
  | .move recv side i =>
    LeafFieldCopy.instruction .resident (pc ∘ Stage.move recv side)
      (LeafIncidentLoad.copyRegs (subRegs reg)) (pc (if recv then .advance else .incoming)) i

theorem resize_instruction (pc : Stage → Fin p) (reg : Fin 17 ↪ Fin r) (done : Fin p) (s : Stage) :
    (instruction (W := 1) (k := k) pc reg done s).resize W = instruction pc reg done s := by
  cases s <;> try rfl
  case prepare recv side i => fin_cases i <;> rfl
  case move recv side i => fin_cases i <;> rfl

/-- The host table contains the sorting traversal's physical instructions. -/
def Linked (M : Machine W p r k) (pc : Stage → Fin p) (reg : Fin 17 ↪ Fin r) (done : Fin p) :=
  ∀ s, M.code (pc s) = instruction pc reg done s

/-- Start of this sorting layer's field in one half-wire payload. -/
def arcStart (l : Layer D) (H w : ℕ) := D*(8*w)+l.ordinal.val*blockBits H w

theorem fieldFits (l : Layer D) (H w : ℕ) : arcStart l H w+blockBits H w ≤ ramPayloadWidth D H w := by
  unfold arcStart ramPayloadWidth
  have h := Nat.mul_le_mul_right (blockBits H w) l.ordinal.isLt
  rw [Nat.succ_mul] at h
  omega

/-- Endpoint bit chosen for the outgoing or incoming field of a sorting layer. -/
def side (l : Layer D) (receive : Bool) : Bool := decide (l.siteBit = if receive then D-1 else 0)

/-- Bits of the selected resident sorting field. -/
def field (l : Layer D) (receive : Bool) (buf : Buffers D H w) : List Bool :=
  Field (some (port receive (side l receive))) (arcStart l H w) (blockBits H w) (fieldFits l H w) buf

@[simp] theorem field_length (l : Layer D) (receive : Bool) (buf : Buffers D H w) :
    (field l receive buf).length = blockBits H w := List.length_ofFn

/-- Concatenate a layer's outgoing field with its incoming field. -/
def block (l : Layer D) (buf : Buffers D H w) := field l false buf ++ field l true buf

@[simp] theorem block_length (l : Layer D) (buf : Buffers D H w) :
    (block l buf).length = 2*blockBits H w := by simp [block, two_mul]

/-- Index of a field-loader register in the sorting register file. -/
def index (i : Fin 11) : Fin 17 := Fin.castAdd 6 i

/-- Constant operands for a complete sorting-layer traversal. -/
structure Fixed (reg : Fin 17 ↪ Fin r) (base : LocalPort → ℕ) (D H w : ℕ) (c : Config W p r) : Prop where
  one : c.reg (reg 3) = 1
  len : c.reg (reg 5) = word W (blockBits H w)
  bases : ∀ a, c.reg (reg (index (LeafIncidentLoad.baseReg a))) = word W (base a)
  dims : c.reg (reg 11) = word W D
  last : c.reg (reg 12) = word W (D-1)
  zero : c.reg (reg 16) = 0

/-- Register operands that can change in a sorting-field scan. -/
def changed : List (Fin 17) := [0,1,2,4,6,13,14,15]

/-- Registers preserved while one sorting-field step executes. -/
def Frame (reg : Fin 17 ↪ Fin r) (c out : Config W p r) :=
  ∀ i, (∀ j ∈ changed, i ≠ reg j) → out.reg i = c.reg i

theorem Frame.trans {reg : Fin 17 ↪ Fin r} {a b c : Config W p r}
    (h : Frame reg a b) (h' : Frame reg b c) : Frame reg a c :=
  fun i hi => (h' i hi).trans (h i hi)

theorem Fixed.of_frame {reg : Fin 17 ↪ Fin r} {base D H w} {c out : Config W p r}
    (hc : Fixed reg base D H w c) (h : Frame reg c out) : Fixed reg base D H w out := by
  have keep (j : Fin 17) (hj : j ∉ changed) : out.reg (reg j) = c.reg (reg j) :=
    h _ (fun i hi => reg.injective.ne (fun eq => hj (eq ▸ hi)))
  refine ⟨(keep _ (by decide)).trans hc.one, (keep _ (by decide)).trans hc.len, ?_,
    (keep _ (by decide)).trans hc.dims, (keep _ (by decide)).trans hc.last, (keep _ (by decide)).trans hc.zero⟩
  intro port
  exact (keep _ (by cases port with | outgoing side | incoming side => cases side <;> decide)).trans (hc.bases port)

theorem frame_put {reg : Fin 17 ↪ Fin r} (c : Config W p r) (next : Fin p) (j : Fin 17)
    (v : Word W) (hj : j ∈ changed) : Frame reg c (c.put next (reg j) v) :=
  fun _ hi => Function.update_of_ne (hi j hj) _ _

theorem stored_place (base : LocalPort → ℕ) (buf : Buffers D H w) (m : Word W → Word W)
    (lo : ℕ) (bs : List Bool) (h : Stored base buf m)
    (fit : lo+bs.length ≤ 2^W) (hf : ∀ a, base a+ramPayloadWidth D H w ≤ 2^W)
    (apart : ∀ a, base a+ramPayloadWidth D H w ≤ lo ∨ lo+bs.length ≤ base a) :
    Stored base buf (LeafFieldCopy.place lo bs m) := by
  intro a i
  have hi := i.isLt
  have hh := hf a
  have hs := apart a
  rw [LeafFieldCopy.place_outside _ _ _ _ fit]
  · exact h a i
  · change (base a + i.val) % 2^W < lo ∨ lo+bs.length ≤ (base a+i.val) % 2^W
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

variable {M : Machine W p r k} {pc : Stage → Fin p} {reg : Fin 17 ↪ Fin r} {done : Fin p}

theorem step_at (hl : Linked M pc reg done) (q : Stage) (c : Config W p r) (hc : c.pc = pc q) :
    M.program.step c = (instruction pc reg done q).run M.publicData c := by simp [Machine.program, hc, hl q]

private theorem move_run (hl : Linked M pc reg done) (l : Layer D) (recv : Bool)
    (base : LocalPort → ℕ) (buf : Buffers D H w) (lo : ℕ) (c : Config W p r)
    (hc : c.pc = pc (.prepare recv (side l recv) 0)) (hf : Fixed reg base D H w c)
    (ho : c.reg (reg 6) = word W (arcStart l H w))
    (hd : c.reg (reg 2) = word W (lo+blockBits H w)) (hs : Stored base buf c.privateMem)
    (fit : lo+blockBits H w < 2^W) (sourceFit : ∀ a, base a+ramPayloadWidth D H w ≤ 2^W)
    (sep : ∀ a, base a+ramPayloadWidth D H w ≤ lo ∨ lo+blockBits H w ≤ base a) :
    ∃ out, Prefix M c (List.replicate (5*blockBits H w+3) .tick) out ∧
      out.pc = pc (if recv then .advance else .incoming) ∧ out.reg (reg 2) = word W lo ∧
      (∀ i, i ≠ reg 0 → i ≠ reg 1 → i ≠ reg 2 → i ≠ reg 4 → out.reg i = c.reg i) ∧
      out.privateMem = LeafFieldCopy.place lo (field l recv buf) c.privateMem ∧
      out.persistent = c.persistent := by
  let s := side l recv
  obtain ⟨out,pref,res⟩ := LeafIncidentLoad.copy_run M (some (port recv s))
    (pc ∘ Stage.prepare recv s) (pc ∘ Stage.move recv s) (subRegs reg)
    (pc (if recv then .advance else .incoming))
    (fun i => hl (.prepare recv s i)) (fun i => hl (.move recv s i))
    base buf (arcStart l H w) (blockBits H w) lo (fieldFits l H w) fit sep sourceFit c hc
    hf.bases hf.len ho hd hf.one hs
  exact ⟨out, pref, res.pc, res.cursor, res.frame, res.mem, res.persistent⟩

private theorem word_eq_iff {a b : ℕ} (ha : a < 2^W) (hb : b < 2^W) :
    word W a = word W b ↔ a = b := by
  constructor
  · intro h
    have he := congrArg Fin.val h
    change a % 2^W = b % 2^W at he
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at he
  · rintro rfl; rfl

private theorem move_frame (reg : Fin 17 ↪ Fin r) {c out : Config W p r}
    (h : ∀ i, i ≠ reg 0 → i ≠ reg 1 → i ≠ reg 2 → i ≠ reg 4 → out.reg i = c.reg i) :
    Frame reg c out := fun i hi => h i (hi 0 (by decide)) (hi 1 (by decide)) (hi 2 (by decide)) (hi 4 (by decide))

/-- Both physical fields of one layer, before the address and loop counters advance. -/
theorem layer_run (hl : Linked M pc reg done) (l : Layer D) (base : LocalPort → ℕ)
    (buf : Buffers D H w) (lo : ℕ) (c : Config W p r)
    (hc : c.pc = pc .stride) (hf : Fixed reg base D H w c) (hD : D < 2^W)
    (hp : c.reg (reg 13) = word W l.phase) (ht : c.reg (reg 14) = word W l.step)
    (ho : c.reg (reg 6) = word W (arcStart l H w)) (hd : c.reg (reg 2) = word W (lo+2*blockBits H w))
    (hs : Stored base buf c.privateMem) (fit : lo+2*blockBits H w < 2^W)
    (sourceFit : ∀ a, base a+ramPayloadWidth D H w ≤ 2^W)
    (sep : ∀ a, base a+ramPayloadWidth D H w ≤ lo ∨ lo+2*blockBits H w ≤ base a) :
    ∃ out, Prefix M c (List.replicate (10*blockBits H w+9) .tick) out ∧
      out.pc = pc .advance ∧ out.reg (reg 2) = word W lo ∧
      out.reg (reg 6) = c.reg (reg 6) ∧ out.reg (reg 13) = c.reg (reg 13) ∧
      out.reg (reg 14) = c.reg (reg 14) ∧ Frame reg c out ∧
      out.privateMem = LeafFieldCopy.place lo (block l buf) c.privateMem ∧ out.persistent = c.persistent := by
  let a := c.put (pc .outgoing) (reg 15) (word W l.siteBit)
  let b := {a with pc := pc (.prepare false (side l false) 0)}
  have s0 : M.program.step c = .localStep a := by
    rw [step_at hl _ c hc]
    simp [instruction,Instr.run,BinaryOp.eval,a,hp,ht,word,Layer.siteBit,Nat.cast_sub l.step_le]
  have heq : a.reg (reg 15) = a.reg (reg 16) ↔ l.siteBit = 0 := by
    simp only [a,Config.put,Function.update_self,Function.update_of_ne (reg.injective.ne (by decide : (16 : Fin 17) ≠ 15)),hf.zero]
    exact word_eq_iff (l.siteBit_lt.trans hD) (Nat.two_pow_pos W)
  have s1 : M.program.step a = .localStep b := by
    rw [step_at hl .outgoing a rfl]
    simp [instruction,Instr.run,b,side,heq]
    split <;> simp_all
  have fb : Frame reg c b := frame_put c _ 15 _ (by decide)
  have hD₁ : c.reg (reg 2) = word W (lo+blockBits H w+blockBits H w) := by
    simpa [two_mul,Nat.add_assoc] using hd
  obtain ⟨u,pu,hup,hud,ku,hu,hperu⟩ := move_run hl l false base buf (lo+blockBits H w) b rfl
    (hf.of_frame fb) (by simpa [b,a,Config.put] using ho) (by simpa [b,a,Config.put] using hD₁)
    hs (by omega) sourceFit (fun a => by have := sep a; omega)
  let d := {u with pc := pc (.prepare true (side l true) 0)}
  have fb_u : Frame reg b u := move_frame reg ku
  have fdu : Frame reg c d := fb.trans fb_u
  have hfu := hf.of_frame fdu
  have hstride : u.reg (reg 15) = word W l.siteBit := by
    rw [ku _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
      (reg.injective.ne (by decide)) (reg.injective.ne (by decide))]
    exact Config.put_same ..
  have eqr : u.reg (reg 15) = u.reg (reg 12) ↔ l.siteBit = D-1 := by
    change u.reg (reg 15) = d.reg (reg 12) ↔ _
    rw [hstride,hfu.last]
    exact word_eq_iff (l.siteBit_lt.trans hD) (by omega)
  have s2 : M.program.step u = .localStep d := by
    rw [step_at hl .incoming u hup]
    simp [instruction,Instr.run,d,side,eqr]
    split <;> simp_all
  have su : Stored base buf u.privateMem := by
    rw [hu]
    exact stored_place _ _ _ _ _ hs (by simp; omega) sourceFit (fun a => by have := sep a; simp; omega)
  have keepU (i : Fin 17) (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2) (h4 : i ≠ 4) :
      u.reg (reg i) = b.reg (reg i) := ku _ (reg.injective.ne h0) (reg.injective.ne h1)
        (reg.injective.ne h2) (reg.injective.ne h4)
  have off : d.reg (reg 6) = word W (arcStart l H w) := by
    change u.reg (reg 6) = _
    rw [keepU 6 (by decide) (by decide) (by decide) (by decide)]
    simpa [b,a,Config.put] using ho
  obtain ⟨out,pv,hvp,hvd,kv,hv,hperv⟩ := move_run hl l true base buf lo d rfl
    hfu off hud su (by omega) sourceFit (fun a => by have := sep a; omega)
  have both (i : Fin 17) (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2) (h4 : i ≠ 4) (h15 : i ≠ 15) :
      out.reg (reg i) = c.reg (reg i) := by
    rw [kv _ (reg.injective.ne h0) (reg.injective.ne h1) (reg.injective.ne h2) (reg.injective.ne h4)]
    change u.reg (reg i) = _
    rw [keepU _ h0 h1 h2 h4]
    exact Function.update_of_ne (reg.injective.ne h15) _ _
  refine ⟨out, ?_, hvp, hvd, both _ (by decide) (by decide) (by decide) (by decide) (by decide),
    both _ (by decide) (by decide) (by decide) (by decide) (by decide),
    both _ (by decide) (by decide) (by decide) (by decide) (by decide),
    fdu.trans (move_frame reg kv), ?_, hperv.trans hperu⟩
  · have pre : Prefix M c (List.replicate 2 .tick) b := .tick s0 (.tick s1 (.nil _))
    have mid : Prefix M u (List.replicate 1 .tick) d := .tick s2 (.nil _)
    convert pre.append (pu.append (mid.append pv)) using 1
    repeat rw [← List.replicate_add]
    congr 1; omega
  · rw [hv]
    change LeafFieldCopy.place lo (field l true buf) u.privateMem = _
    rw [hu,block,LeafIncidentLoad.place_append,field_length]
    rfl

end PairSimulation.LeafSortFields

end VPVNP
end Computability
end OAI
