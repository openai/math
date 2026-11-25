import OAI.Hierarchy.Catalyst
import OAI.ThreeFlat.RAM.PackWordBlock
import OAI.ThreeFlat.RAM.PhysicalProcedure

namespace OAI
/-! # A finite binary advice tape for one catalyst approximation

One packed copy of the original cell table and one decoding triple per original
port suffice for all vertices of the grid. The final words store multiplication
in the same field numbering as the trivalent evaluator. -/

namespace Hierarchy.GridApproximationAdvice

open Catalyst ThreeFlat RAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {F : Type*} [Field F] [Fintype F] {k p W : ℕ} (X : Approximation F k p)

noncomputable section

abbrev portCount := Fintype.card (Port p X.width)

def header : Fin 6 → ℕ :=
  ![k,p,X.network.internal,X.network.cells,portCount X,Fintype.card F]

def rowBase (_ : Approximation F k p) := 6+k
def portBase := rowBase X+11*X.network.cells
def multBase := portBase X+3*portCount X
def wordCount := multBase X+Fintype.card F*Fintype.card F

/-- The tag is zero for an original data bit, one for a negative catalyst end,
and two for a positive catalyst end. -/
def descriptor : Port p X.width → Fin 3 → ℕ
  | .inl bit => ![0,0,bit.val]
  | .inr (⟨axis,bit⟩,side) => ![1+side.toNat,axis.val,bit.val]

private def descriptorWord (a : ℕ) : Word W :=
  if h : a/3 < portCount X then
    (descriptor X ((Fintype.equivFin (Port p X.width)).symm ⟨_,h⟩)
      ⟨a%3,Nat.mod_lt _ (by decide)⟩ : ℕ)
  else 0

variable (code : FieldCode F W)

/-- All positions used by the multiplication read are genuine indices of the
ordinary evaluator's finite field table. -/
private def productWord (a : ℕ) : Word W :=
  BitLayout.memory X.network code (fun _ => false) (fun _ => false)
    (BitLayout.mulBase (portCount X) X.network.internal X.network.cells + a)

def word (a : ℕ) : Word W :=
  if hh : a < 6 then (header X ⟨a,hh⟩ : ℕ)
  else if hw : a < rowBase X then (X.width ⟨a-6,by unfold rowBase at hw; omega⟩ : ℕ)
  else if a < portBase X then TraceTemplate.localWord X.network code (a-rowBase X)
  else if a < multBase X then descriptorWord X (a-portBase X)
  else productWord X code (a-multBase X)

def tape : Fin (W*wordCount X) → Bool := fun i => FixedTraceImage.bits (word X code) i.val

def packed (base : ℕ) (m : Memory W) : Memory W :=
  fillSegment base (wordCount X) (fun a => word X code (a-base)) m

theorem packed_at (base : ℕ) (m : Memory W) (a : ℕ) (h : a < wordCount X) :
    packed X code base m (base+a) = word X code a := by
  simp [packed,fillSegment,h]

theorem packed_outside (base : ℕ) (m : Memory W) (a : ℕ)
    (ha : a < base ∨ base+wordCount X ≤ a) : packed X code base m a = m a := by
  simp [packed,fillSegment,show ¬(base ≤ a ∧ a < base+wordCount X) by omega]

theorem packed_header (base : ℕ) (m : Memory W) (i : Fin 6) :
    packed X code base m (base+i.val) = (header X i : Word W) := by
  have h := i.isLt
  rw [packed_at X code base m _ (by unfold wordCount multBase portBase rowBase; omega)]
  simp [word,h]

theorem packed_width (base : ℕ) (m : Memory W) (j : Fin k) :
    packed X code base m (base+(6+j.val)) = (X.width j : Word W) := by
  have h : 6+j.val < rowBase X := by unfold rowBase; omega
  rw [packed_at X code base m _ (by unfold wordCount multBase portBase; omega)]
  simp [word,h]

theorem packed_row (base : ℕ) (m : Memory W) (i : Fin X.network.cells) (j : Fin 11) :
    packed X code base m (base+(rowBase X+(11*i.val+j.val))) =
      BitLayout.record X.network code i j := by
  have h : 11*i.val+j.val < 11*X.network.cells := by have := i.isLt; have := j.isLt; omega
  let a := rowBase X+(11*i.val+j.val)
  have h0 : 6 ≤ a := by dsimp [a,rowBase]; omega
  have h1 : rowBase X ≤ a := Nat.le_add_right _ _
  have h2 : a < portBase X := by dsimp [a,portBase]; omega
  have h3 : a < wordCount X := by unfold wordCount multBase; omega
  change packed X code base m (base+a) = _
  rw [packed_at X code base m a h3]
  simpa [word, Nat.not_lt.mpr h0, Nat.not_lt.mpr h1, h2, a] using
    TraceTemplate.localWord_at X.network code i j

theorem packed_port (base : ℕ) (m : Memory W) (i : Fin (portCount X)) (j : Fin 3) :
    packed X code base m (base+(portBase X+(3*i.val+j.val))) =
      (descriptor X ((Fintype.equivFin (Port p X.width)).symm i) j : Word W) := by
  have h : 3*i.val+j.val < 3*portCount X := by have := i.isLt; have := j.isLt; omega
  let a := portBase X+(3*i.val+j.val)
  have h0 : 6 ≤ a := by dsimp [a,portBase,rowBase]; omega
  have h1 : rowBase X ≤ a := by dsimp [a,portBase]; omega
  have h2 : portBase X ≤ a := Nat.le_add_right _ _
  have h3 : a < multBase X := by dsimp [a,multBase]; omega
  change packed X code base m (base+a) = _
  rw [packed_at X code base m a (by unfold wordCount; omega)]
  have hiq : (3*i.val+j.val)/3=i.val := by have := j.isLt; omega
  have hir : (3*i.val+j.val)%3=j.val := by have := j.isLt; omega
  simp [word, Nat.not_lt.mpr h0,Nat.not_lt.mpr h1,Nat.not_lt.mpr h2,h3,
    a,descriptorWord,hiq,hir]
  intro bad
  have inside : i.val < p+(∑ t,X.width t)*2 := by simpa [portCount,Port,Wire] using i.isLt
  exact (Nat.not_le_of_lt inside bad).elim


omit [Field F] [Fintype F] in
theorem data_le_size : p ≤ X.size := by
  simp [Approximation.size,Port]; omega

omit [Field F] [Fintype F] in
theorem width_le_size (j : Fin k) : X.width j ≤ X.size := by
  have total : X.width j≤∑ i, X.width i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (X.width i)) (Finset.mem_univ j)
  simpa [Approximation.size,Port,Wire] using
    (show X.width j ≤ X.network.cells+X.network.internal+
      (p+(∑ i, X.width i)*2) by omega)

theorem header_val {B : ℕ} (size : X.size ≤ B)
    (fixedPart : 6+k+Fintype.card F*Fintype.card F ≤ B) (fit : B+2 < 2^W)
    (base : ℕ) (m : Memory W) (i : Fin 6) :
    (packed X code base m (base+i.val)).val=header X i := by
  rw [packed_header,Fin.val_cast_of_lt]
  have d := (data_le_size X).trans size
  have f : Fintype.card F ≤ Fintype.card F*Fintype.card F :=
    Nat.le_mul_of_pos_right _ Fintype.card_pos
  change X.network.cells+X.network.internal+portCount X ≤ B at size
  fin_cases i <;> dsimp [header] <;> omega

theorem width_val {B : ℕ} (size : X.size ≤ B) (fit : B < 2^W)
    (base : ℕ) (m : Memory W) (j : Fin k) :
    (packed X code base m (base+(6+j.val))).val=X.width j := by
  rw [packed_width,Fin.val_cast_of_lt ((width_le_size X j).trans_lt (size.trans_lt fit))]

theorem descriptor_val {B : ℕ} (size : X.size ≤ B) (dimension : k ≤ B) (fit : B+2 < 2^W)
    (base : ℕ) (m : Memory W) (z : Port p X.width) (j : Fin 3) :
    (packed X code base m (base+(portBase X+(3*((Fintype.equivFin _) z).val+j.val)))).val =
      descriptor X z j := by
  rw [packed_port,Equiv.symm_apply_apply,Fin.val_cast_of_lt]
  rcases z with bit | ⟨⟨axis,bit⟩,side⟩
  · have d := (data_le_size X).trans size
    have := bit.isLt
    fin_cases j <;> dsimp [descriptor] <;> omega
  · have d := (width_le_size X axis).trans size
    have := bit.isLt
    have := axis.isLt
    cases side <;> fin_cases j <;> dsimp [descriptor] <;> omega

theorem packed_product (base : ℕ) (m : Memory W) (x y : F) :
    packed X code base m (base+(multBase X+(Fintype.card F*((Fintype.equivFin F) x).val+
      ((Fintype.equivFin F) y).val))) = code.encode (x*y) := by
  let q := Fintype.card F
  let ix := ((Fintype.equivFin F) x).val
  let iy := ((Fintype.equivFin F) y).val
  let a := multBase X+(q*ix+iy)
  have hx : ix+1 ≤ q := ((Fintype.equivFin F) x).isLt
  have hy : iy < q := ((Fintype.equivFin F) y).isLt
  have cap := Nat.mul_le_mul_left q hx
  rw [Nat.mul_succ] at cap
  have h0 : 6 ≤ a := by dsimp [a,multBase,portBase,rowBase]; omega
  have h1 : rowBase X ≤ a := by dsimp [a,multBase,portBase]; omega
  have h2 : portBase X ≤ a := by dsimp [a,multBase]; omega
  have h3 : multBase X ≤ a := Nat.le_add_right _ _
  have h4 : a < wordCount X := by change multBase X+(q*ix+iy) < multBase X+q*q; omega
  change packed X code base m (base+a) = _
  rw [packed_at X code base m a h4]
  simpa [word,Nat.not_lt.mpr h0,Nat.not_lt.mpr h1,Nat.not_lt.mpr h2,Nat.not_lt.mpr h3,
    a,q,ix,iy,productWord,Nat.add_assoc] using
    BitLayout.read_product X.network code (fun _ => false) (fun _ => false) x y

theorem tape_at (i : Fin (wordCount X)) (j : Fin W) :
    tape X code ⟨W*i.val+j.val,by
      have h := Nat.mul_le_mul_left W i.isLt
      rw [Nat.mul_succ] at h
      omega⟩ = (word X code i.val).val.testBit (W-1-j.val) :=
  FixedTraceImage.bits_at _ _ _

private theorem load_words {pcCount regs pubCount : ℕ} (M : Machine W pcCount regs pubCount)
    (pc : Fin 15 ↪ Fin pcCount) (reg : Fin 8 ↪ Fin regs) (pub : Fin 4 → Fin pubCount)
    (exit : Fin pcCount) (installed : (PackWordBlock.block W).Installed M pc reg pub exit)
    (src dst count : ℕ) (words : ℕ → Word W) (c : Config W pcCount regs) (m : Memory W)
    (entry : c.pc=pc (PackWordBlock.block W).first)
    (params : ∀ i, M.publicData (pub i) = (![src,dst,dst+count,W] i : ℕ))
    (apart : dst+count ≤ src ∨ src+W*count ≤ dst)
    (dstFit : dst+count < 2^W) (srcFit : src+W*count < 2^W)
    (input : ∀ i < W*count, m (src+i) = ((FixedTraceImage.bits words i).toNat : Word W)) :
    ∃ out, RAM.advance M.program (count*(5*W+6)+6) c m =
      some (out,fillSegment dst count (fun i => words (i-dst)) m) ∧ out.pc=exit := by
  have read (i : ℕ) (hi : i < count) (j : ℕ) (hj : j < W) :
      m (src+W*i+j)=(((words (dst+i-dst)).val.testBit (W-1-j)).toNat : Word W) := by
    have bound := Nat.mul_le_mul_left W hi
    rw [Nat.mul_succ] at bound
    have here := input (W*i+j) (by omega)
    simpa only [Nat.add_assoc,FixedTraceImage.bits_at words i (⟨j,hj⟩ : Fin W),
      Nat.add_sub_cancel_left] using here
  apply PackWordBoot.generate_disjoint M (PackWordBlock.headPC pc) (PackWordBlock.loopPC pc)
    reg pub exit _ _ src dst count (fun a => words (a-dst)) c m entry params apart dstFit srcFit read
  · intro i
    simpa [PackWordBlock.block,PackWordBlock.headPC] using installed (i.castAdd 10)
  · intro i
    simpa [PackWordBlock.block,PackWordBlock.loopPC] using installed (Fin.natAdd 5 i)

/-- From arbitrary registers the fixed fifteen-label, eight-register packer
mounts the entire tape and preserves every word outside the destination. -/
theorem generate {pcCount regs pubCount : ℕ} (M : Machine W pcCount regs pubCount)
    (pc : Fin 15 ↪ Fin pcCount) (reg : Fin 8 ↪ Fin regs) (pub : Fin 4 → Fin pubCount)
    (exit : Fin pcCount) (installed : (PackWordBlock.block W).Installed M pc reg pub exit)
    (src dst : ℕ) (c : Config W pcCount regs) (m : Memory W)
    (entry : c.pc=pc (PackWordBlock.block W).first)
    (params : ∀ i, M.publicData (pub i) = (![src,dst,dst+wordCount X,W] i : ℕ))
    (apart : dst+wordCount X ≤ src ∨ src+W*wordCount X ≤ dst)
    (dstFit : dst+wordCount X < 2^W) (srcFit : src+W*wordCount X < 2^W)
    (input : ∀ i, m (src+i.val) = ((tape X code i).toNat : Word W)) :
    ∃ out, RAM.advance M.program (wordCount X*(5*W+6)+6) c m =
      some (out,packed X code dst m) ∧ out.pc=exit := by
  exact load_words M pc reg pub exit installed src dst (wordCount X) (word X code) c m
    entry params apart dstFit srcFit (fun i hi => input ⟨i,hi⟩)

omit [Field F] in
theorem wordCount_le : wordCount X ≤ 11*X.size + 6+k+Fintype.card F*Fintype.card F := by
  unfold wordCount multBase portBase rowBase Approximation.size portCount
  omega

omit [Field F] in
theorem wordCount_cap {B : ℕ} (size : X.size ≤ B)
    (fixedPart : 6+k+Fintype.card F*Fintype.card F ≤ B) : wordCount X ≤ 12*B := by
  have h := wordCount_le X
  have sized := Nat.mul_le_mul_left 11 size
  omega

omit [Field F] in
/-- At the paper's native width the tape fits the advice budget, and its entire
startup takes at most 4,000 instructions per width-bit of the size bound. -/
theorem budget {B w : ℕ} (size : X.size ≤ B) (fixedPart : 6+k+Fintype.card F*Fintype.card F ≤ B)
    (large : 768 ≤ w) :
    (64*w)*wordCount X ≤ B*w^2 ∧ wordCount X*(5*(64*w)+6)+6 ≤ 4000*(w*B) := by
  have words := wordCount_cap X size fixedPart
  constructor
  · calc
      _ ≤ (64*w)*(12*B) := Nat.mul_le_mul_left _ words
      _ = (B*w)*768 := by ring
      _ ≤ (B*w)*w := Nat.mul_le_mul_left _ large
      _ = _ := by ring
  · have hcost := Nat.mul_le_mul_right (5*(64*w)+6) words
    have bpos : 1 ≤ B := by omega
    have bw : B ≤ w*B := by simpa using Nat.mul_le_mul_right B (show 1 ≤ w by omega)
    nlinarith only [hcost,bpos,bw]

/-- Padding the payload words gives a fixed public unpacking limit independent
of the approximation chosen at this scale. -/
def paddedWord (i : ℕ) : Word W := if i < wordCount X then word X code i else 0

def paddedTape (w B : ℕ) (enc : FieldCode F (64*w)) : Fin (B*w^2) → Bool :=
  fun i => FixedTraceImage.bits (paddedWord X enc) i.val

theorem paddedTape_at {w B : ℕ} (enc : FieldCode F (64*w)) (i : Fin (wordCount X))
    (j : Fin (64*w)) (room : (64*w)*wordCount X ≤ B*w^2) :
    paddedTape X w B enc ⟨64*w*i.val+j.val,by
      have h := Nat.mul_le_mul_left (64*w) i.isLt
      rw [Nat.mul_succ] at h
      omega⟩ = (word X enc i.val).val.testBit (64*w-1-j.val) := by
  rw [paddedTape,FixedTraceImage.bits_at (paddedWord X enc) i.val j]
  simp [paddedWord,i.isLt]

theorem paddedTape_after {w B : ℕ} (enc : FieldCode F (64*w)) (i : Fin (B*w^2))
    (large : 0 < w) (after : (64*w)*wordCount X ≤ i.val) : paddedTape X w B enc i = false := by
  have hw : 0 < 64*w := by omega
  have h := (Nat.le_div_iff_mul_le hw).mpr
    (show wordCount X*(64*w) ≤ i.val by simpa [Nat.mul_comm] using after)
  simp [paddedTape,FixedTraceImage.bits,paddedWord,Nat.not_lt.mpr h]

def paddedMemory (B base : ℕ) (m : Memory W) : Memory W :=
  fillSegment base (12*B) (fun i => paddedWord X code (i-base)) m

theorem paddedMemory_eq (B base : ℕ) (m : Memory W) (a : ℕ) (ha : a < wordCount X)
    (cap : wordCount X ≤ 12*B) :
    paddedMemory X code B base m (base+a) = packed X code base m (base+a) := by
  have h : a < 12*B := lt_of_lt_of_le ha cap
  simp [paddedMemory,packed,fillSegment,paddedWord,ha,h]

theorem padded_clock (w B : ℕ) (large : 768 ≤ w) (positive : 0 < B) :
    (64*w)*(12*B) ≤ B*w^2 ∧ (12*B)*(5*(64*w)+6)+6 ≤ 4000*(w*B) := by
  constructor
  · calc
      _ = (B*w)*768 := by ring
      _ ≤ (B*w)*w := Nat.mul_le_mul_left _ large
      _ = _ := by ring
  · have bw : B ≤ w*B := by simpa using Nat.mul_le_mul_right B (show 1 ≤ w by omega)
    nlinarith only [bw,positive]

/-- Every choice of X at the same age and size budget is loaded by the same
fifteen instructions, four public operands, and exact instruction clock. -/
theorem generate_padded {pcCount regs pubCount w B : ℕ} (enc : FieldCode F (64*w))
    (M : Machine (64*w) pcCount regs pubCount)
    (pc : Fin 15 ↪ Fin pcCount) (reg : Fin 8 ↪ Fin regs) (pub : Fin 4 → Fin pubCount)
    (exit : Fin pcCount) (installed : (PackWordBlock.block (64*w)).Installed M pc reg pub exit)
    (src dst : ℕ) (c : Config (64*w) pcCount regs) (m : Memory (64*w))
    (entry : c.pc=pc (PackWordBlock.block (64*w)).first)
    (params : ∀ i, M.publicData (pub i) = (![src,dst,dst+12*B,64*w] i : ℕ))
    (large : 768 ≤ w) (positive : 0 < B)
    (apart : dst+12*B ≤ src ∨ src+(64*w)*(12*B) ≤ dst)
    (dstFit : dst+12*B < 2^(64*w)) (srcFit : src+(64*w)*(12*B) < 2^(64*w))
    (input : ∀ i, m (src+i.val) = ((paddedTape X w B enc i).toNat : Word (64*w))) :
    ∃ out, RAM.advance M.program ((12*B)*(5*(64*w)+6)+6) c m =
      some (out,paddedMemory X enc B dst m) ∧ out.pc=exit := by
  apply load_words M pc reg pub exit installed src dst (12*B) (paddedWord X enc) c m
    entry params apart dstFit srcFit
  intro i hi
  exact input ⟨i,lt_of_lt_of_le hi (padded_clock w B large positive).1⟩

/-- The four public operands depend only on the scale and the memory map. -/
def loader (w B src dst : ℕ) : PhysicalProcedure.Procedure (64*w) :=
  ⟨15,8,4,PackWordBlock.block _,fun i => (![src,dst,dst+12*B,64*w] i : ℕ)⟩

theorem loader_spec {w B src dst : ℕ} (enc : FieldCode F (64*w)) (large : 768 ≤ w)
    (positive : 0 < B) (apart : dst+12*B ≤ src ∨ src+(64*w)*(12*B) ≤ dst)
    (dstFit : dst+12*B < 2^(64*w)) (srcFit : src+(64*w)*(12*B) < 2^(64*w)) :
    (loader w B src dst).Spec
      (fun m => ∀ i, m (src+i.val) = ((paddedTape X w B enc i).toNat : Word (64*w)))
      (fun m out => out=paddedMemory X enc B dst m) (4000*(w*B)) := by
  intro P R K M pc reg pub exit installed params c m start bits
  obtain ⟨out,run,done⟩ := generate_padded X enc M pc reg pub exit installed src dst c m start
    params large positive apart dstFit srcFit bits
  exact ⟨_,(padded_clock w B large positive).2,out,_,run,done,rfl⟩


end
end Hierarchy.GridApproximationAdvice

end OAI
