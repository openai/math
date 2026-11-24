import OAI.Computability.VPVNP.LiveHeaderShapes

/-!
# Native descriptor writes for Section 14.1

A fixed straight-line block takes an incident side and a field. It reads
the width, tag, and two phase flags, then writes the field's source offset
and length. The block handles clamped endpoints, the incoming midpoint
of the first tail group, and all zero-length intervals.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderDescriptors

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM
open scoped Fin.CommRing

/-- Public data are small sizes and scratch addresses. Exponent size is the
total `t*Z`. Configuration size excludes the mode and zero padding. -/
structure Parameters where
  /-- Public operand index for the address holding the incident cut width. -/
  widthAddress : Fin 16
  /-- Public operand index for the address holding the selected live-mode tag. -/
  tagAddress : Fin 16
  /-- Public operand index for the address of the first-half flag. -/
  firstHalfAddress : Fin 16
  /-- Public operand index for the address marking the first evaluator group after the
  midpoint. -/
  firstTailAddress : Fin 16
  /-- Public operand index supplying the cut's basic width parameter. -/
  delta : Fin 16
  /-- Public operand index supplying the allocated exponent field size. -/
  exponentSize : Fin 16
  /-- Public operand index supplying the allocated evaluator configuration size. -/
  configSize : Fin 16
  /-- Public operand index for the destination cell of the computed source offset. -/
  offsetAddress : Fin 16
  /-- Public operand index for the destination cell of the computed field length. -/
  countAddress : Fin 16

namespace Native

private abbrev Pub := Fin 16
private abbrev Reg := Fin 48
private abbrev Code := Flow 48 16

/-- Load the public sizes and descriptor destinations and read the live width, mode tag, and
phase flags. -/
def load (p : Parameters) : Code :=
  straight (.constant 1 1) [
    .publicWord 2 p.widthAddress, .publicWord 3 p.tagAddress, .publicWord 4 p.firstHalfAddress,
    .publicWord 5 p.firstTailAddress, .publicWord 6 p.delta, .publicWord 7 p.exponentSize,
    .publicWord 8 p.configSize, .publicWord 9 p.offsetAddress, .publicWord 10 p.countAddress,
    .read 2 2, .read 3 3, .read 4 4, .read 5 5]

/-- Registers 15 and 16 indicate respectively a pair-format and a tail-format
payload. Register 11 is the length of the mode (zero or one). -/
def masks (side : Side) : Code :=
  straight (.binary .div 11 2 2) [.binary .div 12 3 3, .binary .mul 13 11 12,
    (match side with | .left => .binary .bitOr 14 4 5 | .right => .copy 14 4),
    .binary .mul 15 13 14, .binary .sub 16 1 14, .binary .mul 16 13 16]

/-- Apply the phase and mode masks to obtain the exterior, exponent, and configuration field
lengths. -/
def lengths : Code := straight (.binary .sub 17 2 6) [
  .binary .mul 17 17 15, .binary .mul 18 7 15, .binary .mul 19 8 16]

/-- Compute successive field offsets and the residual padding length from the live width and
the enabled field lengths. -/
def starts : Code := straight (.binary .add 20 11 17) [
  .binary .add 21 20 18, .binary .add 22 21 19, .binary .sub 23 2 22]

/-- Select the register containing the computed source offset for the requested field. -/
def startReg : Field → Reg
  | .exterior => 11 | .exponents => 20 | .config => 21 | .padding => 22

/-- Select the register containing the computed length for the requested field. -/
def countReg : Field → Reg
  | .exterior => 17 | .exponents => 18 | .config => 19 | .padding => 23

/-- Write the field length and its offset, setting the offset to zero when the interval is
empty. -/
def emit (f : Field) : Code := straight (.binary .div 24 (countReg f) (countReg f)) [
  .binary .mul 25 (startReg f) 24, .write 9 25, .write 10 (countReg f)]

/-- The descriptor worker that reads metadata, selects the masks for the incident side,
computes its field intervals, and publishes one interval. -/
def block (p : Parameters) (side : Side) (f : Field) : Code :=
  .seq (load p) (.seq (masks side) (.seq lengths (.seq starts (emit f))))

variable {w : ℕ}

private def putAll (rs : Regs w 48) (vs : List (Reg × Word w)) :=
  vs.foldl (fun a j => Function.update a j.1 j.2) rs

private def loadRegs (pub : Pub → Word w) (p : Parameters) (m : Memory w) (rs : Regs w 48) : Regs w 48 :=
  putAll rs [(1,1),(2,pub p.widthAddress),(3,pub p.tagAddress),(4,pub p.firstHalfAddress),
    (5,pub p.firstTailAddress),(6,pub p.delta),(7,pub p.exponentSize),(8,pub p.configSize),
    (9,pub p.offsetAddress),(10,pub p.countAddress),(2,m (pub p.widthAddress).val),
    (3,m (pub p.tagAddress).val),(4,m (pub p.firstHalfAddress).val),(5,m (pub p.firstTailAddress).val)]

private def loadEvents (pub : Pub → Word w) (p : Parameters) (m : Memory w) : List (Event w) :=
  List.replicate 10 .tick ++ [.read (pub p.widthAddress) (m (pub p.widthAddress).val),
    .read (pub p.tagAddress) (m (pub p.tagAddress).val),
    .read (pub p.firstHalfAddress) (m (pub p.firstHalfAddress).val),
    .read (pub p.firstTailAddress) (m (pub p.firstTailAddress).val)]

private def nz (x : Word w) := BinaryOp.div.eval x x
private def sideWord (side : Side) (rs : Regs w 48) : Word w :=
  match side with | .left => BinaryOp.bitOr.eval (rs 4) (rs 5) | .right => rs 4

private def maskRegs (side : Side) (rs : Regs w 48) : Regs w 48 :=
  let active := nz (rs 2) * nz (rs 3)
  let group := sideWord side rs
  putAll rs [(11,nz (rs 2)),(12,nz (rs 3)),(13,active),(14,group),(15,active*group),
    (16,rs 1 - group),(16,active*(rs 1-group))]

private def lengthRegs (rs : Regs w 48) : Regs w 48 :=
  putAll rs [(17,rs 2 - rs 6),(17,(rs 2-rs 6)*rs 15),(18,rs 7*rs 15),(19,rs 8*rs 16)]

private def startRegs (rs : Regs w 48) : Regs w 48 :=
  let x := rs 11 + rs 17
  let y := x + rs 18
  let z := y + rs 19
  putAll rs [(20,x),(21,y),(22,z),(23,rs 2-z)]

/-- Zero-length fields receive offset zero. -/
private def offWord (rs : Regs w 48) (f : Field) := rs (startReg f) * nz (rs (countReg f))

private theorem raw_exec (pub : Pub → Word w) (p : Parameters) (state : Word w) (m : Memory w)
    (rs : Regs w 48) (side : Side) (f : Field) :
    let a := startRegs (lengthRegs (maskRegs side (loadRegs pub p m rs)))
    let v := offWord a f
    let l := a (countReg f)
    ∃ out, Flow.Exec pub state (block p side f) rs m
      (loadEvents pub p m ++ (List.replicate 7 .tick ++ (List.replicate 4 .tick ++
        (List.replicate 4 .tick ++ [.tick,.tick,.write (a 9) v,.write (a 10) l])))) out
      (writeMemory (writeMemory m (a 9) v) (a 10) l) := by
  let a := loadRegs pub p m rs
  let b := maskRegs side a
  let d := lengthRegs b
  let g := startRegs d
  have ha : Flow.Exec pub state (load p) rs m (loadEvents pub p m) a m :=
    (Flow.once_sound pub state false _ rs m rfl).1
  have hb : Flow.Exec pub state (masks side) a m (List.replicate 7 .tick) b m := by
    apply (Flow.once_sound pub state false _ a m ?_).1
    cases side <;> rfl
  have hd : Flow.Exec pub state lengths b m (List.replicate 4 .tick) d m :=
    (Flow.once_sound pub state false _ b m rfl).1
  have hg : Flow.Exec pub state starts d m (List.replicate 4 .tick) g m :=
    (Flow.once_sound pub state false _ d m rfl).1
  let v := offWord g f
  let l := g (countReg f)
  let out := putAll g [(24,nz l),(25,v)]
  have hw : Flow.Exec pub state (emit f) g m [.tick,.tick,.write (g 9) v,.write (g 10) l] out
      (writeMemory (writeMemory m (g 9) v) (g 10) l) := by
    apply (Flow.once_sound pub state false _ g m ?_).1
    cases f <;> rfl
  exact ⟨out,ha.seq (hb.seq (hd.seq (hg.seq hw)))⟩

private theorem nz_eq (x : Word w) : nz x = (if x.val = 0 then 0 else 1) := by
  apply Fin.ext
  change (x.val / x.val) % 2^w = _
  by_cases hz : x.val = 0
  · simp [hz]
  · rw [Nat.div_self (Nat.pos_of_ne_zero hz), ite_eq_right hz]; rfl

private theorem nz_val (x : Word w) (hw : 0 < w) : (nz x).val = mode x.val := by
  rw [nz_eq, mode]
  split_ifs with hz
  · rfl
  · exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')

private theorem or_bits (hw : 0 < w) (x y : Bool) :
    BinaryOp.bitOr.eval (encodeBit w x) (encodeBit w y) = encodeBit w (x || y) := by
  have ho := Nat.one_lt_two_pow hw.ne'
  cases x <;> cases y <;> apply Fin.ext <;>
    simp [BinaryOp.eval, encodeBit, Nat.mod_eq_of_lt ho]

private theorem shapeMasks (hw : 0 < w) (side : Side) (a : Regs w 48) (W tag : ℕ)
    (half firstTail : Bool) (h1 : a 1 = 1) (hW : (a 2).val = W) (htag : (a 3).val = tag)
    (hhalf : a 4 = encodeBit w half) (htail : a 5 = encodeBit w firstTail) :
    let b := maskRegs side a
    let form := shape side W tag half firstTail
    b 15 = (if form = .pair then 1 else 0) ∧ b 16 = (if form = .tail then 1 else 0) := by
  let g := half || (decide (side = .left) && firstTail)
  have hgroup : sideWord side a = encodeBit w g := by
    cases side
    · simpa [sideWord, g, hhalf, htail] using or_bits (w := w) hw half firstTail
    · simpa [sideWord, g] using hhalf
  let active := nz (a 2) * nz (a 3)
  change active*sideWord side a = _ ∧ active*(a 1-sideWord side a) = _
  rw [hgroup,h1]
  dsimp only [active]
  rw [nz_eq, nz_eq, hW, htag]
  change _ = (if (if W = 0 then Shape.missing else if tag = 0 then .unit else if g then .pair else .tail)
    = .pair then _ else _) ∧ _ = (if (if W = 0 then Shape.missing else if tag = 0 then .unit else
    if g then .pair else .tail) = .tail then _ else _)
  by_cases hz : W = 0 <;> by_cases hu : tag = 0 <;> cases g <;> simp [hz, hu, encodeBit]

private theorem geometry {side : Side} (a : Regs w 48) (W tag Δ e c : ℕ) (half firstTail : Bool)
    (hW : (a 2).val = W) (hΔ : (a 6).val = Δ) (he : (a 7).val = e) (hc : (a 8).val = c)
    (hmode : (a 11).val = mode W)
    (hpair : a 15 = if shape side W tag half firstTail = .pair then 1 else 0)
    (htail : a 16 = if shape side W tag half firstTail = .tail then 1 else 0)
    (hefit : 1+e ≤ Δ) (hcfit : 1+c ≤ Δ) (hblock : W = 0 ∨ Δ ≤ W) (f : Field) :
    let g := startRegs (lengthRegs a)
    let form := shape side W tag half firstTail
    (g (startReg f)).val = start form W Δ e c f ∧ (g (countReg f)).val = count form W Δ e c f := by
  let d := lengthRegs a
  let g := startRegs d
  let form := shape side W tag half firstTail
  have hδ := shape_fit (side := side) (tag := tag) (half := half) (firstTail := firstTail) hblock
  have hbound := payload_le hefit hcfit hδ
  change mode W + exterior form W Δ + exponents form e + config form c ≤ W at hbound
  have hf := (a 2).isLt
  rw [hW] at hf
  have h17 : (d 17).val = exterior form W Δ := by
    change ((a 2-a 6)*a 15).val = _
    change a 15 = (if form = .pair then 1 else 0) at hpair
    rw [hpair,exterior]
    split_ifs with hp
    · rw [mul_one, Fin.sub_val_of_le (by change (a 6).val ≤ _; rw [hΔ,hW]; exact hδ (Or.inl hp)),hW,hΔ]
    · rw [mul_zero]; rfl
  have h18 : (d 18).val = exponents form e := by
    change (a 7*a 15).val = _
    change a 15 = (if form = .pair then 1 else 0) at hpair
    rw [hpair,exponents]; split_ifs <;> simp [he]
  have h19 : (d 19).val = config form c := by
    change (a 8*a 16).val = _
    change a 16 = (if form = .tail then 1 else 0) at htail
    rw [htail,config]; split_ifs <;> simp [hc]
  have h11 : (d 11).val = mode W := hmode
  have h20 : (g 20).val = start form W Δ e c .exponents := by
    change (d 11+d 17).val = _
    rw [Fin.val_add_eq_of_add_lt (by omega),h11,h17]; rfl
  have h21 : (g 21).val = start form W Δ e c .config := by
    change (g 20+d 18).val = _
    simp only [start] at h20 ⊢
    rw [Fin.val_add_eq_of_add_lt (by omega),h20,h18]
  have h22 : (g 22).val = start form W Δ e c .padding := by
    change (g 21+d 19).val = _
    simp only [start] at h21 ⊢
    rw [Fin.val_add_eq_of_add_lt (by omega),h21,h19]
  have h23 : (g 23).val = count form W Δ e c .padding := by
    change (a 2 - g 22).val = _
    rw [Fin.sub_val_of_le (by change (g 22).val ≤ _; rw [h22,hW]; exact hbound),hW,h22]; rfl
  cases f with
  | exterior => exact ⟨h11,h17⟩
  | exponents => exact ⟨h20,h18⟩
  | config => exact ⟨h21,h19⟩
  | padding => exact ⟨h22,h23⟩

/-- Four scratch reads and two writes. The other twenty-seven operations
are register arithmetic and public parameter loads. -/
def events (pub : Pub → Word w) (p : Parameters) (m : Memory w) (o l : Word w) : List (Event w) :=
  loadEvents pub p m ++ (List.replicate 7 .tick ++ (List.replicate 4 .tick ++
    (List.replicate 4 .tick ++ [.tick,.tick,.write (pub p.offsetAddress) o,.write (pub p.countAddress) l])))

theorem event_cost (pub : Pub → Word w) (p : Parameters) (m : Memory w) (o l : Word w) :
    countProbes (events pub p m o l) = 6 ∧ choiceBits (events pub p m o l) = [] ∧
    (events pub p m o l).length = 33 := ⟨rfl,rfl,rfl⟩

/-- The block materializes both descriptor words at designated addresses.
Their exact natural values fit because the whole source interval fits in
the incident width. All parameter cells are read before either write. -/
theorem block_exec (hw : 0 < w) (pub : Pub → Word w) (p : Parameters) (state : Word w)
    (m : Memory w) (rs : Regs w 48) (side : Side) (f : Field) (W tag Δ e c : ℕ) (half firstTail : Bool)
    (hW : (m (pub p.widthAddress).val).val = W) (ht : (m (pub p.tagAddress).val).val = tag)
    (hh : m (pub p.firstHalfAddress).val = encodeBit w half)
    (hft : m (pub p.firstTailAddress).val = encodeBit w firstTail)
    (hΔ : (pub p.delta).val = Δ) (he : (pub p.exponentSize).val = e) (hc : (pub p.configSize).val = c)
    (hefit : 1+e ≤ Δ) (hcfit : 1+c ≤ Δ) (hblock : W = 0 ∨ Δ ≤ W) :
    let form := shape side W tag half firstTail
    let iv := span form W Δ e c f
    ∃ out o l, Flow.Exec pub state (block p side f) rs m (events pub p m o l) out
      (writeMemory (writeMemory m (pub p.offsetAddress) o) (pub p.countAddress) l) ∧
      o.val = iv.1 ∧ l.val = iv.2 := by
  let a := loadRegs pub p m rs
  let b := maskRegs side a
  let g := startRegs (lengthRegs b)
  let form := shape side W tag half firstTail
  obtain ⟨out,hr⟩ := raw_exec pub p state m rs side f
  obtain ⟨hp,hq⟩ := shapeMasks hw side a W tag half firstTail rfl hW ht hh hft
  have hm : (b 11).val = mode W := (nz_val (a 2) hw).trans (congrArg mode hW)
  obtain ⟨hs,hl⟩ := geometry (side := side) b W tag Δ e c half firstTail hW hΔ he hc hm hp hq hefit hcfit hblock f
  have ho : (offWord g f).val = (span form W Δ e c f).1 := by
    change (g (startReg f) * nz (g (countReg f))).val =
      (if count form W Δ e c f = 0 then 0 else start form W Δ e c f)
    change (g (countReg f)).val = count form W Δ e c f at hl
    change (g (startReg f)).val = start form W Δ e c f at hs
    rw [nz_eq,hl]
    split_ifs <;> simp [hs]
  exact ⟨out,offWord g f,g (countReg f),hr,ho,hl⟩

/-- When the chosen output cells are distinct, the field runner reads back
the offset and count deposited by the descriptor block. -/
theorem output_words (m : Memory w) (dstOff dstCount o l : Word w) (h : dstOff ≠ dstCount) :
    let after := writeMemory (writeMemory m dstOff o) dstCount l
    after dstOff.val = o ∧ after dstCount.val = l := by
  have hn : dstOff.val ≠ dstCount.val := fun e => h (Fin.ext e)
  simp [writeMemory, hn]

end Native
end LiveHeaderDescriptors

end VPVNP
end Computability
end OAI
