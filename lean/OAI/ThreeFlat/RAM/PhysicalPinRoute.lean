import OAI.ThreeFlat.RAM.PhysicalPinDecode

namespace OAI
/-! # Row-major indices select the stipulated physical input pins -/

namespace ThreeFlat.RAM.PhysicalPinsExpr.Shape

open Diagonal Diagonal.ApproximateImage

variable (s : Shape) [NeZero s.period]

def slots (block : ℕ) (j : Fin (s.inside+1)) : Fin s.chunks :=
  AlignedChunks.slot (AlignedChunks.phase s.period block) j

private theorem slots_val (block : ℕ) (tick : Fin (s.inside+1)) :
    (s.slots block tick).val = block%s.period*(s.inside+1)+tick.val :=
  AlignedChunks.slot_nat _ _

omit [NeZero s.period] in
private theorem chunk_val (half : Bool) (c b : ℕ) :
    ApproximateAddress.chunk s.chunks s.bits half c b =
      half.toNat*s.halfBits + c*s.bits+b := by
  cases half <;> simp [ApproximateAddress.chunk,Shape.halfBits]

private theorem digit_eq (w x j : ℕ) (h : x<2^w) :
    digit w x j = (x.testBit j).toNat := shift_digit x j h

theorem ticking_port (w : ℕ) (m : ℕ → ℕ) (params : Fin s.parameterBits → Bool)
    (readParams : ∀ j : Fin s.parameterBits, m (s.parameterBase+j.val)=(params j).toNat)
    (block : Fin (s.last+1)) (tick : Fin (s.inside+1)) (team : Fin s.teams)
    (ht : team.val<2^w) (hs : block.val*(s.inside+1)+tick.val<2^w) (j : Fin s.plen) :
    s.ticking w m block.val tick.val team.val j.val =
      ApproximateAddress.physical (s.slots block.val) (AlignedChunks.active s.period block.val) block
        (tickPort (d:=s.advice) (nt:=s.teamBits) (ns:=s.timeBits) block.val params tick team j) := by
  have hbit (bit : Fin s.bits) : bit.val<s.bits := bit.isLt
  have hteam (j : Fin s.teamBits) : j.val<s.teamBits := j.isLt
  have htime (j : Fin s.timeBits) : j.val<s.timeBits := j.isLt
  have hparam (j : Fin s.parameterBits) : j.val<s.parameterBits := j.isLt
  have hadvice (j : Fin s.advice) : j.val<s.advice := j.isLt
  have addIdx (k : Fin s.bits) : k.addNat s.bits=Fin.natAdd s.bits k :=
    Fin.ext (Nat.add_comm k.val s.bits)
  have rightField (k : Fin s.bits) :
      Fin.append (ApproximatePort.leftChunk (I:=Fin s.chunks) (d:=s.advice) tick)
        (ApproximatePort.rightChunk tick) (k.addNat s.bits) = ApproximatePort.rightChunk tick k := by
    rw [addIdx,Fin.append_right]
  unfold tickPort fields
  refine Fin.addCases ?_ (Fin.addCases ?_ (Fin.addCases ?_ (Fin.addCases ?_
    (Fin.addCases ?_ (Fin.addCases ?_ (Fin.addCases ?_ ?_)))))) j
  all_goals
    intro k
    have hk := k.isLt
    simp (disch := first | assumption | omega) [ticking,ApproximateAddress.physical,
      Fin.append_left,Fin.append_right,Function.comp_apply, Fin.val_natAdd,
      Nat.add_assoc,Nat.add_sub_add_left,rightField,digit_eq _ _ _ ht,digit_eq _ _ _ hs,digits,readParams,
      slots_val,chunk_val, Nat.two_mul,Shape.halfBits]

theorem decode_port (w : ℕ) (m : ℕ → ℕ) (params : Fin s.parameterBits → Bool)
    (readParams : ∀ j : Fin s.parameterBits, m (s.parameterBase+j.val)=(params j).toNat)
    (block : Fin (s.last+1)) (teamsFit : s.teams≤2^w)
    (ticksFit : (s.last+1)*(s.inside+1)≤2^w)
    (raw : Fin (s.area+2*s.halfBits)) :
    s.decode w m block.val raw.val =
      ApproximateAddress.physical (s.slots block.val) (AlignedChunks.active s.period block.val) block
        (select (d:=s.advice) (nt:=s.teamBits) (ns:=s.timeBits) block.val params raw) := by
  let e := FoldInput.rowMajor (L:=s.inside+1) (copies:=s.teams) (p:=s.plen) (B:=s.halfBits)
  have unpack (q : FoldInput.Port (s.inside+1) s.teams s.plen s.halfBits) :
      select (d:=s.advice) (nt:=s.teamBits) (ns:=s.timeBits) block.val params (e q) =
        port (n:=s.inside) (chunks:=s.chunks) (d:=s.advice) (nt:=s.teamBits) (ns:=s.timeBits)
          block.val params q := by
    exact congrArg _ (e.symm_apply_apply q)
  obtain ⟨pt,rfl⟩ : ∃ pt, e pt=raw := (FoldInput.rowMajor (L:=s.inside+1) (copies:=s.teams)
    (p:=s.plen) (B:=s.halfBits)).surjective raw
  rw [unpack]
  cases pt with
  | inl pt =>
    rcases pt with ⟨⟨tick,team⟩,k⟩
    have hs : block.val*(s.inside+1)+tick.val<2^w := by
      have a := Nat.add_lt_add_left tick.isLt (block.val*(s.inside+1))
      have b := Nat.mul_le_mul_right (s.inside+1) block.isLt
      rw [Nat.succ_mul] at b
      exact a.trans_le (b.trans ticksFit)
    exact (s.decode_tick w m block.val tick team k).trans
      (s.ticking_port w m params readParams block tick team (team.isLt.trans_le teamsFit) hs k)
  | inr pt =>
    obtain ⟨flag,idx⟩ := pt
    obtain ⟨⟨hi,lo⟩,rfl⟩ := finProdFinEquiv.surjective idx
    dsimp only [e]
    rw [s.decode_boundary w m block.val flag (finProdFinEquiv (hi,lo))]
    have hidx : (finProdFinEquiv (hi,lo)).val=hi.val*s.bits+lo.val := by
      change lo.val+s.bits*hi.val=_
      ac_rfl
    cases flag <;> simp [ApproximateImage.port,ApproximateAddress.physical,chunk_val,hidx,Nat.add_assoc]

end ThreeFlat.RAM.PhysicalPinsExpr.Shape

end OAI
