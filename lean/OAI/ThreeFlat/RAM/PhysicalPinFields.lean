import OAI.ThreeFlat.RAM.PhysicalPinsNumeric
import OAI.ThreeFlat.Diagonal.ApproximateImage

namespace OAI
/-! # Decoding the eight fields of an aligned physical tick row -/

namespace ThreeFlat.RAM.PhysicalPinsExpr

open Diagonal Diagonal.ApproximateImage
namespace Shape

variable (s : Shape)

abbrev plen := pinCount s.advice s.teamBits s.timeBits s.parameterBits s.bits

def area := (s.inside+1)*s.teams*s.plen

def digit (w x j : ℕ) := (if j<w then x>>>j else 0)%2

def ticking (w : ℕ) (mem : ℕ → ℕ) (block tick team j : ℕ) : ℕ :=
  let z0 := s.advice
  let z1 := z0+s.teamBits
  let z2 := z1+s.timeBits
  let z3 := z2+s.parameterBits
  let z4 := z3+s.bits
  let z5 := z4+s.bits
  let z6 := z5+s.bits
  let ep := ApproximateAddress.endpoint s.chunks s.bits s.last s.advice
  let mid := ApproximateAddress.interior s.chunks s.bits s.last s.inside s.advice
  let chunk := (block%s.period)*(s.inside+1)+tick
  let pos := (AlignedChunks.active s.period block).toNat*s.halfBits + chunk*s.bits
  if j<z0 then 2+j
  else if j<z1 then digit w team (j-z0)
  else if j<z2 then digit w (block*(s.inside+1)+tick) (j-z1)
  else if j<z3 then mem (s.parameterBase+(j-z2))
  else if j<z4 then
    if tick=0 then ep false block (2*s.halfBits+(j-z3)) else mid block (tick-1) (j-z3)
  else if j<z5 then
    if tick=s.inside then ep true block (2*s.halfBits+(j-z4)) else mid block tick (j-z4)
  else if j<z6 then ep false block (pos+(j-z5))
  else ep true block (pos+(j-z6))

def passive (s : Shape) (block offset : ℕ) := (1-(AlignedChunks.active s.period block).toNat)*
  s.halfBits + offset%s.halfBits

def decode (w : ℕ) (mem : ℕ → ℕ) (block raw : ℕ) : ℕ :=
  if raw<s.area then s.ticking w mem block (raw/s.plen/s.teams)
      (raw/s.plen%s.teams) (raw%s.plen)
  else
    let off := raw-s.area
    ApproximateAddress.endpoint s.chunks s.bits s.last s.advice (decide (s.halfBits≤off))
      block (s.passive block off)

private theorem tick_index {n q p h : ℕ} (j : Fin n) (team : Fin q) (k : Fin p) :
    (FoldInput.rowMajor (B:=h) (.inl ((j,team),k))).val =
      (j.val*q+team.val)*p+k.val := by
  change k.val+p*(team.val+q*j.val) = _
  ac_rfl

private theorem boundary_index {n q p h : ℕ} (b : Bool) (i : Fin h) :
    (FoldInput.rowMajor (L:=n) (copies:=q) (p:=p) (.inr (b,i))).val =
      n*q*p+b.toNat*h+i.val := by
  cases b <;> simp [FoldInput.rowMajor, FoldInput.flagIndex, finSumFinEquiv_apply_right, finProdFinEquiv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem decode_tick (w : ℕ) (mem : ℕ → ℕ) (block : ℕ)
    (j : Fin (s.inside+1)) (team : Fin s.teams) (k : Fin s.plen) :
    s.decode w mem block (FoldInput.rowMajor (B:=s.halfBits) (.inl ((j,team),k))).val =
      s.ticking w mem block j.val team.val k.val := by
  let limb := j.val*s.teams+team.val
  have pos : 0<s.plen := (Nat.zero_le _).trans_lt k.isLt
  have teamsPos : 0<s.teams := (Nat.zero_le _).trans_lt team.isLt
  have ltLimb : limb < (s.inside+1)*s.teams := by
    have a := Nat.add_lt_add_left team.isLt (j.val*s.teams)
    have b := Nat.mul_le_mul_right s.teams j.isLt
    simp only [Nat.succ_mul] at b
    simpa only [limb,Shape.area,Nat.succ_mul] using a.trans_le b
  have ltRaw : limb*s.plen+k.val < s.area :=
    by
      have a := Nat.add_lt_add_left k.isLt (limb*s.plen)
      have b := Nat.mul_le_mul_right s.plen ltLimb
      simp only [Nat.succ_mul] at b
      simpa only [limb,Shape.area,Nat.succ_mul] using a.trans_le b
  rw [tick_index]
  change s.decode w mem block (limb*s.plen+k.val) = _
  have rawDiv : (limb*s.plen+k.val)/s.plen=limb := by
    rw [Nat.mul_comm limb, Nat.mul_add_div pos, Nat.div_eq_of_lt k.isLt, Nat.add_zero]
  have teamDiv : limb/s.teams=j.val := by
    dsimp [limb]
    rw [Nat.mul_comm j.val, Nat.mul_add_div teamsPos, Nat.div_eq_of_lt team.isLt, Nat.add_zero]
  simp [decode,ltRaw,rawDiv,teamDiv,Nat.mul_add_mod_of_lt k.isLt,
    show limb%s.teams=team.val from Nat.mul_add_mod_of_lt team.isLt]

theorem decode_boundary (w : ℕ) (mem : ℕ → ℕ) (block : ℕ)
    (flag : Bool) (i : Fin s.halfBits) :
    s.decode w mem block (FoldInput.rowMajor (L:=s.inside+1) (copies:=s.teams)
      (p:=s.plen) (.inr (flag,i))).val =
    ApproximateAddress.endpoint s.chunks s.bits s.last s.advice flag block
      ((!(AlignedChunks.active s.period block)).toNat*s.halfBits+i.val) := by
  rw [boundary_index]
  change s.decode w mem block (s.area + flag.toNat*s.halfBits+i.val) = _
  have hi := i.isLt
  cases flag <;> cases ha : AlignedChunks.active s.period block <;>
    simp [decode,passive,ha,Nat.add_assoc,Nat.mod_eq_of_lt hi,Nat.not_le.mpr hi,
      Nat.not_lt.mpr (Nat.le_add_right _ _)]

end Shape
end ThreeFlat.RAM.PhysicalPinsExpr

end OAI
