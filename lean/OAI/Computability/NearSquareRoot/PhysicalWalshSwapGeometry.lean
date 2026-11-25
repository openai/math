import OAI.Computability.NearSquareRoot.PhysicalWalshNodeSwap
import OAI.Computability.NearSquareRoot.PhysicalWalshElementarySchedule
import OAI.Computability.NearSquareRoot.CRTControlledBudget

/-! # The two high windows in the dyadically extended Walsh lane -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.SlotSwap

open IntegerMultiplication Code Strip Strip.Dims Adic Carry Staff
open ElementarySchedule (slotWidth)

variable {A W : ℕ}

def reserve (D A : ℕ) (s : Shape) := min (slotWidth A s) (Controlled.payloadBits D (Header.scale A s))

def geometry (W : ℕ) (i j : Fin A) (s : Shape) (c : ℕ) : Geometry :=
  ⟨Nat.clog 2 (groups W s) + min i.val j.val * slotWidth A s,
   (max i.val j.val - min i.val j.val - 1) * slotWidth A s+c, slotWidth A s-c⟩

def trailBits (i j : Fin A) (s : Shape) (c : ℕ) :=
  (A-1-max i.val j.val)*slotWidth A s+c

def stride (i j : Fin A) (s : Shape) (c : ℕ) := 2^(trailBits i j s c)*s.suff

def wordWidth (i j : Fin A) (s : Shape) (c : ℕ) := stride i j s c*(2*(s.w+1))

private theorem pow_room (n : ℕ) : room (field 2 n) = 2^n := (space _).symm.trans (lineSize ..)

theorem geometry_count (z : Geometry) : z.grid.count = 2^(z.pre+z.wing+z.gap+z.wing) := by
  rw [Geometry.grid,SwapOrdinal.stock_count]
  simp only [pow_room,room_nil,mul_one,pow_add]

theorem width_sum (i j : Fin A) (ne : i ≠ j) (s : Shape) (c : ℕ) (hc : c ≤ slotWidth A s) :
    let z := geometry W i j s c
    z.pre+z.wing+z.gap+z.wing+trailBits i j s c =
      Nat.clog 2 (groups W s) + A*slotWidth A s := by
  have diff : i.val ≠ j.val := fun h => ne (Fin.ext h)
  have E : min i.val j.val + (max i.val j.val-min i.val j.val-1) + (A-1-max i.val j.val) + 2 = A := by
    have h1 := i.isLt
    have h2 := j.isLt
    omega
  have eq := congrArg (fun t => t*slotWidth A s) E
  simp only [Nat.add_mul, Nat.two_mul] at eq
  dsimp only [geometry,trailBits]
  omega

theorem volume_eq (i j : Fin A) (ne : i ≠ j) (s : Shape) (hs : 0 < s.level)
    (c : ℕ) (hc : c ≤ slotWidth A s) :
    (geometry W i j s c).grid.count * stride i j s c =
      2^(Nat.clog 2 (groups W s)) * inner A s := by
  have axes : A*slotWidth A s = grow A s.level := by
    unfold slotWidth grow
    rw [Nat.mul_left_comm A 2,← pow_succ',Nat.sub_add_cancel hs]
  rw [geometry_count,stride,← Nat.mul_assoc,← pow_add,width_sum i j ne s c hc,axes,pow_add,inner,Nat.mul_assoc]

theorem header_le (i j : Fin A) (ne : i ≠ j) (s : Shape) (hs : 0 < s.level) (c : ℕ) (hc : c ≤ slotWidth A s) :
    size (geometry W i j s c).header ≤ Header.scale A s := by
  have g_le : groups W s ≤ s.pref+1 := (max_le s.pref_pos (Nat.div_le_self _ _)).trans (Nat.le_succ _)
  have clog := Nat.clog_mono_right (b:=2) g_le
  have sum := width_sum (W:=W) i j ne s c hc
  have axes : A*slotWidth A s = grow A s.level := by
    unfold slotWidth grow
    rw [Nat.mul_left_comm A 2,← pow_succ',Nat.sub_add_cancel hs]
  rw [axes] at sum
  simp only [Geometry.header,size_prod,size_tally,tally_length,Header.scale_exact]
  omega

theorem reserve_fit (D : ℕ) (i j : Fin A) (ne : i ≠ j) (s : Shape) (hs : 0 < s.level)
    (large : Controlled.payloadBits D (Header.scale A s) ≤ slotWidth A s) :
    (size (geometry W i j s (reserve D A s)).header + 1)^D ≤ wordWidth i j s (reserve D A s) := by
  let c := reserve D A s
  have hcut : c ≤ slotWidth A s := min_le_left ..
  have hlow : c = Controlled.payloadBits D (Header.scale A s) := min_eq_right large
  have h := Nat.pow_le_pow_left (Nat.succ_le_succ (header_le (W:=W) i j ne s hs c hcut)) D
  apply h.trans
  have cap := Controlled.payload_capacity D (Header.scale A s) (s.suff*(2*(s.w+1))) (Nat.mul_pos s.suff_pos (by omega))
  apply cap.trans
  rw [← hlow,wordWidth,stride,Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.le_add_left ..))

/-- The compact header provides its exact size, even when spectator lengths
are recorded in binary. -/
theorem scale_realizes (A : ℕ) : Realizes (Header.regime A) (Header.scale A) := by
  have hd : (Header.regime A).Has (Header.wire A) := (Header.regime A).self
  have lv : Realizes (Header.regime A) Shape.level := hd.ez (Easy.fst.compose Easy.fst)
  have ac : Realizes (Header.regime A) (fun s => grow A s.level) := hd.ez (Easy.fst.compose (Easy.snd.compose Easy.fst))
  have wd : Realizes (Header.regime A) (fun s => s.w+1) := hd.ez (Easy.fst.compose (Easy.snd.compose Easy.snd))
  have pp : Figure (Header.regime A) Shape.pref :=
    ⟨_,hd.ez (Easy.snd.compose Easy.fst),fun s => Header.binary_value s.pref⟩
  have p := (pp.added (Figure.natural 1)).short_log
  have b := ((Header.suff A).added (Figure.natural 1)).short_log
  convert ((Realizes.fix 2).times ((((lv.plus ac).plus wd).plus p).plus b)).plus (.fix 9) using 1
  funext s; exact Header.scale_exact A s

theorem reserve_realizes (D A : ℕ) (hA : 1 ≤ A) : Realizes (Header.regime A) (reserve D A) := by
  let L := slotWidth A
  have hl : Realizes (Header.regime A) L := Header.childBits A hA
  have t := (Realizes.fix D).times (Figure.of_spoken ((scale_realizes A).plus (.fix 1))).short_log
  have h := hl.minused (hl.minused t)
  convert h using 1
  funext s
  dsimp only [reserve,Controlled.payloadBits,L]; omega

theorem geometry_has (D : ℕ) (i j : Fin A) : (Header.regime A).Has
    (fun s => (geometry W i j s (reserve D A s)).header) := by
  have hA : 1 ≤ A := by have := i.isLt; omega
  have c := reserve_realizes D A hA
  have L := Header.childBits A hA
  exact (((Header.groupCount A W).short_log.plus ((Realizes.fix _).times L))).pair
    (((((Realizes.fix _).times L).plus c)).pair (L.minused c))

end PhysicalWalshNode.SlotSwap

end NearSquareRoot
end Computability
end OAI
