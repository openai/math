import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalLocalLift
import OAI.Computability.NearSquareRoot.InterchangeROMStageVolume

/-! # Uniform local time and space in the physical bank volume -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.LocalTable.Lift

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip InterchangeROM
  InterchangeROMStageVolume Raw

/-- This coefficient is computed from the static table and the encoded arity. -/
def costFactor (k : Kind) (p l w s m half : ℕ) (t : Tape) : ℕ :=
  inputs k l w s * (2*(p+1)+2) + 99 + factor k p l w s m half t

theorem primrec_costFactor {X : Type} [Primcodable X] (k : Kind)
    {p l w s m half : X → ℕ} {t : X → Tape} (hp : Primrec p) (hl : Primrec l)
    (hw : Primrec w) (hs : Primrec s) (hm : Primrec m) (hh : Primrec half) (ht : Primrec t) :
    Primrec fun x => costFactor k (p x) (l x) (w x) (s x) (m x) (half x) (t x) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp
    (pr_input k (Primrec.nat_mul.comp hl hw) (Primrec.nat_mul.comp hl hs))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 2) (Primrec.succ.comp hp)) (.const 2))) (.const 99))
    (primrec_factor k hp hl hw hs hm hh ht)

/-- The three allowances of the active ragged bank all scale linearly with
header size and total address/payload volume. -/
theorem charge_le (k : Kind) (p l w s m half : ℕ) (t : Tape) {A : Type} {P : A → Type}
    (rows : Series A) (pay : (a : A) → Series (P a)) (H : Tree) (width : ℕ)
    (hw : ∀ a, (pay a).count ≤ width) (xs : List Tree) (hx : domain rows pay p (inputs k l w s) xs) :
    let a := charge p (outputs k l w s) (inputs k l w s) (matrix k p l w s m half t) H rows.count width xs
    let cap := costFactor k p l w s m half t * InterchangeROMStageVolume.mass H rows.count width
    a.time ≤ cap ∧ a.cap ≤ cap ∧ a.depth ≤ cap := by
  obtain ⟨x,rfl⟩ := hx
  let data := rows.count*(width+1)+1
  have stream (z : Tree) (hz : z ∈ render rows pay x) :
      z.count+1 ≤ data*(2*(p+1)+2) := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    apply stream_size rows pay width hw (fun a j => x a j i)
  have packet := packet_size (p:=p+1) rows width H (render rows pay x) stream
  rw [render_length] at packet
  let v := InterchangeROMStageVolume.mass H rows.count width
  have dh : H.count ≤ v := by dsimp [v,InterchangeROMStageVolume.mass]; omega
  have dd : data ≤ v := by dsimp [data,v,InterchangeROMStageVolume.mass]; omega
  have pos : 1 ≤ v := by dsimp [v,InterchangeROMStageVolume.mass]; omega
  have cost := Nat.mul_le_mul_left (factor k p l w s m half t) dd
  let time := 84*H.count + factor k p l w s m half t * data + 11
  have ht : time ≤ (95+factor k p l w s m half t)*v := by
    dsimp only [time]
    rw [Nat.add_mul]
    omega
  change time ≤ _ ∧ (InterchangeROM.packet H (render rows pay x)).count+time ≤ _ ∧ time ≤ _
  have hpeak : (InterchangeROM.packet H (render rows pay x)).count + time ≤ costFactor k p l w s m half t*v := by
    apply (Nat.add_le_add ((Nat.le_succ _).trans packet) ht).trans
    simp only [costFactor,v]
    ring_nf
    rfl
  have htime := (Nat.le_add_left time _).trans hpeak
  exact ⟨htime,hpeak,htime⟩

end InterchangeROMRepair.Physical.LocalTable.Lift

end NearSquareRoot
end Computability
end OAI
