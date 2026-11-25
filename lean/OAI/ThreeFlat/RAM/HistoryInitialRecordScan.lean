import OAI.ThreeFlat.RAM.HistoryInitialBody

namespace OAI
/-! # Decoding a four-word S12 record at an absolute scan address -/
namespace ThreeFlat.RAM.HistoryInitialSeed
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

theorem decode_record {F : Type*} {p W : ℕ} (tag : ((Fin 3→Bool)→F)→ℕ) (N : BitNetwork F p)
    (A : Layout) (z : Site) (pub : Fin TraceEndpointROM.params→Word W) (src : Memory W)
    (count : N.cells=z.rows A) (four : 4<2^W) (operand : ∀ (m : Memory W),z.retains A m src →
      ∀ i : Fin N.cells,∀ j : Fin 4,∀ v : Fin 4→Word W,
        (v 0).val=i.val → (v 1).val=j.val → v 2=(z.lane:Word W) → v 3=(z.stage:Word W) →
        (decoder W A).eval pub m v=(HistoryCompiledRows.metadata tag N i j:Word W)) :
    ∀ a : Word W,∀ m,z.stream A≤a.val → a.val<z.stream A+4*z.rows A → z.retains A m src →
      let delta:=a-(z.stream A:Word W)
      (decoder W A).eval pub m
        ![BinaryOp.eval .div delta 4,BinaryOp.eval .mod delta 4,(z.lane:Word W),(z.stage:Word W)]=
        recordAt tag N (z.stream A) a.val := by
  intro a m lo hi keep
  let n:=a.val-z.stream A
  have ir : n/4<N.cells := by dsimp [n];rw [count];omega
  let i : Fin N.cells:=⟨n/4,ir⟩
  let j : Fin 4:=⟨n%4,Nat.mod_lt _ (by decide)⟩
  let delta:=a-(z.stream A:Word W)
  have hcast : ((z.stream A):Word W).val=z.stream A:=Fin.val_cast_of_lt (lo.trans_lt a.isLt)
  have le : (z.stream A:Word W)≤a := Fin.le_def.mpr (hcast.trans_le lo)
  have val : delta.val=n := by rw [show delta.val=_ from Fin.sub_val_of_le le,hcast]
  have denom : (4:Word W).val=4 := Fin.val_cast_of_lt four
  dsimp only
  change _=recordAt tag N (z.stream A) a.val
  rw [show recordAt (W:=W) tag N (z.stream A) a.val=(HistoryCompiledRows.metadata tag N i j:Word W)
    from dite_eq_left ir]
  apply operand m keep i j _ _ _ rfl rfl
  · change (Fin.ofNat (2^W) (delta.val/(4:Word W).val)).val=i.val
    rw [val,denom]
    exact Fin.val_cast_of_lt ((Nat.div_le_self n 4).trans_lt (by dsimp [n];exact (Nat.sub_le ..).trans_lt a.isLt))
  · change (Fin.ofNat (2^W) (delta.val%(4:Word W).val)).val=j.val
    rw [val,denom]
    exact Fin.val_cast_of_lt ((Nat.mod_lt n (by decide : 0<4)).trans four)


end ThreeFlat.RAM.HistoryInitialSeed

end OAI
