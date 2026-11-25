import OAI.Hierarchy.DescentResetNodeBooks
import OAI.Hierarchy.DescentPackedColumnHardware
import OAI.Hierarchy.DescentDateBillVolume

namespace OAI
/-! # Charged reset node-book compilation over every paid field and block -/
namespace Hierarchy.DescentResetNodeBooks
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local DescentOrdinaryAtomFieldRAM DescentStaticWordColumn
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section

theorem work (floor old N H G s M p : ℕ) : (term floor old N H G s M p).work≤1+18*N :=by
  have aux (is : List (Fin N)) : (Gather.collect (tabs floor s N M)
      (fun n=>Expr.lookup (scalar old N H G M p n) .row) is).work≤1+18*is.length:=by
    induction is with
    | nil=>rfl
    | cons j js ih=>
      simp only [Gather.collect,Tables.read,Expr.work,List.length_cons,Nat.mul_succ] at *
      omega
  simpa only [term,Gather.assembly,List.length_finRange] using aux (List.finRange N)

theorem charged (floor old names N H G s M w : ℕ) :
    ticks floor old names N H G s M≤4+10*volume N s M+
      (4+names*(4+rows H G M*(2*(1+18*N)+4))) ∧
    DescentStaticWordColumn.names (program floor old names N H G s M w)≤15*(volume N s M+1)+
      (15+names*(11+4*(1+18*N))) :=by
  constructor
  · exact Nat.add_le_add_left (DescentPackedFlowBatch.tariff _ _ _ _ _ _
      (fun j _=>work floor old N H G s M j)) _
  · unfold program
    rw [names_seq,ROM.mount,names_mount]
    apply Nat.add_le_add_left
    exact DescentOperandVectorArena.names_passes _ _ _ _ _ _ 0 names (fun i _ _=>work floor old N H G s M i)

/-- Uniform instruction and bit accounting, including the true mounting of
all the shared dictionary pages. The group width pays the packed physical
rows and the capped literal ROM independently. -/
theorem paper (floor old names N H G s M w h u ratio R : ℕ)
    (pos : 0<u) (wide : 2*u≤h) (bus : w≤ratio*h) (aperture : (s*N+s)*M≤h/2)
    (packed : rows H G M≤R*Stage.DateBill.words H G h u) :
    w*ticks floor old names N H G s M+7*DescentStaticWordColumn.names (program floor old names N H G s M w) ≤
      2*((ratio+7)*((4+10*(N+1)+(4+names*(4+R*(2*(1+18*N)+4))))+
        (15*((N+1)+1)+(15+names*(11+4*(1+18*N))))))*Stage.DateBill.volumeBits H G h u := by
  let U:=Stage.DateBill.words H G h u
  let C:=4+10*(N+1)+(4+names*(4+R*(2*(1+18*N)+4)))
  let B:=15*((N+1)+1)+(15+names*(11+4*(1+18*N)))
  have dyadic : 2^(h/2)≤U:=by dsimp [U,Stage.DateBill.words];omega
  have positive : 1≤U :=(Nat.two_pow_pos _).trans_le dyadic
  have unit (k : ℕ) : k≤k*U :=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left k positive
  have dict : volume N s M≤(N+1)*U:=Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) aperture).trans dyadic)
  obtain ⟨cpu,isa⟩:=charged floor old names N H G s M w
  have t : ticks floor old names N H G s M≤C*U:=cpu.trans (calc
    _ ≤ (4*U+10*((N+1)*U))+(4*U+names*(4*U+(R*U)*(2*(1+18*N)+4))) :=by gcongr <;> first | exact unit _
    _ = C*U :=by dsimp [C];ring)
  have b : DescentStaticWordColumn.names (program floor old names N H G s M w)≤B*U:=isa.trans (calc
    _ ≤ 15*((N+1)*U+1*U)+(15*U+names*((11+4*(1+18*N))*U)):=by gcongr <;> first | exact unit _
    _ = B*U:=by dsimp [B];ring)
  have hp : 1≤h:=by omega
  have liftB :=Nat.mul_le_mul_left (B*U) hp
  have all:=Nat.add_le_add (Nat.mul_le_mul bus t) (Nat.mul_le_mul_left 7 (b.trans (by simpa only [Nat.mul_one] using liftB)))
  calc
    _ ≤ ratio*h*(C*U)+7*(B*U*h):=all
    _ ≤ (ratio+7)*(C+B)*(U*h):=by
      have e : ratio*h*(C*U)+7*(B*U*h)=(ratio*C+7*B)*(U*h):=by ring
      rw [e]
      apply Nat.mul_le_mul_right
      simp only [Nat.add_mul,Nat.mul_add];omega
    _ ≤ (ratio+7)*(C+B)*(2*Stage.DateBill.volumeBits H G h u):=
      Nat.mul_le_mul_left _ (Stage.DateBill.words_bits H G h u pos wide)
    _ = _:=by dsimp [C,B];ring

end
end Hierarchy.DescentResetNodeBooks

end OAI
