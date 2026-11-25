import OAI.Hierarchy.DescentPackedCensusAny

namespace OAI
/-! # The census ingress preserves words outside its arena on every input -/
namespace Hierarchy.DescentPackedColumnSum
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {n w : ℕ}

theorem after_outside (base out u M width H G : ℕ) (b : Fin n→ℕ) (f : ∀i,Cell (b i)→ℕ)
    (src : Fin n→Expr) (m : Memory w) (sep : finish base n u M≤out) (a : ℕ)
    (away : a<base ∨ out+H*chunks G M≤a) :
    after base out u M width H G b f src m a=m a := by
  have left : base≤out := (Nat.le_add_right ..).trans sep
  rcases away with lower|upper
  · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ a (.inl (lower.trans_le left))).trans
      (DescentStaticWordColumn.frame _ _ _ _ a (.inl lower))
  · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ a (.inr upper)).trans
      (DescentStaticWordColumn.frame _ _ _ _ a (.inr (sep.trans ((Nat.le_add_right ..).trans upper))))

end
end Hierarchy.DescentPackedColumnSum

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census
open DescentSIMDLookup DescentPackedColumnSum ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {w : ℕ}

theorem any_framed (k D cap b u M H G origin out : ℕ) (hubBank : Bank) (atoms : Fin (2^k)→Expr)
    (wires : Fin (2^k)→Fin (2*cap)→Bank) (m : Memory w)
    (covered : max 1 (max b (DescentSignedCableCodec.width D cap))≤u) (fit : hubBank.Fits w origin)
    (aFit : ∀x,(atoms x).Fits w origin) (wFit : ∀x j,(wires x j).Fits w origin)
    (low : finish (beginSum origin H G M) (columns (2^k) cap) u M≤out)
    (room : out+H*chunks G M<2^w) :
    let n:=H*chunks G M
    let r:=2^k
    let start:=beginSum origin H G M
    let col:=order r cap
    let bits:=fun i=>width D cap b (col.symm i)
    let func:=fun i=>contribution D cap b (col.symm i)
    let f:=Broadcast.result hubBank origin H G M
    let src:=fun i=>expr f atoms (fun x j=>Expr.lookup (wires x j) .row) (col.symm i)
    let wide:=(1+b+2*(2*cap))*r
    let warm:=DescentStaticWordColumn.image origin (Broadcast.literal H G M) m (2*n)
    let final:=DescentPackedColumnSum.after start out u M wide H G bits func src warm
    ((DescentStaticWordColumn.program w origin (Broadcast.literal H G M) (2*n)).seq
      (DescentPackedColumnSum.program w start out u M wide H G bits func src)).Exec m
      final ((4+10*(2*n))+DescentPackedColumnSum.ticks start u M H G bits src) ∧
      ∀a,a<origin ∨ out+n≤a → final a=m a := by
  intro n r start col bits func f src wide warm final
  refine ⟨any k D cap b u M H G origin out hubBank atoms wires m covered fit aFit wFit low room,?_⟩
  have left : origin ≤ start := by
    change origin≤origin+n+2^(Broadcast.widthBits H G M)
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have count : n≤2^(Broadcast.widthBits H G M) :=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have uploadEnd : origin+2*n ≤ start := by
    change origin+2*n≤origin+n+2^(Broadcast.widthBits H G M)
    omega
  have sumEnd : start≤out := (Nat.le_add_right ..).trans low
  intro a away
  rcases away with lower|upper
  · exact (after_outside start out u M wide H G bits func src warm low a (.inl (lower.trans_le left))).trans
      (DescentStaticWordColumn.frame _ _ _ _ a (.inl lower))
  · exact (after_outside start out u M wide H G bits func src warm low a (.inr upper)).trans
      (DescentStaticWordColumn.frame _ _ _ _ a (.inr (uploadEnd.trans (sumEnd.trans ((Nat.le_add_right ..).trans upper)))))

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census

end OAI
