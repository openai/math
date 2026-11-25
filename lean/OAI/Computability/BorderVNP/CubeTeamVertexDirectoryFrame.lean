import OAI.Computability.BorderVNP.CubeTeamOwnedRole
import OAI.Computability.BorderVNP.CubeTeamOwnedPhysicalSetup

/-! # Retention of earlier native vertex triples at strict and diagonal visits

The packet and singleton stores lie below the directory's starting address.
The subsequent checker touches only its local subtotal and descriptor regions.
At a strict visit the vertex append begins at the current cursor, so every
previous record remains available without including it in the routed source set.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.OwnedStages Physical Physical.Owned Scatter Padding.Banks Tally VPVNP.BurstRAM

variable {w n d blocks b h K s : ℕ}

/-- The concrete packet scatter and the two oriented singleton scatters all leave
addresses past the singleton allocation alone. -/
theorem scattered_after_singletons (D : PacketRowData n d blocks b h K s) (A : SideData n d blocks b h)
    (m : Memory w) (x : ℕ) (stride : bankWidth n b h K s ≤ D.stride)
    (pack : D.base+(d*d)^(n+1)*2*blocks*D.stride ≤ A.bank)
    (singles : A.bank+d^(n+1)*d^(n+1)*(blocks*(h*b)) ≤ x) : scattered D A m x = m x := by
  let st := D.before m (packetTrials n d blocks)
  let lo := D.singletonRow D.pair.val.1 D.pair.val.2 A.bank st.sel st.cross A.value
  let next := lo.before st.mem (singlePairTrials n d)
  let hi := D.singletonRow D.pair.val.2 D.pair.val.1 A.bank st.sel next.1 A.value
  change (hi.before next.2 _).2 x = _
  rw [hi.final_outside _ _ x (.inr singles)]
  change (lo.before st.mem _).2 x = _
  rw [lo.final_outside _ _ x (.inr singles)]
  apply D.before_invariant m (fun u => u x = m x) rfl _ _ le_rfl
  intro p _ z old
  apply (D.visit_outside p z x (.inr ?_)).trans old
  have endBound := Nat.mul_le_mul_right D.stride (LocalRow.index_lt p)
  rw [Nat.succ_mul] at endBound
  have upper := pack.trans ((Nat.le_add_right ..).trans singles)
  change D.base + packetIndex p*D.stride + bankWidth n b h K s ≤ x
  omega

/-- A word of an already emitted triple survives both the actual strict-side
scatter/append and the subsequent native declaration check. -/
theorem StrictReturn.directory_word {D : PacketRowData n d blocks b h K s} {A : SideData n d blocks b h}
    {pub : Arg → Word w} {src : Set ℕ} {actual : ℕ} {r t : Bank w} {m mt : Memory w}
    (ready : SideReady D A pub src r m) (ret : StrictReturn D A src actual r m t mt) (x : ℕ)
    (singles : A.bank+d^(n+1)*d^(n+1)*(blocks*(h*b)) ≤ x) (old : x < A.out)
    (subtotal : actual+(n+1) ≤ x) (scratch : LocalRow.head (layout D A.power A.header) n b h K s+8+h ≤ x) :
    mt x = m x := by
  obtain ⟨u,mu,side,check⟩ := ret.stages
  have eqCheck := check.outside x ⟨.inr subtotal,.inr scratch⟩
  have eqAppend := (OwnedVertex.rowImage_frame (blocks := blocks) D.axis D.pair D.high D.base D.stride
    (selectorWidth n K h) A.out (readings (scattered D A m)) (packetTrials n d blocks)).2 x old
  have eqScatter := scattered_after_singletons D A m x ready.stride.ge ready.packetsBeforeSingletons singles
  exact Fin.ext (eqCheck.trans (((congrFun side.image x).trans eqAppend).trans (congrArg Fin.val eqScatter)))

/-- On the allocated team frame every past triple is protected. The bound follows
from the native allocation and checker layout even for addresses outside the input source set. -/
theorem PhysicalSetup.strict_directory_word {l : TeamRowPrepare.Layout} {A : Data n l.d blocks b h K s}
    {owner : Fin l.d → ℕ} {power base stop actual claimed : ℕ}
    {rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ} {pub : Arg → Word w} {original m mt : Memory w}
    {r t : Bank w} {src : Set ℕ} (P : PhysicalSetup A owner power base stop actual claimed rows pub original)
    (pair : Symbols l.d) (high : Bool) (sel cross out : ℕ)
    (ready : SideReady (A.packet pair high sel cross) (A.side power l.header out) pub src r m)
    (ret : StrictReturn (A.packet pair high sel cross) (A.side power l.header out) src actual r m t mt)
    {x : ℕ} (past : base ≤ x) (below : x < out) : mt x = m x := by
  have highBank := P.allocation.orderSingles.trans past
  have scratch := P.afterScratch.trans ((Nat.le_add_right ..).trans highBank)
  have subtotal : actual+(n+1) ≤ A.packetBase :=
    P.checker.beforeClaim.trans ((Nat.le_add_right ..).trans P.checker.beforeBank)
  have packet : A.packetBase ≤ LocalRow.head (TeamRowSources.rowLayout A l power) n b h K s :=
    LocalRow.bank_le_head (TeamRowSources.rowLayout A l power) n b h K s
  exact ret.directory_word ready x highBank below
    (subtotal.trans (packet.trans ((Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans scratch)))) scratch

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
