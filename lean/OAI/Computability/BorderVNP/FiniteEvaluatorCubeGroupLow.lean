import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleSound
import OAI.Computability.BorderVNP.CubeTeamOwnedDiagonalSound

/-! # Survival of the original packed geometry in each native owner callback

The genuine packet and singleton scatter starts above the geometry. The
vertex append follows both banks, and the local checker touches its subtotal
and descriptor arrays. Consequently any returning row preserves every word
below the subtotal base even for private choices different from a supplied witness.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeTriple

open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Physical.Owned
open BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows BorderVNP.Cube.Padding.Banks
open BorderVNP.Cube.TeamRowSources BorderVNP.Cube.Tally VPVNP.BurstRAM RoutingISA RoutingISA.OwnedStages
open scoped Classical

private theorem scattered_low {n d blocks b h K s w : ℕ} (D : PacketRowData n d blocks b h K s) (S : SideData n d blocks b h)
    (m : Memory w) (x : ℕ) (packet : x < D.base) (single : x < S.bank) : scattered D S m x = m x := by
  let st := D.before m (packetTrials n d blocks)
  let lo := D.singletonRow D.pair.val.1 D.pair.val.2 S.bank st.sel st.cross S.value
  let next := lo.before st.mem (singlePairTrials n d)
  let hi := D.singletonRow D.pair.val.2 D.pair.val.1 S.bank st.sel next.1 S.value
  change (hi.before next.2 _).2 x = _
  rw [hi.final_outside _ _ x (.inl single)]
  change (lo.before st.mem _).2 x = _
  rw [lo.final_outside _ _ x (.inl single)]
  exact D.before_invariant m (fun u => u x=m x) rfl (fun p _ z old =>
    (D.visit_outside p z x (.inl (packet.trans_le (Nat.le_add_right ..)))).trans old) _ le_rfl

variable {w n blocks b h K s : ℕ} {l : TeamRowPrepare.Layout} {A : Data n l.d blocks b h K s}
variable {owner : Fin l.d → ℕ} {power base stop actual claimed : ℕ} {rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ}
variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {original m mt : Memory w} {r t : Bank w}
variable (P : PhysicalSetup A owner power base stop actual claimed rows pub original)

include P in
private theorem low_banks : actual ≤ A.packetBase ∧ A.packetBase ≤ A.singleBase ∧ A.singleBase ≤ base := by
  exact ⟨(Nat.le_add_right ..).trans (P.checker.beforeClaim.trans ((Nat.le_add_right ..).trans P.checker.beforeBank)),
    (Nat.le_add_right ..).trans P.allocation.orderPackets,(Nat.le_add_right ..).trans P.allocation.orderSingles⟩

include P in
private theorem strict_low (p : Symbols l.d) (high : Bool) (own : owner (oriented p high).1=l.teamID)
    (same : ∀ a ∈ source l power n, m a=original a)
    (cursor : readings r 7=base+3*vertexPrefix l (wordOwner owner) n blocks (key (oriented p high)))
    (prep : TeamRowPrepare.ReadyRow l (readings m) (key (oriented p high)) (.ofWords r m))
    {es} (run : Runs pub mac (strictRole n b h K s) r m es t mt) : ∀ x < actual, mt x=m x := by
  let q := key (oriented p high)
  let out := base+3*vertexPrefix l (wordOwner owner) n blocks q
  let D := A.packet p high (l.view q) (l.crossing q)
  let S := A.side power l.header out
  obtain ⟨subtotal,packet,single⟩ := low_banks P
  have before : base ≤ out := Nat.le_add_right ..
  have room := P.strictRoom p high own
  have ready := strict_ready P.seed P.allocation p high r out cursor before room same prep (P.selectorWords p high own) (P.crossingWords p high own)
  have sep (a : ℕ) (ha : a ∈ source l power n) : a < out ∨ out+(2*blocks*(l.d.choose 2)^n)*(3*2^n) ≤ a :=
    (P.allocation.outside ha).elim (fun lo => .inl (lo.trans_le (packet.trans (single.trans before)))) (fun hi => .inr (room.trans hi))
  obtain ⟨dem,sup,_,_,ret,_⟩ := strict_return_sound D S ready actual claimed rows (P.image.transfer same) P.checker
    P.labelsFit P.packetFit P.capFit sep P.checkSafe run
  let E := D.withWords dem sup
  obtain ⟨u,mu,side,check⟩ := ret.stages
  intro x lower
  have lo := lower.trans_le subtotal
  have head : A.packetBase ≤ LocalRow.head (layout E S.power S.header) n b h K s := LocalRow.bank_le_head (layout E S.power S.header) n b h K s
  have vertex := (OwnedVertex.rowImage_frame (blocks := blocks) E.axis E.pair E.high E.base E.stride (selectorWidth n K h)
    S.out (readings (scattered E S m)) (packetTrials n l.d blocks)).2 x (lo.trans_le (packet.trans (single.trans before)))
  exact Fin.ext ((check.outside x ⟨.inl lower,.inl (lo.trans_le head)⟩).trans
    ((congrFun side.image x).trans (vertex.trans (congrArg Fin.val (scattered_low E S m x lo (lo.trans_le packet))))))

include P in
private theorem diagonal_low (g : Fin l.d) (same : ∀ a ∈ source l power n, m a=original a)
    (prep : TeamRowPrepare.ReadyRow l (readings m) (key (g,g)) (.ofWords r m))
    {es} (run : Runs pub mac (diagonalRole n b h K s) r m es t mt) : ∀ x < actual, mt x=m x := by
  let L := rowLayout A l power
  let q := key (g,g)
  let D := A.single g g (l.view q) (l.crossing q)
  have ready := diagonal_ready P.seed P.allocation g r ((Nat.le_add_right ..).trans P.capacity) same prep
  have protect : OwnedStages.Protected L n (pub 0).val (source l power n) := by
    change OwnedStages.Protected _ _ (readings pub 0) _
    rw [P.seed.frame]
    exact frame_protected
  obtain ⟨gs,u,mu,hs,rfl,stage,checker⟩ := CellDispatch.seq_split run
  let E := D.withTape (ChoiceTape.extend (gs.flatMap TeamRAM.Event.choices))
  obtain ⟨_,_,held,_,_,image⟩ := singleStage_recover pub mac L D (source l power n) r m ready.entry
    ready.selector ready.crossing ready.loaded ready.fit ready.prepared ready.fields.1 ready.fields.2 ready.labels
    ready.bank ready.room.frameFit ready.room.keys ready.room.allocation stage
  change mu = (E.before m (singlePairTrials n l.d)).2 at image
  have keep x (hx : x ∈ source l power n) : mu x=m x :=
    (congrFun image x).trans (E.before_source m (D.prepared_withTape _ m ready.prepared) _ x hx)
  have input := (P.image.transfer same).transfer keep
  have en := ready.entry.keep held
  have checked := (LocalRow.diagonalChecked_run pub mac u mu L A.axis g b h K s actual claimed A.select rows
    (protect.loaded ready.loaded keep) input.actualAt input.claimedAt input.table P.checker rfl P.labelsFit P.capFit
    en.zero en.one en.axis en.left en.right).sound checker
  obtain ⟨subtotal,packet,_⟩ := low_banks P
  have head : A.packetBase ≤ LocalRow.head L n b h K s := LocalRow.bank_le_head L n b h K s
  intro x lower
  exact (Fin.ext (checked.2.outside x ⟨.inl lower,.inl (lower.trans_le (subtotal.trans head))⟩)).trans
    ((congrFun image x).trans (E.final_outside _ _ x (.inl (lower.trans_le (subtotal.trans packet)))))

include P in
/-- The complete strict or diagonal callback preserves the packed geometry below
the local subtotal, on every actual return with the publicly assigned owner. -/
theorem role_low (v : Fin l.d × Fin l.d) (own : owner v.1=l.teamID)
    (same : ∀ a ∈ source l power n, m a=original a)
    (cursor : readings r 7=base+3*vertexPrefix l (wordOwner owner) n blocks (key v))
    (prep : TeamRowPrepare.ReadyRow l (readings m) (key v) (.ofWords r m))
    {es} (run : Runs pub mac (if v.1=v.2 then diagonalRole n b h K s else strictRole n b h K s) r m es t mt) :
    ∀ x < actual, mt x=m x := by
  rcases v with ⟨u,z⟩
  change Runs pub mac (if u=z then _ else _) _ _ _ _ _ at run
  rcases lt_trichotomy u z with less|rfl|greater
  · rw [ite_eq_right less.ne] at run
    exact strict_low P ⟨(u,z),less⟩ false own same cursor prep run
  · rw [ite_eq_left rfl] at run
    exact diagonal_low P u same prep run
  · rw [ite_eq_right greater.ne'] at run
    exact strict_low P ⟨(z,u),greater⟩ true own same cursor prep run

end FiniteEvaluator.CubeTriple

end BorderVNP
end Computability
end OAI
