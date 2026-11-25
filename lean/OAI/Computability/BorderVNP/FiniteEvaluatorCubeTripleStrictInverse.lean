import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleStages
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleSound

/-! # Chronological directory and memory effects of every returning strict role -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeTriple

open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Physical.Owned
open BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows BorderVNP.Cube.Padding.Banks
open BorderVNP.Cube.TeamRowSources BorderVNP.Cube.Tally VPVNP.BurstRAM RoutingISA RoutingISA.OwnedStages
open scoped Classical

variable {w n blocks b h K s : ℕ} {l : TeamRowPrepare.Layout} {A : Data n l.d blocks b h K s}
variable {owner : Fin l.d → ℕ} {power base stop actual claimed : ℕ} {rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ}
variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {original m mt : Memory w} {r t : Bank w}
variable (P : PhysicalSetup A owner power base stop actual claimed rows pub original)

/-- The actual per-row postcondition needed to invert the complete program's
native loop. Its ordinal, limit, and triple cursor are all true register words. -/
structure StepReturn (A : Data n l.d blocks b h K s) (owner : Fin l.d → ℕ) (power base stop : ℕ)
    (v : Fin l.d × Fin l.d) (r : Bank w) (m : Memory w) (t : Bank w) (mt : Memory w) : Prop where
  next : Past (l := l) A owner base (key v+1) mt
  sourceWords : ∀ a ∈ source l power n, mt a=m a
  above : ∀ a, stop ≤ a → mt a=m a
  vertex : readings t 7=readings r 7+(if v.1=v.2 then 0 else 3*strictVertices n l.d blocks)
  cursor : readings t 22=key v
  bound : readings t 23=l.d*l.d

include P in
/-- Any successful strict role reads the public selector of the input packet
and appends precisely its owned vertices. The field deck and all previous
triple records survive arbitrary successful private choices. -/
theorem strict_step_sound (p : Symbols l.d) (high : Bool) (own : owner (oriented p high).1=l.teamID)
    (same : ∀ a ∈ source l power n, m a=original a)
    (old : Past (l := l) A owner base (key (oriented p high)) m)
    (cursor : readings r 7=base+3*vertexPrefix l (wordOwner owner) n blocks (key (oriented p high)))
    (prep : TeamRowPrepare.ReadyRow l (readings m) (key (oriented p high)) (.ofWords r m))
    {es} (run : Runs pub mac (strictRole n b h K s) r m es t mt) :
    StepReturn A owner power base stop (oriented p high) r m t mt := by
  let q := finProdFinEquiv (oriented p high)
  let out := base+3*vertexPrefix l (wordOwner owner) n blocks q.val
  let D := A.packet p high (l.view q.val) (l.crossing q.val)
  let S := A.side power l.header out
  have before : base ≤ out := Nat.le_add_right ..
  have room := P.strictRoom p high own
  have ready := strict_ready P.seed P.allocation p high r out cursor before room same prep (P.selectorWords p high own) (P.crossingWords p high own)
  have singleEnd := P.allocation.orderSingles
  have singles : A.singleBase ≤ base := (Nat.le_add_right ..).trans singleEnd
  have packets : A.packetBase ≤ A.singleBase := (Nat.le_add_right ..).trans P.allocation.orderPackets
  have subtotal : actual+(n+1) ≤ base := P.checker.beforeClaim.trans
    ((Nat.le_add_right ..).trans (P.checker.beforeBank.trans (packets.trans singles)))
  have scratch := P.afterScratch.trans singles
  have separated (a : ℕ) (ha : a ∈ source l power n) : a < out ∨ out+(2*blocks*(l.d.choose 2)^n)*(3*2^n) ≤ a := by
    exact (P.allocation.outside ha).elim (fun lo => .inl (lo.trans_le (packets.trans (singles.trans before))))
      (fun hi => .inr (room.trans hi))
  obtain ⟨x,z,_,entered,ret,_⟩ := strict_return_sound D S ready actual claimed rows (P.image.transfer same)
    P.checker P.labelsFit P.packetFit P.capFit separated P.checkSafe run
  let E := D.withWords x z
  have atRole : pairAt l.d q=oriented p high := finProdFinEquiv.symm_apply_apply _
  have records := strict_stored E S entered ret (subtotal.trans before) (scratch.trans before)
  have more : Past (l := l) A owner base (q.val+1) mt := by
    apply old.strict q p high atRole (atRole ▸ own)
    · intro a lo hi
      exact ret.directory_word entered a (singleEnd.trans lo) hi (subtotal.trans lo) (scratch.trans lo)
    · intro j
      have hit := records ⟨j.val,by simpa only [List.length_map,E,PacketRowData.withWords,D,Data.packet] using j.isLt⟩
      simp only [List.getElem_map] at hit ⊢
      exact hit
  have diff : (oriented p high).1≠(oriented p high).2 := by cases high <;> first | exact p.property.ne | exact p.property.ne'
  refine ⟨more,ret.source,?_,?_,ret.cursors.1.trans prep.cursor,ret.cursors.2.trans prep.bound⟩
  · intro a top
    have baseLe : base≤a := (before.trans ((Nat.le_add_right ..).trans room)).trans top
    obtain ⟨u,mu,side,check⟩ := ret.stages
    have upper := OwnedVertex.rowImage_above (blocks := blocks) A.axis p high A.packetBase
      (bankWidth n b h K s) (selectorWidth n K h) out (readings (scattered E S m)) (packetTrials n l.d blocks)
    dsimp only at upper
    rw [OwnedVertex.rowImage_cursor,OwnedVertex.selectedPrefix_end] at upper
    have scatter := scattered_after_singletons E S m a entered.stride.ge entered.packetsBeforeSingletons (singleEnd.trans baseLe)
    exact Fin.ext ((check.outside a ⟨.inr (subtotal.trans baseLe),.inr (scratch.trans baseLe)⟩).trans
      ((congrFun side.image a).trans ((upper a (room.trans top)).trans (congrArg Fin.val scatter))))
  · rw [ite_eq_right diff,cursor,ret.vertex]
    change out+(2*blocks*(l.d.choose 2)^n)*(3*2^n)=out+3*strictVertices n l.d blocks
    unfold strictVertices
    ring

end FiniteEvaluator.CubeTriple

end BorderVNP
end Computability
end OAI
