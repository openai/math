import OAI.Computability.BorderVNP.CubeTeamOwnedPhysicalSetup
import OAI.Computability.BorderVNP.CubeTeamOwnedRoleCosts

/-! # Genuine native role histories for every physical row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open Physical Physical.Owned Scatter Padding.Banks TeamRowSources Tally
open RoutingISA RoutingISA.Owned RoutingISA.OwnedStages VPVNP.BurstRAM

variable {w n blocks b h K s : ℕ} {l : TeamRowPrepare.Layout}

/-- The two possible verified native role histories on a directed symbol row. -/
inductive PhysicalStages (A : Data n l.d blocks b h K s) (power actual : ℕ)
    (pub : Arg → Word w) (r : Bank w) (m : Memory w) (t : Bank w) (mt : Memory w) :
    Fin l.d × Fin l.d → Prop
  | strict (p : Symbols l.d) (high : Bool) (out : ℕ)
      (ready : SideReady (A.packet p high (l.view (key (oriented p high))) (l.crossing (key (oriented p high))))
        (A.side power l.header out) pub (source l power n) r m)
      (result : StrictReturn (A.packet p high (l.view (key (oriented p high))) (l.crossing (key (oriented p high))))
        (A.side power l.header out) (source l power n) actual r m t mt) : PhysicalStages A power actual pub r m t mt
        (oriented p high)
  | diagonal (g : Fin l.d)
      (verified : LocalRow.Return h actual (LocalRow.head (rowLayout A l power) n b h K s)
        (readings r) (readings (A.rowMem g g (l.view (key (g,g))) (l.crossing (key (g,g))) m))
        (subtotals itemRow (crossCount b s A.select) A.axis (Sym2.mk g g)) (.ofWords t mt)) :
        PhysicalStages A power actual pub r m t mt (g,g)

/-- The native return carries the real bank writes, source preservation, all
three loop cursors, and the concrete scatter/checker stages. -/
structure PhysicalReturn (A : Data n l.d blocks b h K s) (power actual : ℕ)
    (pub : Arg → Word w) (v : Fin l.d × Fin l.d) (r : Bank w) (m : Memory w) (t : Bank w) (mt : Memory w) : Prop where
  vertex : readings t 7 = readings r 7 + (if v.1 = v.2 then 0 else 3*strictVertices n l.d blocks)
  cursor : readings t 22 = key v
  bound : readings t 23 = l.d*l.d
  sourceWords : ∀ x ∈ source l power n, mt x = m x
  bankWords : ∀ x, A.BankWord x → mt x = A.rowMem v.1 v.2 (l.view (key v)) (l.crossing (key v)) m x
  stages : PhysicalStages A power actual pub r m t mt v

variable {A : Data n l.d blocks b h K s} {owner : Fin l.d → ℕ} {power base stop actual claimed : ℕ}
variable {rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ} {pub : Arg → Word w} {original m : Memory w}

private theorem strict_ne (p : Symbols l.d) (high : Bool) : (oriented p high).1 ≠ (oriented p high).2 := by
  cases high
  · exact p.property.ne
  · exact p.property.ne'

private theorem strictTape (A : Data n l.d blocks b h K s) (p : Symbols l.d) (high : Bool) :
    let v := oriented p high
    let q := key v
    A.privateTapeAt l q = rowChoices packetTrialValid (A.packet p high (l.view q) (l.crossing q)).choices := by
  intro v q
  have hq : q < l.d*l.d := (finProdFinEquiv v).isLt
  have pair : pairAt l.d ⟨q,hq⟩ = v := finProdFinEquiv.symm_apply_apply v
  rw [Data.privateTapeAt,dite_eq_left hq,pair,Data.privateRowBits]
  cases high
  · exact dite_eq_left p.property
  · simp only [v,oriented,ite_true,Prod.fst_swap,Prod.snd_swap,Prod.swap_swap,
      dite_eq_right (not_lt_of_ge p.property.le),dite_eq_left p.property]

private theorem strictBank (A : Data n l.d blocks b h K s) (p : Symbols l.d) (high : Bool)
    (sel cross : ℕ) (m : Memory w) :
    A.rowMem (oriented p high).1 (oriented p high).2 sel cross m = A.strictMem p high sel cross m := by
  cases high
  · exact dite_eq_left p.property
  · simp only [Data.rowMem,oriented,ite_true,Prod.fst_swap,Prod.snd_swap,
      dite_eq_right (not_lt_of_ge p.property.le),dite_eq_left p.property]

/-- Execute an authentic strict row starting from the actual prepared registers and resident delivered streams. -/
theorem PhysicalSetup.strictRun (P : PhysicalSetup A owner power base stop actual claimed rows pub original)
    (mac : TeamOpcode.Macros w 8) (p : Symbols l.d) (high : Bool) (owned : owner (oriented p high).1 = l.teamID)
    (r : Bank w) (same : ∀ x ∈ source l power n, m x = original x)
    (output : readings r 7 = base+3*vertexPrefix l (wordOwner owner) n blocks (key (oriented p high)))
    (prep : TeamRowPrepare.ReadyRow l (readings m) (key (oriented p high)) (.ofWords r m)) :
    let v := oriented p high
    let q := key v
    TraceRun pub mac (strictRole n b h K s) r m (A.privateTapeAt l q) (physicalCostAt l blocks b h K s A.axis q)
      (PhysicalReturn A power actual pub v r m) := by
  intro v q
  let out := base+3*vertexPrefix l (wordOwner owner) n blocks q
  have before : base ≤ out := Nat.le_add_right ..
  have room := P.strictRoom p high owned
  have ready := strict_ready P.seed P.allocation p high r out output before room same prep
    (P.selectorWords p high owned) (P.crossingWords p high owned)
  have dir (x : ℕ) (hx : x ∈ source l power n) : x < out ∨ out+(2*blocks*(l.d.choose 2)^n)*(3*2^n) ≤ x := by
    rcases P.allocation.outside hx with low | hi
    · have packet : A.packetBase ≤ A.singleBase := (Nat.le_add_right ..).trans P.allocation.orderPackets
      have single : A.singleBase ≤ base := (Nat.le_add_right ..).trans P.allocation.orderSingles
      exact Or.inl (low.trans_le (packet.trans (single.trans before)))
    · exact Or.inr (room.trans hi)
  have run := strictRole_run (mac := mac) (A.packet p high (l.view q) (l.crossing q)) (A.side power l.header out) r m ready
    actual claimed rows (P.image.transfer same) P.checker P.labelsFit P.packetFit P.capFit P.authentic dir P.checkSafe
  rw [strictTape A p high,physicalCostAt_strict l A rfl p high (l.view q) (l.crossing q) power l.header out]
  apply run.mono le_rfl
  intro t mt ht
  have vertex : readings t 7 = out+(2*blocks*(l.d.choose 2)^n)*(3*2^n) := ht.vertex
  obtain ⟨u,mu,side,verified⟩ := ht.stages
  refine ⟨?_,ht.cursors.1.trans prep.cursor,ht.cursors.2.trans prep.bound,ht.source,?_,.strict p high out ready ht⟩
  · rw [ite_eq_right (strict_ne p high),output,vertex]
    simp only [strictVertices,out,q,v,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
  · intro x hx
    rw [strictBank A p high]
    exact (Fin.ext (verified.outside x (checker_bank_protected A power l.header actual claimed _
      P.checker P.afterScratch x hx))).trans (A.strictSide_words p high _ _ power l.header out ready side x hx)

/-- Execute the one-family diagonal callback, using the empty common crossing stream and the local private bits. -/
theorem PhysicalSetup.diagonalRun (P : PhysicalSetup A owner power base stop actual claimed rows pub original)
    (mac : TeamOpcode.Macros w 8) (g : Fin l.d) (r : Bank w) (same : ∀ x ∈ source l power n, m x = original x)
    (prep : TeamRowPrepare.ReadyRow l (readings m) (key (g,g)) (.ofWords r m)) :
    let q := key (g,g)
    TraceRun pub mac (diagonalRole n b h K s) r m (A.privateTapeAt l q) (physicalCostAt l blocks b h K s A.axis q)
      (PhysicalReturn A power actual pub (g,g) r m) := by
  intro q
  have room : base ≤ stop := (Nat.le_add_right ..).trans P.capacity
  have run := diagonalRole_dispatch_framed mac P.seed P.allocation g r room same prep P.image P.authentic
    P.checker P.labelsFit P.capFit P.afterScratch P.checkSafe
  rw [physicalCostAt_diagonal l A rfl g (l.view q) (l.crossing q)]
  apply run.mono le_rfl
  rintro t mt ⟨⟨vertex,cursor,bound,_,bank,src⟩,checked⟩
  exact ⟨by simpa only [ite_true,Nat.add_zero] using vertex,cursor,bound,src,bank,.diagonal g checked⟩

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
