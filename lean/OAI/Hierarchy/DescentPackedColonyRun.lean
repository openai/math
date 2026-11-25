import OAI.Hierarchy.DescentPackedColonyStep

namespace OAI
/-! # Counted native execution from packed old census to the common split and affine score banks -/
namespace Hierarchy.DescentPackedColony
open DescentSIMDLookup DescentColonies DescentColonies.PackedSplit DescentGL
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H G Δ M k a b c w : ℕ}

structure Layout (Δ : ℕ) where
  ports : Ports Δ
  weight : Bank
  source : ℕ→Bank
  base : ℕ→DescentPackedZip.Tables
  merge : ℕ→DescentPackedZip.Tables
  fresh : ℕ

structure Hardware (L : Layout Δ) (H G k b M w : ℕ) : Prop where
  space (s : ℕ) (lt : s<k) : StageRoom L.ports (L.source s) L.weight (L.base s) (L.merge s)
    H G k b M w (L.source (s+1)).base
  before (s : ℕ) (lt : s<k) : L.fresh≤(L.source (s+1)).base
  output (s : ℕ) (lt : s<k) : (L.source (s+1)).base+H*chunks G M<2^w

def pass (L : Layout Δ) (H G M s : ℕ) : Pass :=
  ⟨(L.source (s+1)).base,H*chunks G M,term L.ports (L.source s) L.weight H (L.base s) (L.merge s)⟩

def passes (L : Layout Δ) (H G M : ℕ) : ℕ→List Pass
  | 0=>[]
  | s+1=>passes L H G M s++[pass L H G M s]

theorem pass_in (L : Layout Δ) (H G M s : ℕ) {p : Pass} (hp : p∈passes L H G M s) :
    ∃j<s,p=pass L H G M j := by
  induction s with
  | zero=>simp [passes] at hp
  | succ s ih=>
    simp only [passes,List.mem_append,List.mem_singleton] at hp
    rcases hp with old|rfl
    · obtain ⟨j,sm,rfl⟩:=ih old
      exact ⟨j,by omega,rfl⟩
    · exact ⟨s,Nat.lt_succ_self _,rfl⟩

theorem pass_count (L : Layout Δ) (H G M s : ℕ) : (passes L H G M s).length=s := by
  induction s with
  | zero=>rfl
  | succ s ih=>simp [passes,ih]

theorem physical (L : Layout Δ) (S : Hardware L H G k b M w) (m : Memory w) :
    (program w (passes L H G M k)).Exec m (result (passes L H G M k) m) (clock (passes L H G M k)) ∧
      CheapCode (program w (passes L H G M k)) := by
  refine ⟨program_exec _ _ ?_,@ProtocolRAM.program_cheap _ _⟩
  intro p member
  obtain ⟨j,sm,rfl⟩:=pass_in L H G M k member
  exact ⟨term_fits _ _ _ _ _ _ (S.space j sm),S.output j sm⟩

theorem below (L : Layout Δ) (S : Hardware L H G k b M w) (m : Memory w) {s : ℕ} (sh : s≤k)
    (i : ℕ) (lt : i<L.fresh) : result (passes L H G M s) m i=m i := by
  induction s with
  | zero=>rfl
  | succ s ih=>
    rw [passes,result_append]
    have low : ¬(L.source (s+1)).base≤ i:=Nat.not_le_of_lt (lt.trans_le (S.before s (by omega)))
    simpa [result,Pass.apply,pass,ProtocolRAM.image,fillSegment,low] using ih (by omega)

/-- Every immutable parameter read is below the first layer. These are bounds on
addresses of actual public tables and measured input words. -/
structure Low (L : Layout Δ) (H G k b M : ℕ) : Prop where
  ids (q : Fin Δ) : (L.ports.ids q).base+H*chunks G M≤L.fresh
  roster : L.ports.roster.base+H*Δ≤L.fresh
  offsets : L.ports.offsets.base+H≤L.fresh
  chunk : L.ports.chunks.base+H*chunks G M≤L.fresh
  weight : L.weight.base+H*chunks G M≤L.fresh
  baseShift (s : ℕ) (lt : s<k) : (L.base s).shift.base+2^(width k*M)≤L.fresh
  baseApply (s : ℕ) (lt : s<k) : (L.base s).apply.base+2^((width k+b*2^k)*M)≤L.fresh
  mergeShift (s : ℕ) (lt : s<k) : (L.merge s).shift.base+2^(width k*M)≤L.fresh
  mergeApply (s : ℕ) (lt : s<k) : (L.merge s).apply.base+2^((width k+width k)*M)≤L.fresh

structure Input (L : Layout Δ) (rs : Fin H→Fin Δ→Option (Fin H)) (W : Fin G→Fin H→Block k→ℕ)
    (D cap b M : ℕ) (a μ : Bits k) (m : Memory w) : Prop where
  topology : Mounted L.ports rs m G M
  counts : Reads L.weight (fun v g=>DescentPackedColony.counts b (W g v)) M m
  empty : Reads (L.source 0) (stateAt rs W D cap a μ 0) M m
  base (s : ℕ) (lt : s<k) : DescentPackedZip.Static (L.base s) (baseUpdate (b:=b) a μ cap (k-(s+1))) M m
  merge (s : ℕ) (lt : s<k) : DescentPackedZip.Static (L.merge s) (DescentPackedColony.merge (k:=k) D (k-(s+1))) M m

theorem static_congr (T : DescentPackedZip.Tables) (f : Cell a→Cell b→Cell c) (m n : Memory w) (lo : ℕ)
    (frame : ∀i<lo,n i=m i) (left : T.shift.base+2^(a*M)≤lo) (right : T.apply.base+2^((a+b)*M)≤lo)
    (prior : DescentPackedZip.Static T f M m) : DescentPackedZip.Static T f M n := by
  constructor
  · intro i
    rw [frame _ (by have := i.isLt;omega),prior.1]
  · intro i
    rw [frame _ (by have := i.isLt;omega),prior.2]

theorem produced (L : Layout Δ) (S : Hardware L H G k b M w) (lo : Low L H G k b M)
    (rs : Fin H→Fin Δ→Option (Fin H)) (W : Fin G→Fin H→Block k→ℕ) (D cap : ℕ) (a μ : Bits k)
    (room : ∀g v x,W g v x<2^b) (m : Memory w) (inp : Input L rs W D cap b M a μ m)
    (s : ℕ) (sh : s≤k) :
    Reads (L.source s) (stateAt rs W D cap a μ s) M (result (passes L H G M s) m) := by
  induction s with
  | zero=>exact inp.empty
  | succ s ih=>
    let low:=L.fresh
    let n:=result (passes L H G M s) m
    have smaller : s<k := by omega
    have frame (i : ℕ) (lt : i<L.fresh) : n i=m i := below L S m smaller.le i lt
    have top : Mounted L.ports rs n G M := by
      constructor
      · intro p i
        rw [frame _ (by have :=lo.ids i;have := (row H G M p).isLt;omega),inp.topology.ids]
      · intro v q
        have hi : v.val*Δ+q.val<H*Δ := by
          have :=Nat.mul_le_mul_right Δ (Nat.succ_le_of_lt v.isLt)
          rw [Nat.succ_mul] at this
          have := q.isLt
          omega
        rw [frame _ (by have:=lo.roster;omega),inp.topology.roster]
      · intro v
        rw [frame _ (by have:=lo.offsets;have:=v.isLt;omega),inp.topology.offsets]
      · intro p
        rw [frame _ (by have:=lo.chunk;have:=(row H G M p).isLt;omega),inp.topology.chunks]
    have wt : Reads L.weight (fun v g=>counts b (W g v)) M n := by
      intro p
      rw [frame _ (by have:=lo.weight;have:=(row H G M p).isLt;omega),inp.counts p]
    have src:=term_read L.ports (L.source s) L.weight (L.base s) (L.merge s) _ (S.space s smaller)
      n rs top W D cap a μ s smaller room
      (static_congr _ _ m n L.fresh frame (lo.baseShift s smaller) (lo.baseApply s smaller) (inp.base s smaller))
      (static_congr _ _ m n L.fresh frame (lo.mergeShift s smaller) (lo.mergeApply s smaller) (inp.merge s smaller))
      (ih smaller.le) wt
    intro p
    rw [passes,result_append]
    have ip:=(row H G M p).isLt
    simpa [result,Pass.apply,pass,ProtocolRAM.image,fillSegment,n,show (L.source (s+1)).base≤
      (L.source (s+1)).base+(row H G M p).val ∧ (L.source (s+1)).base+(row H G M p).val<
      (L.source (s+1)).base+H*chunks G M by omega,Nat.cast_add] using src p

theorem split_read (L : Layout Δ) (S : Hardware L H G k b M w) (lo : Low L H G k b M)
    (rs : Fin H→Fin Δ→Option (Fin H)) (W : Fin G→Fin H→Block k→ℕ) (D cap : ℕ) (a : Bits k) (μ : Nonzero k)
    (room : ∀g v x,W g v x<2^b) (m : Memory w) (inp : Input L rs W D cap b M a μ.val m) :
    Reads (L.source k) (PackedSplit.state (incoming (peers rs)) W D cap a μ) M
      (result (passes L H G M k) m) :=
  produced L S lo rs W D cap a μ.val room m inp k le_rfl

theorem clock_price (L : Layout Δ) (H G M k : ℕ) :
    clock (passes L H G M k)≤4+k*(4+H*chunks G M*(2*(25+56*Δ)+4)) := by
  have bounds (z : Pass) (hz : z∈passes L H G M k) : z.rows≤H*chunks G M ∧ z.term.work≤25+56*Δ := by
    obtain ⟨s,_,rfl⟩:=pass_in L H G M _ hz
    exact ⟨le_rfl,(term_work ..).le⟩
  simpa only [pass_count] using clock_le (passes L H G M k) (H*chunks G M) (25+56*Δ) bounds

end
end Hierarchy.DescentPackedColony

end OAI
