import OAI.Hierarchy.DescentPackedColonyRun
import OAI.Hierarchy.DescentColonyCandidateHardware

namespace OAI
/-! # Running every packed multiplier trial and retaining all candidate panels -/

namespace Hierarchy.DescentPackedColony.AllSeeds
open DescentColonies DescentGL DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {q Δ H G k b M w : ℕ}

def trial (w H G M k : ℕ) (L : Layout Δ) : NativeBatch.Code w :=
  let ps:=passes L H G M k
  ⟨program w ps,result ps,clock ps⟩

def search (w H G M k : ℕ) (L : Fin q→Layout Δ) :=
  NativeBatch.Code.seq (fun i=>trial w H G M k (L i)) q le_rfl

/-- Common input reads, including the initial all-present zero-split panel,
are below the first output of any trial. -/
structure SourceRoom (L : Layout Δ) (base H G k b M : ℕ) : Prop where
  immutable : Low {L with fresh:=base} H G k b M
  start : (L.source 0).base+H*chunks G M≤base

/-- Only ordering and capacity of actual written rows is used. -/
structure ArrayRoom (L : Fin q→Layout Δ) (base H G k b M w : ℕ) : Prop where
  low : ∀i,SourceRoom (L i) base H G k b M
  beginAt : ∀i,base≤(L i).fresh
  hardware : ∀i,Hardware (L i) H G k b M w
  next : ∀i j : Fin q,i<j→((L i).source k).base+H*chunks G M≤(L j).fresh

private theorem bank_copy (n m : Memory w) {base : ℕ} (same : ∀i<base,n i=m i)
    (B : Bank) (x : Fin H→Fin G→Cell b) (bb : B.base+H*chunks G M≤base) (old : Reads B x M m) : Reads B x M n :=
  fun p=>(same _ (by have :=(row H G M p).isLt;omega)).trans (old p)

theorem input_copy {base : ℕ} (L : Layout Δ) (space : SourceRoom L base H G k b M)
    (rs : Fin H→Fin Δ→Option (Fin H)) (W : Fin G→Fin H→Block k→ℕ) (D cap : ℕ) (a μ : Bits k)
    {m n : Memory w} (same : ∀i<base,n i=m i) (old : Input L rs W D cap b M a μ m) :
    Input L rs W D cap b M a μ n := by
  let lo:=space.immutable
  refine ⟨?_,bank_copy n m same L.weight _ lo.weight old.counts,bank_copy n m same (L.source 0) _ space.start old.empty,
    fun s hs=>static_congr _ _ m n base same (lo.baseShift s hs) (lo.baseApply s hs) (old.base s hs),
    fun s hs=>static_congr _ _ m n base same (lo.mergeShift s hs) (lo.mergeApply s hs) (old.merge s hs)⟩
  constructor
  · intro p i
    exact (same _ (by have :=lo.ids i;have :=(row H G M p).isLt;dsimp at *;omega)).trans (old.topology.ids p i)
  · intro v j
    have use := Nat.mul_le_mul_right Δ v.isLt
    rw [Nat.succ_mul] at use
    exact (same _ (by have :=lo.roster;have :=j.isLt;dsimp at *;omega)).trans (old.topology.roster v j)
  · intro v;exact (same _ (by have :=lo.offsets;have :=v.isLt;dsimp at *;omega)).trans (old.topology.offsets v)
  · intro p;exact (same _ (by have :=lo.chunk;have :=(row H G M p).isLt;dsimp at *;omega)).trans (old.topology.chunks p)

theorem low_mono {base : ℕ} (L : Layout Δ) (space : SourceRoom L base H G k b M) (before : base≤L.fresh) :
    Low L H G k b M :=
  ⟨fun i=>(space.immutable.ids i).trans before,space.immutable.roster.trans before,
    space.immutable.offsets.trans before,space.immutable.chunk.trans before,space.immutable.weight.trans before,
    fun s h=>(space.immutable.baseShift s h).trans before,fun s h=>(space.immutable.baseApply s h).trans before,
    fun s h=>(space.immutable.mergeShift s h).trans before,fun s h=>(space.immutable.mergeApply s h).trans before⟩

/-- All old split panels are in the very same post-memory and survive until the
native first-minimum. The result allows repeated input graphs and partial chunks. -/
theorem published {base : ℕ} (L : Fin q→Layout Δ) (space : ArrayRoom L base H G k b M w)
    (rs : Fin H→Fin Δ→Option (Fin H)) (W : Fin G→Fin H→Block k→ℕ) (D cap : ℕ)
    (a : Bits k) (seed : Fin q→Nonzero k) (small : ∀g v x,W g v x<2^b)
    (m : Memory w) (initial : ∀i,Input (L i) rs W D cap b M a (seed i).val m) :
    let P:=search w H G M k L
    P.text.Exec m (P.after m) P.ticks ∧ (∀z<base,P.after m z=m z) ∧ ∀i,
      Reads ((L i).source k) (PackedSplit.state (incoming (peers rs)) W D cap a (seed i)) M (P.after m) := by
  let code := fun i=>trial w H G M k (L i)
  have ok (i) : (code i).exec := fun mem=>(physical (L i) (space.hardware i) mem).1
  let low (mem : Memory w) := ∀z<base,mem z=m z
  let resultAt (i : Fin q) (mem : Memory w) :=
    Reads ((L i).source k) (PackedSplit.state (incoming (peers rs)) W D cap a (seed i)) M mem
  have reached := NativeBatch.Code.read_seq code low
    (fun i mem kept z hz=>(below (L i) (space.hardware i) mem le_rfl z (hz.trans_le (space.beginAt i))).trans (kept z hz))
    resultAt (fun i mem kept=>split_read (L i) (space.hardware i) (low_mono (L i) (space.low i) (space.beginAt i))
      rs W D cap a (seed i) small mem (input_copy (L i) (space.low i) rs W D cap a _ kept (initial i)))
    (fun i j lt mem old p=>(below (L j) (space.hardware j) mem le_rfl _
      (by have bound:=space.next i j lt;have key:=(row H G M p).isLt;omega)).trans (old p))
    m (fun _ _=>rfl) q le_rfl
  exact ⟨NativeBatch.Code.exec_seqAll code ok q le_rfl m,reached.1,fun i=>reached.2 i i.isLt⟩

theorem frame_above {z : ℕ} (L : Fin q→Layout Δ) (m : Memory w)
    (upper : ∀i (d : ℕ),d<k→((L i).source (d+1)).base+H*chunks G M≤z) :
    (search w H G M k L).after m z=m z := by
  apply NativeBatch.Code.frame_seq
  intro i before
  have fixed (s) (lower : s≤k) : result (passes (L i) H G M s) before z=before z := by
    induction s with
    | zero=>rfl
    | succ d ih=>
      rw [passes,result_append]
      exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inr (upper i d (by omega)))).trans (ih (by omega))
  exact fixed k le_rfl

theorem clock_bound (L : Fin q→Layout Δ) (w H G M k : ℕ) :
    (search w H G M k L).ticks≤4+q*(4+k*(4+H*chunks G M*(2*(25+56*Δ)+4))) :=
  NativeBatch.Code.clock_seq _ _ (fun i=>clock_price (L i) H G M k) _ _

theorem bit_price (L : Fin q→Layout Δ) (w H G k a : ℕ) (positive : 0<a) (wide : 2*a≤w) :
    (search w H G (lanes w a) k L).ticks*w ≤ (4+q*(4+k*(8+2*(25+56*Δ))))*(w+H*w+4*H*G*a) := by
  let u := w+H*w+4*H*G*a
  let n := H*chunks G (lanes w a)
  have nr : n*w≤u := (volume H G w a positive wide).trans (by dsimp [u];omega)
  have wr : w≤u := by dsimp [u];omega
  apply (Nat.mul_le_mul_right w (clock_bound L w H G (lanes w a) k)).trans
  calc
    _ = 4*w+q*(4*w+k*(4*w+n*w*(2*(25+56*Δ)+4))) := by dsimp [n];ring
    _ ≤ 4*u+q*(4*u+k*(4*u+u*(2*(25+56*Δ)+4))) := by gcongr
    _ = _ := by dsimp [u];ring

theorem storage (L : Fin q→Layout Δ) (w H G M k : ℕ) (live : 0<H*chunks G M) :
    let P:=search w H G M k L
    CandidateRAM.Bounded P.text P.ticks := by
  apply CandidateRAM.batch_bound
  intro i
  apply CandidateRAM.passes_bound
  intro p member
  obtain ⟨d,lt,rfl⟩:=pass_in (L i) H G M k member
  exact live

end
end Hierarchy.DescentPackedColony.AllSeeds

end OAI
