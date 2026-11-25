import OAI.Hierarchy.DescentPackedAllSeeds
import OAI.Hierarchy.DescentPackedColonyFrame

namespace OAI
/-! # Shared read-only tables and consecutive write arenas for ordinary trials -/
namespace Hierarchy.DescentPackedColony.Frame
open DescentColonies DescentSIMDLookup DescentGL ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {q Δ H G k b M w : ℕ}

def Chart.trialAt (A : Chart) (base Δ k b M : ℕ) : Layout Δ :=
  { A.issued Δ k b M with
    fresh := base
    source := fun s=>match s with
      | 0=>(A.issued Δ k b M).source 0
      | s+1=>⟨base+s*A.page,A.bits⟩ }

def startAt (base k page : ℕ) (i : Fin q) := base+i.val*((k+1)*page)

theorem trial_input (A : Chart) (base : ℕ) (rs : Fin H→Fin Δ→Option (Fin H)) (W : Fin G→Fin H→Block k→ℕ)
    (D cap : ℕ) (a μ : Bits k) (m : Memory w) (ready : Input (A.issued Δ k b M) rs W D cap b M a μ m) :
    Input (A.trialAt base Δ k b M) rs W D cap b M a μ m :=
  ⟨ready.topology, ready.counts, ready.empty, ready.base, ready.merge⟩

private theorem move_bank {B : Bank} {base finish : ℕ} (h : B.Fits w base) (le : base≤finish) : B.Fits w finish :=
  ⟨h.1,h.2.1,h.2.2.trans le⟩

private theorem move_words {W : DescentPackedZip.Tables} {a b base finish : ℕ}
    (h : WordRoom W a b M w base) (le : base≤finish) : WordRoom W a b M w finish :=
  ⟨move_bank h.shift le,move_bank h.apply le,h.shiftBits,h.applyBits⟩

theorem trial_hardware (A : Chart) {base : ℕ} (lim : Room A H G Δ k b M w)
    (below : A.fresh Δ k≤base) (upper : base+(k+1)*A.page<2^w) :
    Hardware (A.trialAt base Δ k b M) H G k b M w := by
  have old:=hardware A lim
  have small := (Nat.le_add_left .. : (k+1)*A.page≤base+(k+1)*A.page).trans_lt upper
  have page : A.page<2^w := (Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ k)).trans_lt small
  constructor
  · intro s hs
    have original := old.space s hs
    have next : ((A.issued Δ k b M).source (s+1)).base≤((A.trialAt base Δ k b M).source (s+1)).base :=
      Nat.add_le_add_right below _
    have src : ((A.trialAt base Δ k b M).source s).Fits w ((A.trialAt base Δ k b M).source (s+1)).base := by
      cases s with
      | zero=>exact move_bank original.neighbors.source next
      | succ j=>
        refine ⟨Nat.two_pow_pos _,page,?_⟩
        change base+j*A.page+A.page≤base+(j+1)*A.page
        rw [Nat.succ_mul,Nat.add_assoc]
    have n:=original.neighbors
    refine ⟨⟨fun i=>move_bank (n.ids i) next,n.idsRoom,move_bank n.roster next,n.rosterRoom,move_bank n.offsets next,
      n.offRoom,move_bank n.chunks next,n.chunkRoom,src,?_⟩,move_bank original.weight next,original.rows,
      move_words original.base next,move_words original.add next⟩
    cases s <;> exact lim.cells
  · intro s hs;exact Nat.le_add_right ..
  · intro s hs
    change base+s*A.page+H*chunks G M<2^w
    have used:=Nat.mul_le_mul_right A.page hs
    rw [Nat.succ_mul] at used
    have cnt:=lim.cells
    rw [Nat.succ_mul] at upper
    omega

theorem trial_low (A : Chart) {base first : ℕ} (lim : Room A H G Δ k b M w) (fixed : A.fresh Δ k≤first) :
    AllSeeds.SourceRoom (A.trialAt base Δ k b M) first H G k b M := by
  have l:=low A lim
  refine ⟨⟨fun i=>(l.ids i).trans fixed,l.roster.trans fixed,l.offsets.trans fixed,l.chunk.trans fixed,l.weight.trans fixed,
    fun s h=>(l.baseShift s h).trans fixed,fun s h=>(l.baseApply s h).trans fixed,
    fun s h=>(l.mergeShift s h).trans fixed,fun s h=>(l.mergeApply s h).trans fixed⟩,?_⟩
  exact ((Nat.add_le_add_left lim.cells _).trans (slot_before A (.initial : Slot Δ k))).trans fixed

theorem trial_panel_end (A : Chart) {base : ℕ} (lim : Room A H G Δ k b M w) (before : A.fresh Δ k≤base) :
    ((A.trialAt base Δ k b M).source k).base+H*chunks G M≤base+k*A.page := by
  cases k with
  | zero=>
    change (A.atSlot (.initial : Slot Δ 0)).base + H * chunks G M ≤ base + 0 * A.page
    rw [Nat.zero_mul, Nat.add_zero]
    exact ((Nat.add_le_add_left lim.cells _).trans (slot_before A (.initial : Slot Δ 0))).trans before
  | succ k=>
    change base+k*A.page+H*chunks G M≤base+(k+1)*A.page
    rw [Nat.succ_mul,←Nat.add_assoc];exact Nat.add_le_add_left lim.cells _

def allTrials (charts : Fin q→Chart) (base page Δ k b M : ℕ) (i : Fin q) :=
  (charts i).trialAt (startAt base k page i) Δ k b M

theorem allTrials_room (charts : Fin q→Chart) (base page : ℕ)
    (uniform : ∀i,(charts i).page=page) (conditions : ∀i,Room (charts i) H G Δ k b M w)
    (fixed : ∀i,(charts i).fresh Δ k≤base) (top : base+q*((k+1)*page)<2^w) :
    AllSeeds.ArrayRoom (allTrials charts base page Δ k b M) base H G k b M w := by
  have below (i : Fin q) : base≤ startAt base k page i:=Nat.le_add_right ..
  have segment (i : Fin q) : startAt base k page i+(k+1)*page≤base+q*((k+1)*page) := by
    have idx:=Nat.mul_le_mul_right ((k+1)*page) i.isLt
    rw [Nat.succ_mul] at idx
    dsimp [startAt];omega
  refine ⟨fun i=>trial_low _ (conditions i) (fixed i),below,fun i=>trial_hardware _ (conditions i)
    ((fixed i).trans (below i)) (by rw [uniform];exact (segment i).trans_lt top),?_⟩
  intro i j lt
  have e:=trial_panel_end (charts i) (conditions i) ((fixed i).trans (below i))
  apply e.trans
  change startAt base k page i+k*(charts i).page≤ startAt base k page j
  rw [uniform i]
  have step:=Nat.mul_le_mul_right ((k+1)*page) (show i.val+1≤j.val from lt)
  rw [Nat.succ_mul] at step
  dsimp only [startAt]
  rw [Nat.add_assoc]
  exact Nat.add_le_add_left
    ((Nat.add_le_add_left (Nat.mul_le_mul_right page (Nat.le_succ k)) _).trans step) base

end
end Hierarchy.DescentPackedColony.Frame

end OAI
