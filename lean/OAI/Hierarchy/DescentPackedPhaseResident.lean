import OAI.Hierarchy.DescentImage
import OAI.Hierarchy.DescentPackedPhaseLayout

namespace OAI
/-! # Placing every future ordinary ROM in the original memory image -/
namespace Hierarchy.DescentPackedColony.Phase
open _root_.OAI.Hierarchy.DescentPackedColony.Frame DescentColonies DescentGL DescentSIMDLookup DescentBinaryField DescentAffineColors ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {k b h w H G M Δ ℓ : ℕ}

theorem initial_congr (S : Shelves k Δ) (space : Space S w (2^ℓ) G b M) (hk : 0<k)
    (rs : DynamicSplit.Roster ℓ Δ) (W amt : Fin G→Fin (2^ℓ)→Block k→ℕ) (D cap : ℕ) (m n : Memory w)
    (agree : ∀z<S.first,n z=m z) (old : Initial S hk rs W amt D cap b M m) :
    Initial S hk rs W amt D cap b M n := by
  refine ⟨fun i=>AllSeeds.input_copy (S.layers i) (space.trials.low i) rs W D cap _ _ agree (old.graph i),
    fun p=>(agree _ (by have:=space.countLow;have:=(row (2^ℓ) G M p).isLt;omega)).trans (old.amounts p),
    fun i=>static_congr _ _ m n S.first agree (space.zipLow i).1 (space.zipLow i).2 (old.zip i),
    fun i t=>?_,fun j t=>?_,fun x i j t=>(agree _ (PackedWinnerRAM.entry_low space.paintRom x i j t)).trans (old.names x i j t)⟩
  · have room:=space.splitRom i
    have small : t.val<(S.split.dictionary i).size := by simpa only [Bank.size,space.split.fields i] using t.isLt
    exact (agree _ (by omega)).trans (old.split i t)
  · have room:=space.colorRom j
    have small : t.val<(S.color.dictionary j).size := by simpa only [Bank.size,space.color.fields j] using t.isLt
    exact (agree _ (by omega)).trans (old.color j t)

namespace Arena

def image (A : Chart) (hk : 0<k) (Δ H G b h D cap : ℕ) : Image w :=
  ⟨A.origin,first A Δ k b h,memory A hk Δ H G b h D cap (fun _=>0)⟩

private theorem memory_at (A : Chart) (hk : 0<k) (Δ H G b h D cap : ℕ)
    (m n : Memory w) (u : ℕ) (same : m u=n u) :
    memory A hk Δ H G b h D cap m u=memory A hk Δ H G b h D cap n u := by
  simp only [memory,PackedWinnerRAM.mount,Computability.VPVNP.RAMMemory.initialMemory,Menu.mount,
    Frame.Chart.mountAll,Frame.Chart.mount,same]

/-- At a later epoch only the current predecessor words are new. The retained
ROM reads were installed in the original header once. -/
theorem initial_resident (A : Chart) (amtBank : Bank) (hk : 0<k) (D cap : ℕ)
    (C : Room A amtBank Δ k b h w (2^ℓ) G) (rs : DynamicSplit.Roster ℓ Δ)
    (W amt : Fin G→Fin (2^ℓ)→Block k→ℕ) (m : Memory w)
    (original : (image A hk Δ (2^ℓ) G b h D cap).Resident m)
    (resident : ∀v i,m (A.roster.base+(v.val*Δ+i.val))=(target (rs v i):Word w))
    (wt : Reads A.weights (fun v g=>counts b (W g v)) (lanes h (unit k b)) m)
    (outgoing : Reads amtBank (fun v g=>counts b (amt g v)) (lanes h (unit k b)) m) :
    Initial (shelves A amtBank Δ k b h) hk rs W amt D cap b (lanes h (unit k b)) m := by
  let M:=lanes h (unit k b)
  let source:=fun z=>if z<A.origin then m z else 0
  have early (z) (lt : z<A.origin) : source z=m z := ite_eq_left lt
  have oldTop (v : Fin (2^ℓ)) (i : Fin Δ) : source (A.roster.base+(v.val*Δ+i.val))=(target (rs v i):Word w) := by
    let n : Fin (2^k-1):=⟨0,by have:=Nat.one_lt_pow (Nat.ne_of_gt hk) (by decide : 1<2);omega⟩
    have bound := (C.charts n).topSize
    have edge:=Nat.mul_le_mul_right Δ v.isLt
    rw [Nat.succ_mul] at edge
    exact (early _ (by have:=i.isLt;have:=C.roster;change 2^ℓ*Δ≤A.roster.size at bound;omega)).trans (resident v i)
  have oldWeight (p : Row (2^ℓ) G M) :
    source (A.weights.base+(row (2^ℓ) G M p).val)=((data (fun v g=>counts b (W g v)) p).val:Word w) := by
    let n : Fin (2^k-1):=⟨0,by have:=Nat.one_lt_pow (Nat.ne_of_gt hk) (by decide : 1<2);omega⟩
    have capW : (2^ℓ)*chunks G M≤A.weights.size := (C.charts n).wtSize
    exact (early _ (by have:=(row (2^ℓ) G M p).isLt.trans_le capW;have:=C.weights;omega)).trans (wt p)
  have genuine := initial A amtBank hk D cap C rs W amt source oldTop oldWeight
    (fun p=>(early _ ((Nat.add_lt_add_left ((row (2^ℓ) G M p).isLt.trans_le C.rows) amtBank.base).trans_le
      C.counts.2.2)).trans (outgoing p))
  apply initial_congr _ (space A amtBank hk (2^ℓ) G C) hk rs W amt D cap _ _ _ genuine.1
  intro z hz
  by_cases lower : z<A.origin
  · exact (early z lower).symm.trans ((genuine.2 z lower).symm)
  · exact (original z (Nat.le_of_not_gt lower) hz).trans
      ((memory_at A hk Δ (2^ℓ) G b h D cap source (fun _=>0) z (ite_eq_right lower)).symm)

/-- One global header over a finite calendar, with arbitrary source memory on
unoccupied addresses. Neither a later site choice nor a RAM return is an input. -/
def mountSchedule {n : ℕ} (schedule : Fin n→Image w) (old : Memory w) (z : ℕ) : Word w :=
  if found : ∃i,(schedule i).low≤z ∧ z<(schedule i).stop then (schedule found.choose).value z else old z

theorem schedule_resident {n : ℕ} (schedule : Fin n→Image w) (old : Memory w)
    (separate : ∀i j : Fin n,i<j→(schedule i).stop≤(schedule j).low) (i : Fin n) :
    (schedule i).Resident (mountSchedule schedule old) := by
  intro z low high
  have found : ∃j,(schedule j).low≤z ∧ z<(schedule j).stop := ⟨i,low,high⟩
  have unique : found.choose=i := by
    rcases lt_trichotomy found.choose i with lt|eqn|gt
    · have endAt:=separate _ _ lt;have:=found.choose_spec.2;omega
    · exact eqn
    · have endAt:=separate _ _ gt;have:=found.choose_spec.1;omega
  rw [mountSchedule,dite_eq_left found,unique]

theorem schedule_frame {n : ℕ} (schedule : Fin n→Image w) (old : Memory w) (z : ℕ)
    (off : ∀i,z<(schedule i).low ∨ (schedule i).stop≤z) : mountSchedule schedule old z=old z := by
  rw [mountSchedule,dite_eq_right];rintro ⟨i,a,b⟩;rcases off i with h|h <;> omega

theorem Image.Resident.afterEarlier (im : Image w) {old next : Memory w} (mounted : im.Resident old)
    (last : ℕ) (disjoint : last≤ im.low) (frame : ∀z,last≤z→next z=old z) : im.Resident next :=
  fun z lo hi=>(frame z (disjoint.trans lo)).trans (mounted z lo hi)

end Arena
end
end Hierarchy.DescentPackedColony.Phase

end OAI
