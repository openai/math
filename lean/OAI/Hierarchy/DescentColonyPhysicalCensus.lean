import OAI.Hierarchy.DescentColonyLayerRAM
import OAI.Hierarchy.DescentColonyCensusRAM

namespace OAI
/-! # A native score word for a complete candidate colony arrangement -/

namespace Hierarchy.DescentColonies.PhysicalCensus

open ProtocolRAM Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing

variable {H k w : ℕ}

def output (H k base : ℕ) := base+k*H*2^k

theorem bank_before (base d : ℕ) (hd : d<k) (v : Fin H) :
    LayerRAM.address k base d v+2^k ≤ output H k base := by
  have slot : (k-1-d)*H+v.val+1 ≤ k*H := calc
    _ ≤ (k-1-d)*H+H := by have := v.isLt;omega
    _ = (k-1-d+1)*H := (Nat.succ_mul _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have scaled := Nat.mul_le_mul_right (2^k) slot
  rw [Nat.succ_mul] at scaled
  dsimp [LayerRAM.address,output]
  omega

def program (w k base : ℕ) (incoming : Fin H→List (Fin H)) (loadBase : Fin H→ℕ) (D cap : ℕ) :=
  (ProtocolRAM.program w (LayerRAM.passes k base incoming loadBase D cap)).seq
    (CensusRAM.program w k (output H k base) (LayerRAM.address (H:=H) k base))

def after (k base : ℕ) (incoming : Fin H→List (Fin H)) (loadBase : Fin H→ℕ) (D cap : ℕ)
    (m : Memory w) :=
  CensusRAM.after k (output H k base) (LayerRAM.address (H:=H) k base)
    (result (LayerRAM.passes k base incoming loadBase D cap) m)

def ticks (k base : ℕ) (incoming : Fin H→List (Fin H)) (loadBase : Fin H→ℕ) (D cap : ℕ) :=
  ProtocolRAM.clock (LayerRAM.passes k base incoming loadBase D cap)+
    (4+1*(2*(CensusRAM.expression k (LayerRAM.address (H:=H) k base)).work+4))

theorem run (base : ℕ) (incoming : Fin H→List (Fin H)) (loadBase : Fin H→ℕ) (D cap : ℕ)
    (m : Memory w) (old : ∀v,loadBase v+2^k≤base) (room : output H k base+1<2^w) :
    (program w k base incoming loadBase D cap).Exec m (after k base incoming loadBase D cap m)
      (ticks k base incoming loadBase D cap) := by
  intro labels registers slots machine
  exact Procedure.Exec.then
    (LayerRAM.run (incoming:=incoming) (D:=D) (cap:=cap) m old (by dsimp [output] at room;omega))
    (CensusRAM.run _ _ _ room (bank_before base)) machine

theorem published (base : ℕ) (incoming : Fin H→List (Fin H)) (loadBase : Fin H→ℕ) (D cap : ℕ)
    (m : Memory w) (load : Fin H→Block k→ℕ) (old : ∀v,loadBase v+2^k≤base)
    (room : output H k base+1<2^w) (capRoom : cap<2^w) (bits : 2^k≤2^w)
    (weights : ∀v x,m (loadBase v+x.val)=(load v x:Word w))
    (sumRoom : ∀d<k,∀v x,(Scan.readWeights load d v x).sum<2^w) :
    after k base incoming loadBase D cap m (output H k base)=(Scan.FinRows.score incoming load D cap:Word w) := by
  apply CensusRAM.published _ _ incoming load D cap _
    (by omega) ((Nat.lt_two_pow_self (n:=k)).trans_le bits) bits
  intro d hd v x
  exact LayerRAM.published (incoming:=incoming) (D:=D) m load old
    (by dsimp [output] at room;omega) capRoom weights sumRoom d hd v x

private theorem distinct_le (keys : List (ℕ×ℕ)) : (Scan.uniqueIDs keys).1≤keys.length := by
  induction keys with
  | nil => rfl
  | cons a xs ih =>
    simp only [Scan.uniqueIDs,List.length_cons]
    split <;> omega

theorem score_le (incoming : Fin H→List (Fin H)) (load : Fin H→Block k→ℕ) (D cap : ℕ) :
    Scan.FinRows.score incoming load D cap≤H*2^k := by
  rw [Scan.FinRows.score_eq_leafScore,Scan.leafScore]
  apply le_trans (Finset.sum_le_sum (g:=fun _ : Fin H=>2^k) (fun v _ => ?_)) (by simp)
  simpa only [Scan.keyList,List.length_ofFn] using
    distinct_le (Scan.keyList (Scan.build incoming load D cap k) v)

theorem published_nat (base : ℕ) (incoming : Fin H→List (Fin H)) (loadBase : Fin H→ℕ) (D cap : ℕ)
    (m : Memory w) (load : Fin H→Block k→ℕ) (old : ∀v,loadBase v+2^k≤base)
    (room : output H k base+1<2^w) (capRoom : cap<2^w) (bits : 2^k≤2^w) (bill : H*2^k<2^w)
    (weights : ∀v x,m (loadBase v+x.val)=(load v x:Word w))
    (sumRoom : ∀d<k,∀v x,(Scan.readWeights load d v x).sum<2^w) :
    (after k base incoming loadBase D cap m (output H k base)).val=Scan.FinRows.score incoming load D cap := by
  rw [published base incoming loadBase D cap m load old room capRoom bits weights sumRoom,
    Fin.val_cast_of_lt ((score_le incoming load D cap).trans_lt bill)]

theorem ticks_le (base : ℕ) (incoming : Fin H→List (Fin H)) (loadBase : Fin H→ℕ) (D cap deg : ℕ)
    (degree : ∀v,(incoming v).length≤deg) :
    ticks k base incoming loadBase D cap ≤
      (4+k*H*(4+2^k*(2*SplitRAM.workBound k deg+4)))+(4+1*(2*CensusRAM.workBound H k+4)) := by
  apply Nat.add_le_add (LayerRAM.clock_bound deg degree)
  have h := CensusRAM.work (k:=k) (LayerRAM.address (H:=H) k base)
  omega

end Hierarchy.DescentColonies.PhysicalCensus

end OAI
