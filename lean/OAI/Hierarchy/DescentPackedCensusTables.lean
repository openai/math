import OAI.Hierarchy.DescentPackedCensusRAM
import OAI.Hierarchy.DescentPackedSchedulePins

namespace OAI
/-! # Uniform literal census programs and masks in the original phase header -/
namespace Hierarchy.DescentPackedColony.Phase.CensusTables
open DescentSIMDLookup DescentSixParty DescentColonies ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical Fin.CommRing
noncomputable section
variable {a b M H G w : ℕ}

abbrev Entries (a M H G : ℕ) := (Bool×Cell (a*M)) ⊕ Fin (H*chunks G M)

def base (origin a M : ℕ) (color : Bool) := if color then origin+2^(a*M) else origin
def maskBase (origin a M : ℕ) := origin+2*2^(a*M)
def maskBits (H G M : ℕ) := (H*chunks G M).log2+1

def banks (src : Bank) (origin a M H G : ℕ) (color : Bool) : Banks :=
  ⟨src,⟨base origin a M color,a*M⟩,⟨maskBase origin a M,maskBits H G M⟩⟩

def address (origin : ℕ) : Entries a M H G→ℕ
  | .inl (side,key)=>base origin a M side+key.val
  | .inr row=>maskBase origin a M+row.val

def value (f : Bool→Cell a→Cell b) : Entries a M H G→Word w
  | .inl (side,key)=>(table (f side) key).val
  | .inr j=>(maskWord b M G ((row H G M).symm j).2.val:ℕ)

theorem address_injective (origin : ℕ) : Function.Injective (address (a:=a) (M:=M) (H:=H) (G:=G) origin) := by
  rintro (⟨s,i⟩|i) (⟨t,j⟩|j) eqn
  · cases s <;> cases t <;> simp only [address,base,Bool.false_eq_true,↓reduceIte] at eqn
    all_goals first | (congr 2;apply Fin.ext;omega) | omega
  · cases s <;> simp only [address,base,maskBase,Bool.false_eq_true,↓reduceIte] at eqn <;> omega
  · cases t <;> simp only [address,base,maskBase,Bool.false_eq_true,↓reduceIte] at eqn <;> omega
  · exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel eqn))

def finish (origin a M H G : ℕ) := maskBase origin a M+2^(maskBits H G M)

def image (origin a b M H G : ℕ) (f : Bool→Cell a→Cell b) : Arena.Image w :=
  ⟨origin,finish origin a M H G,fun u=>
    if hit : ∃i : Entries a M H G,address origin i=u then value f hit.choose else 0⟩

theorem read (origin : ℕ) (f : Bool→Cell a→Cell b) (m : Memory w)
    (ok : (image origin a b M H G f).Resident m) (j : Entries a M H G) :
    m (address origin j)=value f j := by
  have bound : H*chunks G M≤2^maskBits H G M := Nat.lt_log2_self.le
  have window : origin≤address origin j ∧ address origin j<finish origin a M H G := by
    rcases j with ⟨s,i⟩|t
    · cases s <;> simp [address,base,finish,maskBase] <;> omega
    · dsimp [address,finish,maskBase];omega
  have result:=ok _ window.1 window.2
  have hit : ∃t : Entries a M H G,address origin t=address origin j := ⟨j,rfl⟩
  change m (address origin j)=(if found : ∃t : Entries a M H G,address origin t=address origin j then value f found.choose else 0) at result
  simpa [dite_eq_left hit,address_injective origin hit.choose_spec] using result

theorem frames (src : Bank) (origin : ℕ) (f : Bool→Cell a→Cell b) (x : Fin H→Fin G→Cell a) (m : Memory w)
    (mounted : (image origin a b M H G f).Resident m) (words : DescentPackedColony.Reads src x M m) :
    ∀side,PinFrame (M:=M) (banks src origin a M H G side) (f side) x m := by
  intro side
  refine ⟨?_,words⟩
  intro j i
  rcases j with key|key
  · exact congrArg (fun v=>wordBits w v i) (read origin f m mounted (.inl (side,key)))
  · exact congrArg (fun v=>wordBits w v i) (read origin f m mounted (.inr key))

theorem fits (src : Bank) (origin out : ℕ) (side : Bool)
    (source : src.Fits w out) (rows : H*chunks G M ≤ src.size)
    (before : finish origin a M H G≤out) (limit : out+H*chunks G M<2^w)
    (packed : M*max a b≤w/2) : Fits (banks src origin a M H G side) a b M H G w out := by
  have enough : H*chunks G M≤2^maskBits H G M := Nat.lt_log2_self.le
  have stop:=before
  dsimp [finish,maskBase] at stop
  refine ⟨source,?_,?_,rows,rfl,enough,limit,packed⟩
  · unfold Bank.Fits Bank.size
    simp only [banks,base]
    split <;> exact ⟨Nat.two_pow_pos _,by omega,by omega⟩
  · exact ⟨Nat.two_pow_pos _,by change 2^(maskBits H G M)<_;omega,before⟩

/-- One finite positive table invoice for both complete census LUTs and the
shared tail mask, at the actual packed vector width. -/
theorem price (origin a M H G h W K : ℕ) (short : a*M≤h/2) (wide : W≤K*h) :
    (finish origin a M H G-origin)*W≤K*(2*(2^(h/2)*h)+2*(H*chunks G M+1)*h) := by
  have dict:=Nat.pow_le_pow_right (by decide : 0<2) short
  have bound : 2^(maskBits H G M)≤2*(H*chunks G M+1) := by
    by_cases zero:H*chunks G M=0
    · simp [maskBits,zero]
    · have floor:=Nat.log2_self_le zero
      simp only [maskBits,pow_succ]
      omega
  have grow : finish origin a M H G-origin≤2*2^(h/2)+2*(H*chunks G M+1) := by
    unfold finish maskBase
    omega
  calc
    _ ≤ (2*2^(h/2)+2*(H*chunks G M+1))*(K*h) := Nat.mul_le_mul grow wide
    _ = _ := by ring
end
end Hierarchy.DescentPackedColony.Phase.CensusTables

end OAI
