import OAI.Hierarchy.DescentPackedMatchPrepareIssued
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Exact literal ROM initialization for the packed matching predecessor -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepare.ROM
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentStaticWordColumn DescentSharedCableNames
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {k D cap a d M H G w : ℕ}
local notation "r" => 2^k
local notation "p" => 2*cap
local notation "rows" => H*chunks G M
local notation "WordIndex" => StaticCells k D cap a M H G
local notation "size" => staticWords k D cap a M H G

def ordinal (k D cap a M H G : ℕ) : StaticCells k D cap a M H G ≃ Fin (staticWords k D cap a M H G) :=
  let finPair : Fin 2×Fin (H*D) ≃ Fin (2*(H*D)) := finProdFinEquiv
  let last : Fin (H*chunks G M) ⊕ (Fin 2×Fin (H*D)) ≃ Fin (H*chunks G M+2*(H*D)) := ((Equiv.refl _).sumCongr finPair).trans finSumFinEquiv
  let mid := ((Equiv.refl (Cell (DescentSignedCableCodec.width D cap*M))).sumCongr last).trans finSumFinEquiv
  let middle := ((finProdFinEquiv (m:=2^k) (n:=2^((1*2^k+a)*M))).sumCongr mid).trans finSumFinEquiv
  (((Equiv.refl _).sumCongr middle).trans finSumFinEquiv).trans (finCongr (by unfold staticWords;ring))

def words (d : ℕ) : WordIndex→ℕ
  | .inl u=>2^(a*M)*u.val
  | .inr (.inl (x,t))=>(DescentPackedZip.table (M:=M) (fun b y=>Stage.gated (s:=d) b x y) t).val
  | .inr (.inr (.inl t))=>(DescentSIMDLookup.table (M:=M) (DescentPackedMatchSenderPins.table D cap d) t).val
  | .inr (.inr (.inr (.inl j)))=>maskWord d M G ((row H G M).symm j).2.val
  | .inr (.inr (.inr (.inr (q,j))))=>if q.val=0 then DescentSortedRoster.originValue D j.val else DescentSortedRoster.slotValue D j.val

def data (k D cap a d M H G : ℕ) (j : ℕ) := if b : j<staticWords k D cap a M H G then words d ((ordinal k D cap a M H G).symm ⟨j,b⟩) else 0

def gateBase (base k M : ℕ) := base+2^((1*2^k)*M)
def chipBase (base k a M : ℕ) := gateBase base k M+2^k*2^((1*2^k+a)*M)
def maskBase (base k D cap a M : ℕ) := chipBase base k a M+2^(DescentSignedCableCodec.width D cap*M)
def rankBase (base k D cap a M H G : ℕ) := maskBase base k D cap a M+H*chunks G M

def chart (base D a M bits : ℕ) (actor : Bank) (win : Fin r→Bank) (wire : Fin r→Fin p→Bank) : Chart k cap where
  actor:=actor
  winner:=win
  signed:=wire
  shift:=⟨base,(1*r)*M⟩
  gate x:=⟨gateBase base k M+x.val*2^((1*r+a)*M),(1*r+a)*M⟩
  dictionary:=⟨chipBase base k a M,DescentSignedCableCodec.width D cap*M⟩
  mask:=⟨maskBase base k D cap a M,bits⟩

def roster (base k D cap a M H G bits : ℕ) (raw : Bank) : DescentSortedRoster.Chart :=
  ⟨raw,⟨rankBase base k D cap a M H G,bits⟩,⟨rankBase base k D cap a M H G+H*D,bits⟩⟩

def address (base : ℕ) : WordIndex→ℕ
  | .inl u=>base+u.val
  | .inr (.inl (x,t))=>gateBase base k M+x.val*2^((1*r+a)*M)+t.val
  | .inr (.inr (.inl t))=>chipBase base k a M+t.val
  | .inr (.inr (.inr (.inl j)))=>maskBase base k D cap a M+j.val
  | .inr (.inr (.inr (.inr (q,j))))=>rankBase base k D cap a M H G+q.val*(H*D)+j.val

theorem address_eq (base : ℕ) (j : WordIndex) : address base j=base+(ordinal k D cap a M H G j).val := by
  rcases j with u|⟨x,t⟩|t|x|⟨q,b⟩ <;> simp [address,ordinal,gateBase,chipBase,maskBase,rankBase,finProdFinEquiv_apply_val] <;> ring

def after (base k D cap a d M H G : ℕ) (m : Memory w) :=
  DescentStaticWordColumn.image base (data k D cap a d M H G) m (staticWords k D cap a M H G)

def program (w base k D cap a d M H G : ℕ) := DescentStaticWordColumn.program w base (data k D cap a d M H G) (staticWords k D cap a M H G)

theorem run (base k D cap a d M H G : ℕ) (m : Memory w) (room : base+staticWords k D cap a M H G<2^w) :
    (program w base k D cap a d M H G).Exec m (after base k D cap a d M H G m) (4+10*staticWords k D cap a M H G) :=
  DescentStaticWordColumn.mount base _ _ m room

theorem code_names (w base k D cap a d M H G : ℕ) : DescentStaticWordColumn.names (program w base k D cap a d M H G)=
    15*(staticWords k D cap a M H G+1) := DescentStaticWordColumn.names_mount ..

theorem cheap (w base k D cap a d M H G : ℕ) : CheapCode (program w base k D cap a d M H G) := by
  have h (n : ℕ) : CheapCode (DescentStaticWordColumn.program w base (data k D cap a d M H G) n) := by
    induction n with
    | zero=>exact @scan_cheap _ _ _ _
    | succ n ih=>exact cheap_seq ih (@scan_cheap _ _ _ _)
  exact @h (staticWords k D cap a M H G)

theorem read (base d : ℕ) (m : Memory w) (j : WordIndex) : after base k D cap a d M H G m (address base j)=((words d j):Word w) := by
  rw [address_eq,after,DescentStaticWordColumn.read _ _ _ _ (ordinal k D cap a M H G j).isLt]
  rw [data, dite_eq_left (ordinal k D cap a M H G j).isLt]
  exact congrArg (fun t : WordIndex => (words d t : Word w))
    ((ordinal k D cap a M H G).symm_apply_apply j)

theorem frame (base k D cap a d M H G : ℕ) (m : Memory w) (x : ℕ) (hx : x<base ∨ base+staticWords k D cap a M H G≤x) : after base k D cap a d M H G m x=m x :=
  DescentStaticWordColumn.frame _ _ _ _ _ hx

/-- All varying memory reads are from the old actor, actual selected winners,
signed cable words and old host roster. All fixed truth-table and address
words come from the one literal program above. -/
theorem mounted (base bits shapeBits : ℕ) (m : Memory w) (act : Bank) (win : Fin r→Bank) (wire : Fin r→Fin p→Bank) (raw : Bank)
    (active : Fin H→Fin G→Cell (1*r)) (values : Fin r→Fin H→Fin G→Cell a)
    (signed : Fin r→Fin p→Fin H→Fin G→Option (DescentSharedCableNames.Stage.Live D cap)) (rs : Fin H→Fin D→Option (Fin H))
    (actTop : act.base+rows≤base) (winTop : ∀x,(win x).base+rows≤base) (wireTop : ∀x j,(wire x j).base+rows≤base) (rawTop : raw.base+H*D≤base)
    (aRead : Reads act active M m) (wRead : ∀x,Reads (win x) (values x) M m)
    (sRead : ∀x j,Reads (wire x j) (fun h g=>DescentSignedCableCodec.encode (signed x j h g)) M m)
    (roRead : ∀v : Fin H,∀j : Fin D,m (raw.base+(v.val*D+j.val))=(DescentPackedColony.target (rs v j):Word w)) :
    let C:=chart base D a M bits act win wire;let R:=roster base k D cap a M H G shapeBits raw
    let mem:=after base k D cap a d M H G m
    Prepare.Frame C active values signed d M mem ∧ DescentSortedRoster.Raw R rs mem := by
  intro C R mem
  have old (x : ℕ) (hx : x<base) : mem x=m x:=frame _ _ _ _ _ _ _ _ _ _ _ (.inl hx)
  constructor
  · refine ⟨?_,?_,?_,?_⟩
    · intro t
      exact (old _ ((Nat.add_lt_add_left (row H G M t).isLt act.base).trans_le actTop)).trans (aRead t)
    · intro x t
      exact (old _ ((Nat.add_lt_add_left (row H G M t).isLt (win x).base).trans_le (winTop x))).trans (wRead x t)
    · intro x;constructor
      · intro u;exact read base d m (.inl u : WordIndex)
      · intro u;exact read base d m (.inr (.inl (x,u)) : WordIndex)
    · intro x j;constructor
      · intro t z;cases t with
        | inl t=>exact congrFun (congrArg (wordBits w) (read base d m (.inr (.inr (.inl t)) : WordIndex))) z
        | inr t=>exact congrFun (congrArg (wordBits w) (read base d m (.inr (.inr (.inr (.inl t))) : WordIndex))) z
      · intro t
        exact (old _ ((Nat.add_lt_add_left (row H G M t).isLt (wire x j).base).trans_le (wireTop x j))).trans (sRead x j t)
  · let ix (v : Fin H) (j : Fin D) : Fin (H*D) := finProdFinEquiv (v,j)
    have code (v : Fin H) (j : Fin D) : (ix v j).val=v.val*D+j.val := by simp [ix,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    refine ⟨?_,?_,?_⟩
    · intro v j
      have put:=read base d m (.inr (.inr (.inr (.inr (0,ix v j)))) : WordIndex)
      simpa only [mem,R,roster,address,words,Fin.val_zero,zero_mul,Nat.add_zero,code,ite_true,(DescentSortedRoster.canonical_addresses v j).1] using put
    · intro v j
      have put:=read base d m (.inr (.inr (.inr (.inr (1,ix v j)))) : WordIndex)
      simpa only [mem,R,roster,address,words,Fin.val_one,one_mul,code,ite_eq_right (by decide : (1:ℕ)≠0),(DescentSortedRoster.canonical_addresses v j).2] using put
    · intro v j;have small : v.val*D+j.val<H*D:=by rw [←code v j];exact (ix v j).isLt
      exact (old _ ((Nat.add_lt_add_left small raw.base).trans_le rawTop)).trans (roRead v j)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepare.ROM

end OAI
