import OAI.Hierarchy.DescentNamedGeometry
import OAI.Hierarchy.DescentAtomSchedule

namespace OAI
/-! # Public arithmetic fields of coalesced ordinary host records -/
namespace Hierarchy.DescentHostDirectory.SiteDecode
open DescentStageEdgeReceipt DescentColonies DescentCompiler
open scoped Classical
noncomputable section

structure Header where
  group : ℕ
  host : ℕ
  block : ℕ
  site : ℕ
  merged : ℕ
  marked : Bool
  deriving DecidableEq

/-- The mixed integer slots are laid out with block digit last, then the
local tree address and old vertex ID. The switch handles saturated hubs. -/
def read (k step g slots oldPitch newPitch : ℕ) (flag : Bool) (q : ℕ) : Header :=
  let entry:=q/slots
  let rack:=entry/2^(k+1)
  let node:=entry%2^(k+1)
  let d:=Nat.log 2 (node+1)
  let ident:=node+1-2^d
  let (next,localSlot):=if flag then
    (nodeNumber (k-g) (ident/2^(d-(k-g))),0)
    else (node,q%slots)
  let host:=(rack%oldPitch*2^(k+1)+next)*slots+localSlot
  let group:=(rack/oldPitch)/2^step
  let block:=(rack/oldPitch)%2^step
  ⟨group,host,block,(group*newPitch+host)*2^step+block,(rack*2^(k+1)+next)*slots+localSlot,flag⟩

def component {V : Type} (j d : ℕ) (v : V) (p t : ℕ) : Key (ℕ×V) := ((j,v),(d,p),t)

private theorem divField (a radix b : ℕ) (h : b<radix) : (a*radix+b)/radix=a := by
  rw [Nat.mul_comm a radix, Nat.mul_add_div (by omega : 0<radix), Nat.div_eq_of_lt h, Nat.add_zero]
private theorem modField (a radix b : ℕ) (h : b<radix) : (a*radix+b)%radix=b := by
  exact Nat.mul_add_mod_of_lt h

theorem node_decode (d i : ℕ) (hi : i<2^d) :
    Nat.log 2 (nodeNumber d i+1)=d ∧ nodeNumber d i+1-2^d=i := by
  have h:=node_range hi
  have pos:=Nat.two_pow_pos d
  refine ⟨Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega),?_⟩
  unfold nodeNumber;omega

variable {step : ℕ} {J G V : Type} [Fintype J] [Fintype G] [Fintype V] [DecidableEq V] [DecidableEq J]
variable (oldGroup : J↪ℕ) (newGroup : G↪ℕ) (vRank : V↪ℕ)
variable (digits : J≃G×Block step) (hub : V→Bool) (k g slots : ℕ) (key : Key (J×V))

def hubKey := mergeHub (fun a : J×V=>hub a.2) k g key

omit [Fintype G] [DecidableEq V] [DecidableEq J] in
/-- The smaller group's actual ID and the retained block digit are supplied
by the purchased chronological grouping. The raw numeric code reads its
true new site key, host coordinate, and flags. -/
theorem fields (legal : key∈keys k slots)
    (divide : newGroup (digits key.1.1).1=oldGroup key.1.1/2^step)
    (remain : ((digits key.1.1).2).val=oldGroup key.1.1%2^step) :
    read k step g slots (pitch vRank) (pitch (hostRank vRank k slots))
      (hub key.1.2) (packedNumber (groupRank oldGroup vRank) k slots key)=
    let u:=hubKey hub k g key
    let host:=packedNumber vRank k slots (splitKey u).2
    let j:=newGroup (digits u.1.1).1
    let z:=((digits u.1.1).2).val
    ⟨j,host,z,(j*pitch (hostRank vRank k slots)+host)*2^step+z,
        packedNumber (groupRank oldGroup vRank) k slots u,hub u.1.2⟩ := by
  obtain ⟨_,atKey⟩:=Finset.mem_product.mp legal
  obtain ⟨inCodes,inSlots⟩:=Finset.mem_product.mp atKey
  have sl:=Finset.mem_range.mp inSlots
  obtain ⟨dk,small⟩:=codes_valid inCodes
  have nrange : nodeNumber key.2.1.1 key.2.1.2<2^(k+1) :=
    (node_range small).2.trans_le ((Nat.sub_le ..).trans (Nat.pow_le_pow_right (by decide) (by omega)))
  have oldBound : vRank key.1.2<pitch vRank :=
    Nat.lt_succ_of_le (Finset.le_sup (f:=vRank) (Finset.mem_univ _))
  have dec:=node_decode _ _ small
  have group_at (u : J×V) :
      groupRank oldGroup vRank u = oldGroup u.1*pitch vRank+vRank u.2 := rfl
  have split_at (u : Key (J×V)) : (splitKey u).2=(u.1.2,u.2) := rfl
  cases flag : hub key.1.2 <;> simp [read,hubKey,mergeHub,packedNumber,group_at,split_at,
    flag,divField _ _ _ sl,modField _ _ _ sl,divField _ _ _ nrange,modField _ _ _ nrange,
    divField _ _ _ oldBound,modField _ _ _ oldBound,dec,divide,remain]

theorem real_digits (S : AtomSchedule) {age step : ℕ} (live : age<S.length) (radix : S.radix=2^step)
    (j : Fin (S.groupCount age)) :
    ((S.groupDigits live radix j).1).val=j.val/2^step ∧
    ((S.groupDigits live radix j).2).val=j.val%2^step := ⟨rfl,rfl⟩

end
end Hierarchy.DescentHostDirectory.SiteDecode

end OAI
