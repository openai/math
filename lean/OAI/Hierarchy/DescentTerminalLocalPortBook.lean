import OAI.Hierarchy.DescentTerminalRouteWords
import OAI.Hierarchy.DescentTerminalBinPack
import OAI.Hierarchy.ProtocolRAMPortRanks
import Mathlib.Data.Fintype.Pi

namespace OAI
/-! # Port and operand rows from common-edge, block and wire ordinals retained at a site -/
namespace Hierarchy.DescentTerminalLocalPortBook
open Computability.VPVNP.BurstRAM DescentTerminalRouteRows DescentTerminalBinPack
open ThreeFlat.Routing CallPool
open scoped Classical BigOperators
noncomputable section

/-- Only the current oriented host port, block, wire ordinal and piece appear
in this token. Every reference belonging to the same site uses the same chart. -/
abbrev Token (degree blocks wires pieces : ℕ) := Fin degree × Fin blocks × Fin wires × Fin pieces
def tokenCode {degree blocks wires pieces : ℕ} (t : Token degree blocks wires pieces) :
    Fin (degree*(blocks*(wires*pieces))) :=
  finProdFinEquiv (t.1,finProdFinEquiv (t.2.1,finProdFinEquiv t.2.2))
theorem token_injective {d b e p : ℕ} : Function.Injective (@tokenCode d b e p) := by
  rintro ⟨i,j,k,l⟩ ⟨i',j',k',l'⟩ h
  simpa [tokenCode] using h

/-- This entry has the two true static lists in chronological local order.
Empty slots, spare groups and spare nodes are represented by the count fields. -/
structure Book (G V M A a : ℕ) where
  groupCount : Fin (G+1)
  nodeCount : Fin (V+1)
  groupSize : Fin G → Fin (M+1)
  nodeArity : Fin V → Fin (A+1)
  portName : Fin G → Fin M → Word a
  operand : Fin V → Fin A → Word a

variable {G V M A a W q : ℕ}
namespace Book

private abbrev Fields (G V M A a : ℕ) :=
  Fin (G+1) × Fin (V+1) × (Fin G → Fin (M+1)) × (Fin V → Fin (A+1)) ×
    (Fin G → Fin M → Word a) × (Fin V → Fin A → Word a)

private def fieldsEquiv : Book G V M A a ≃ Fields G V M A a :=
  ⟨fun u => ⟨u.groupCount,u.nodeCount,u.groupSize,u.nodeArity,u.portName,u.operand⟩,
   fun z => ⟨z.1,z.2.1,z.2.2.1,z.2.2.2.1,z.2.2.2.2.1,z.2.2.2.2.2⟩,
   fun _ => rfl,fun _ => rfl⟩

instance : Fintype (Book G V M A a) := Fintype.ofEquiv _ fieldsEquiv.symm

abbrev groups (u : Book G V M A a) := Fin u.groupCount.val
abbrev nodes (u : Book G V M A a) := Fin u.nodeCount.val
def size (u : Book G V M A a) (g : u.groups) := (u.groupSize (g.castLE (by omega))).val
def arity (u : Book G V M A a) (v : u.nodes) := (u.nodeArity (v.castLE (by omega))).val
abbrev Port (u : Book G V M A a) := (g : u.groups) × Fin (u.size g)
abbrev Operand (u : Book G V M A a) := (i : u.nodes) × Fin (u.arity i)
def tag (u : Book G V M A a) (j : u.Port) : Word a :=
  u.portName (j.1.castLE (by omega)) (j.2.castLE (by have:= (u.groupSize (j.1.castLE (by omega))).isLt;unfold size;omega))
def ref (u : Book G V M A a) (j : u.Operand) : Word a :=
  u.operand (j.1.castLE (by omega)) (j.2.castLE (by have:=(u.nodeArity (j.1.castLE (by omega))).isLt;unfold arity;omega))

def portCoord (u : Book G V M A a) (q : ℕ) (j : u.Port) : ℕ×ℕ :=
  (ProtocolRAMPortRanks.prefix (fun g=>poolBatchCount (u.size g) q) Fin.val j.1+j.2.val/q,j.2.val%q)
def argCoord (u : Book G V M A a) (q : ℕ) (j : u.Operand) : ℕ×ℕ :=
  let before := ∑g,poolBatchCount (u.size g) q
  let ordinal := first q u.arity j.1+j.2.val
  (before+ordinal/q,ordinal%q)
def atCoord {I : Type} (geom : I→ℕ×ℕ) (token : I→Word a) (r s : ℕ) : Option (Word a) :=
  if hit:∃i,geom i=(r,s) then some (token hit.choose) else none
theorem at_iff {I : Type} (geom : I→ℕ×ℕ) (token : I→Word a) (inj : Function.Injective geom)
    (r s : ℕ) (name : Word a) : atCoord geom token r s=some name ↔ ∃j,geom j=(r,s) ∧ token j=name := by
  by_cases hit:∃i,geom i=(r,s)
  · simp only [atCoord,dite_eq_left hit,Option.some.injEq]
    exact ⟨fun h=>⟨_,hit.choose_spec,h⟩,fun ⟨j,hj,hn⟩=>by rw [inj (hit.choose_spec.trans hj.symm),hn]⟩
  · rw [atCoord,dite_eq_right hit]
    constructor
    · intro h
      cases h
    · rintro ⟨j,hj,_⟩
      exact (hit ⟨j,hj⟩).elim
def row (u : Book G V M A a) (q r : ℕ) : Row q a :=
  fun side slot=>if side.val=0 then atCoord (u.portCoord q) u.tag r slot.val
    else atCoord (u.argCoord q) u.ref r slot.val

/-- One finite shared table for all sites and all histories, parameterized by
the genuine compact record, the position's local row and the offsets of its
owner in its bin. The word placed in the running bin file includes the owner
to distinguish identical local names at different sites. -/
def own (owner : Fin W) (val : Word a) : Word (Nat.clog 2 (W*2^a)) :=
  (finProdFinEquiv (owner,val)).castLE (Nat.le_pow_clog (by decide) _)
def emit (u : Book G V M A a) (q r : ℕ) (owner : Fin W) :
    Word (rowBits q (Nat.clog 2 (W*2^a))) := pack (fun side slot=>(u.row q r side slot).map (own owner))

def count (G V M A a : ℕ) := (G+1)*(V+1)*(M+1)^G*(A+1)^V*(2^a)^(M*G)*(2^a)^(A*V)
theorem book_count : Fintype.card (Book G V M A a)=count G V M A a := by
  classical
  rw [Fintype.card_congr fieldsEquiv]
  simp [Fields,count,Fintype.card_prod,Nat.pow_mul,Nat.mul_assoc]

end Book
end
end Hierarchy.DescentTerminalLocalPortBook

end OAI
