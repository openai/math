import OAI.Hierarchy.DescentPackedWalshColumnROM
import OAI.Hierarchy.DescentDyadicReductionGhosts

namespace OAI
/-! # Real-host dyadic reductions followed by common-ordinal publication in the same memory -/
namespace Hierarchy.DescentPackedWalsh.Column
open DescentSIMDLookup DescentPackedWalshReduction ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (P : Plan) {w : ℕ}
local notation "k" => P.axis
local notation "l" => P.laneBits P.depth
local notation "s" => P.bits+P.depth
local notation "L" => P.lanes P.depth
local notation "K" => P.chunks P.depth

def chunkAt (d : Fin (2^k)) : Fin K :=
  ⟨d.val/L,(Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by
    have below : l≤k := Nat.min_le_left ..
    have h : K*2^l=2^k := by
      change 2^(k-l)*2^l=2^k
      rw [←pow_add,Nat.sub_add_cancel below]
    rw [h];exact d.isLt)⟩

def laneAt (d : Fin (2^k)) : Fin (2^l) := ⟨d.val%L,Nat.mod_lt _ (Nat.two_pow_pos _)⟩

def input (first : ℕ) : Bank := ⟨P.dataAt first P.depth,k-l⟩

def publishCode (w root first extract out : ℕ) : Procedure w :=
  let src:=input P first
  let B:=banks extract k K s l src
  ((P.padProgram w first).seq (P.code w root first P.depth)).seq (scan w out (2^k) (scanRow B l))

def publishTime (_root first extract : ℕ) :=
  P.padTicks+P.duration P.depth+(4+2^k*(2*(scanRow (banks extract k K s l (input P first)) l).work+4))

def publishMem (root first extract out : ℕ) (m : Memory w) :=
  let final:=P.state root first (P.pad first m) P.depth
  image out (2^k) (scanRow (banks extract k K s l (input P first)) l) final

theorem collected (root first extract out : ℕ) (mem rom : Memory w)
    (x : Fin P.sites→Fin (2^k)→ℕ) (xSize : ∀v d,x v d<2^P.bits)
    (ord : Fin (2^k)→Fin (2^k))
    (reduceROM : P.headerAt root P.depth≤first) (early : extract+size k s l≤first)
    (later : P.dataAt first (P.depth+1)≤out) (limit : out+2^k<2^w)
    (width : P.height≤w) (word : s≤w)
    (reductionHeader : ∀a,root≤a→a<P.headerAt root P.depth→mem a=P.mount root rom P.depth a)
    (selector : ∀a<size k s l,mem (extract+a)=fixedRow (chunkAt P ∘ord) (laneAt P ∘ord) s a)
    (data : P.Seed x first mem) :
    let dst:=publishMem P root first extract out mem
    (publishCode P w root first extract out).Exec mem dst (publishTime P root first extract) ∧
      (∀i : Fin (2^k),dst (out+i.val)=((∑v,x v (ord i)):Word w)) ∧
      (∀z<first,dst z=mem z) ∧ ∀z,out+2^k≤z→dst z=mem z := by
  have outRoom : out<2^w := (Nat.le_add_right out (2^k)).trans_lt limit
  have last : P.dataAt first (P.depth+1)<2^w := later.trans_lt outRoom
  let target:=P.state root first (P.pad first mem) P.depth
  obtain ⟨run,amount,low,high⟩:=P.from_resident x xSize root first mem rom reduceROM last width word reductionHeader data
  have short (i : Fin K) :=(P.resident_words x xSize root first mem rom reduceROM last width word
      reductionHeader data i).2
  have rows : P.dataAt first P.depth+K≤out := by
    have hc : P.hosts P.depth=1:=by simp [Plan.hosts]
    have t:=later
    change P.dataAt first P.depth+P.hosts P.depth*K≤out at t
    simpa only [hc,one_mul] using t
  have inputFits : (input P first).Fits w out := ⟨Nat.two_pow_pos _,by
    exact ((Nat.le_add_left K (P.dataAt first P.depth)).trans rows).trans_lt outRoom,rows⟩
  have firstRoom : first≤out:=(P.data_mono first (Nat.zero_le (P.depth+1))).trans later
  have declared := publish (input P first) extract out (chunkAt P ∘ord) (laneAt P ∘ord)
    (fun i=>∑v,x v (ord i)) target (early.trans firstRoom) ⟨inputFits,le_rfl⟩ limit
    (fun j hj=>(low _ (by omega)).trans (selector j hj)) short (fun i=>amount (ord i))
  obtain ⟨emit,read,before,after⟩:=declared
  refine ⟨?_,?_,fun z hz=>(before _ (hz.trans_le firstRoom)).trans (low _ hz),
    fun z hz=>(after _ hz).trans (high _ (later.trans ((Nat.le_add_right out (2^k)).trans hz)))⟩
  · intro pcs regs keys machine
    exact Procedure.Exec.then run emit machine
  · intro i
    have castTotal := Nat.cast_sum (R:=Word w) Finset.univ (fun v : Fin P.sites => x v (ord i))
    simpa only [publishMem,target] using (read i).trans castTotal

end
end Hierarchy.DescentPackedWalsh.Column

end OAI
