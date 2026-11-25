import OAI.Hierarchy.DescentPackedProfileNumber
import OAI.Hierarchy.DescentPackedLayoutSum
import OAI.Hierarchy.DescentPackedLayoutCPU
import OAI.Hierarchy.DescentTerminalProfileCodes
import OAI.Hierarchy.ProtocolRAMEndpointPrefixCheap

namespace OAI
/-! # One native geometry bit from all the authentic packed matching pages -/
namespace Hierarchy.DescentPacking.PackedMatch.LayoutSum
open DescentSixParty DescentSIMDLookup DescentPackedLayoutCPU DescentTerminalEpochFlags
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {F C : Type} [Field F] [Fintype C] {G : PoweredGadget F} {n M w : ℕ}
variable (s : Shape) (B : DescentBestLayoutRAM.Banks)
local notation "amount" => 2^(SixBirths.width s M)
local notation "tariff" => score (G:=G) s (profileCode G.C) M
def install (M w : ℕ) (G : PoweredGadget F) : Procedure w :=
  (DescentStaticWordColumn.program w (B.tariff false).base (score (G:=G) s (profileCode G.C) M false) (2^(SixBirths.width s M))).seq
    (DescentStaticWordColumn.program w (B.tariff true).base (score (G:=G) s (profileCode G.C) M true) (2^(SixBirths.width s M)))
def mounted (M : ℕ) (G : PoweredGadget F) (m : Memory w) :=
  DescentStaticWordColumn.image (B.tariff true).base (score (G:=G) s (profileCode G.C) M true)
    (DescentStaticWordColumn.image (B.tariff false).base (score (G:=G) s (profileCode G.C) M false) m (2^(SixBirths.width s M)))
    (2^(SixBirths.width s M))

structure ROMSpace (s : Shape) (M n w : ℕ) (B : DescentBestLayoutRAM.Banks) : Prop where
  low : B.pairs.base+n≤(B.tariff false).base
  sep : (B.tariff false).base+2^(SixBirths.width s M)≤(B.tariff true).base
  finish : (B.tariff true).base+2^(SixBirths.width s M) < 2^w
  room : ∀b,2^(SixBirths.width s M)≤(B.tariff b).size

theorem mount (m : Memory w) (fit : ROMSpace s M n w B) :
    (install s B M w G).Exec m (mounted s B M G m) ((4+10*amount)+(4+10*amount)) ∧
    (∀b j,j < amount→ mounted s B M G m ((B.tariff b).base+j)=(tariff b j:Word w)) ∧
    ∀x,x < (B.tariff false).base ∨ (B.tariff true).base+amount≤x→mounted s B M G m x=m x := by
  let T:=DescentStaticWordColumn.image (B.tariff false).base (tariff false) m amount
  have sep:=fit.sep
  have last:=fit.finish
  have loBase : (B.tariff false).base ≤ (B.tariff true).base :=
    (Nat.le_add_right _ amount).trans sep
  have hiBase : (B.tariff true).base ≤ (B.tariff true).base + amount := Nat.le_add_right ..
  refine ⟨?_, ?_, ?_⟩
  · exact Procedure.Exec.then
      (DescentStaticWordColumn.mount (B.tariff false).base amount (tariff false) m (sep.trans_lt (hiBase.trans_lt last)))
      (DescentStaticWordColumn.mount (B.tariff true).base amount (tariff true) T last)
  · intro b j h
    cases b with
    | false=>
      rw [mounted,DescentStaticWordColumn.frame _ _ _ _ _ (.inl (by omega)),DescentStaticWordColumn.read _ _ _ _ h]
    | true=>exact DescentStaticWordColumn.read _ _ _ _ h
  · intro x away
    have afterTrue : x < (B.tariff true).base ∨ (B.tariff true).base + amount ≤ x := by
      rcases away with lo | hi
      · exact .inl (lo.trans_le loBase)
      · exact .inr hi
    have afterFalse : x < (B.tariff false).base ∨ (B.tariff false).base + amount ≤ x := by
      rcases away with lo | hi
      · exact .inl lo
      · exact .inr (sep.trans (hiBase.trans hi))
    exact (DescentStaticWordColumn.frame (B.tariff true).base amount (tariff true) T x afterTrue).trans
      (DescentStaticWordColumn.frame (B.tariff false).base amount (tariff false) m x afterFalse)

variable {I : C→Type} [∀c,Fintype (I c)]
    (seat : C↪Fin n×Fin M) (item : ∀c,I c≃Fin (Fintype.card (I c)))
    (cnt : Fin n→Fin M→Fin (s.pairs+1)) (counts : Chronology.Counts seat (fun c=>Fintype.card (I c)) cnt)
    (prof : (Σc,I c)→Profile G.C)
local notation "slot" => spot s seat item cnt counts
variable (z : ℕ) (positive : 0 < z)

include positive in
theorem packed_layout (m : Memory w) (space : Space B w n) (fit : ROMSpace s M n w B) (_width : SixBirths.width s M≤w)
    (board : Fin n→Cell (SixBirths.width s M)) (input : ∀i,m (B.pairs.base+i.val)=(board i).val)
    (live : ∀c x,digit (s.digit+1) (SixBirths.slot (seat c).2 (slot ⟨c,x⟩).2.2 (0:Fin 6)).val
      (board (seat c).1).val=DescentTerminalEpochFlags.encode (prof ⟨c,x⟩)+1)
    (holes : ∀ (i : Fin n) (a : Fin M) (j : Fin s.pairs),(cnt i a).val≤j.val→
      digit (s.digit+1) (SixBirths.slot a j (0:Fin 6)).val (board i).val=0)
    (budget : Fintype.card (Σc,I c)*(G.C+8+8*G.k) < 2^w) :
    let fee:=fun b (i : Fin n)=>tariff b (board i).val
    let result:=DescentPackedLayoutCPU.after B (mounted s B M G m) fee
    ((install s B M w G).seq (DescentPackedLayoutCPU.program B w n)).Exec m result
        ((4+10*amount)+(4+10*amount)+DescentPackedLayoutCPU.ticks B n) ∧
      result B.out=if bestLayout (branchWidth G (fun _=>z) prof) then (1:Word w) else 0 := by
  dsimp only
  let fee:=fun b (i : Fin n)=>tariff b (board i).val
  obtain ⟨setup,rom,frame⟩:=mount (G:=G) s B m fit
  have whole b : (∑i,fee b i)=∑v,layoutUnits G.k b (prof v) :=
    total s (profileCode G.C) seat item cnt counts prof (fun i=>(board i).val) b live holes
  have bounds b : (∑i,fee b i) < 2^w := by
    rw [whole]
    exact (Finset.sum_le_sum (fun i _=>layout_units_bound G.k (prof i) b)).trans_lt (by simpa [Nat.mul_comm] using budget)
  refine ⟨setup.then (DescentPackedLayoutCPU.run B _ _ fee space (fun i=>(frame _ (.inl
    (by have a:=fit.low;have j:=i.isLt;omega))).trans (input i)) (fun b i=>(board i).isLt.trans_le (fit.room b))
    (fun b i=>rom b _ (board i).isLt)),?_⟩
  rw [DescentPackedLayoutCPU.read B _ fee space bounds,whole,whole,best_units G z positive]
  simp

private theorem mount_cheap (addr count w : ℕ) (delta : ℕ→ℕ) : CheapCode (DescentStaticWordColumn.program w addr delta count) := by
  induction count with
  | zero=>exact @scan_cheap _ _ _ _
  | succ j ih=>exact cheap_seq ih (@scan_cheap _ _ _ _)

set_option maxHeartbeats 1600000 in
theorem cheap (G : PoweredGadget F) : CheapCode ((install s B M w G).seq (DescentPackedLayoutCPU.program B w n)) := by
  let side := fun b => DescentPackedLayoutCPU.side B b w n
  let words := fun b => DescentStaticWordColumn.program w (B.tariff b).base
    (score (G := G) s (profileCode G.C) M b) amount
  let choose := ProtocolRAM.scan w B.out 1 (DescentBestLayoutRAM.chooseLine B)
  have sideCheap (b : Bool) : CheapCode (side b) := by
    let read := DescentPackedScore.read B.pairs (B.tariff b)
    exact @cheap_seq w (ProtocolRAM.scan w (B.counts b) n read)
      (ProtocolRAMEndpointPrefix.exclusive w (B.counts b) (B.starts b) n)
      (@scan_cheap w (B.counts b) n read)
      (@ProtocolRAMRankCheap.exclusive_cheap w (B.counts b) (B.starts b) n)
  have wordsCheap (b : Bool) : CheapCode (words b) :=
    @mount_cheap (B.tariff b).base amount w (score (G := G) s (profileCode G.C) M b)
  exact @cheap_seq w ((words false).seq (words true)) (((side false).seq (side true)).seq choose)
    (@cheap_seq w (words false) (words true) (@wordsCheap false) (@wordsCheap true))
    (@cheap_seq w ((side false).seq (side true)) choose
      (@cheap_seq w (side false) (side true) (@sideCheap false) (@sideCheap true))
      (@scan_cheap w B.out 1 (DescentBestLayoutRAM.chooseLine B)))

end
end Hierarchy.DescentPacking.PackedMatch.LayoutSum

end OAI
