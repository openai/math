import OAI.ThreeFlat.Diagonal.TraceSeedBanks
import OAI.ThreeFlat.Diagonal.TraceBitNetwork
import OAI.ThreeFlat.RAM.RawTickBuilder
import OAI.ThreeFlat.RAM.HistoryCompiledRows

namespace OAI
/-! # The three actual native H-bucket operand banks after one finite seed procedure -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM RAM RAM.EffectStream LaneCursor LaneCursor.RowLayout
open scoped Fin.CommRing
variable {F : Type*} [Fintype F] [CommRing F] {w W p S f q low : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3≤w+1) (hp : p≤2^(w+1))
    (base : ℕ) (st : Word w) (hs : S≤2^w) (hf : f≤2^(w+1)) (r k : ℕ)
    (fit : S+f≤2^(1+((q+1)+low)))
local notation "d" => (q+1)+low
local notation "P" => layout hF hw hp base st hs hf r k fit
local notation "R" => rawLayout hF hw hp base st hs hf r k fit
local notation "G" => TraceStaticRow.gateTable hF hw hp base f st r k d
local notation "N" => network hF hw hp base st hs hf r k d
local notation "o" => 1+(d+d)
local notation "rows" => 2^(q+1)*2^low

noncomputable def bankRecords (ids masks dict : ℕ) : List (Record W) := (P).seedRecords ids masks dict (fun j : Fin (G).cells => ((HistoryCompiledRows.library G).id j).val)

local notation "es" => bankRecords (W:=W) hF hw hp base st hs hf r k fit

def Banks (ids masks dict : ℕ) (m : Memory W) :=
  (∀ j : Fin (G).cells, (m (ids+j.val)).val=((HistoryCompiledRows.library G).id j).val) ∧
  (∀ a : Occurrence N, (m (dict+((P).offset ((P).code a)).val)).val=((P).code a).val) ∧
  (∀ i, (m (masks+i.val)).val=((P).offset i).val)

theorem seed_image (ids masks dict : ℕ) (m : Memory W) (room : SeedRoom (G).cells o rows ids masks dict W)
    (lib : Fintype.card ((Fin 3→Bool)→F)≤2^W) :
    Banks hF hw hp base st hs hf r k fit ids masks dict (after m (events (es ids masks dict))) := by
  have read (j : SeedKey (G).cells o) := (P).seed_read ids masks dict (fun j : Fin (G).cells => ((HistoryCompiledRows.library G).id j).val) m room j
  refine ⟨?_,?_,?_⟩
  · intro j
    exact (congrArg Fin.val (read (.inl j))).trans (Fin.val_cast_of_lt (((HistoryCompiledRows.library G).id j).isLt.trans_le lib))
  · intro a
    have canon : firstIndex (P).offset ((P).code a)=(P).code a :=
      firstIndex_congr (R).offset (first_eq (R).offset ((R).code a))
    have ok : ((P).code a).val<2^W := ((P).code a).isLt.trans_le (by have := room.maskEnd; have := room.wordEnd; omega)
    simpa only [bankRecords,seedAddress,seedValue,canon,Fin.val_cast_of_lt ok] using congrArg Fin.val (read (.inr (.inr ((P).code a))))
  · intro i
    exact (congrArg Fin.val (read (.inr (.inl i)))).trans
      (Fin.val_cast_of_lt (((P).offset i).isLt.trans_le (by have := room.wordEnd; omega)))

theorem native_seed (ids masks dict src tmp raw : ℕ) (code : FieldCode F W)
    (room : SeedRoom (G).cells o rows ids masks dict W) (lib : Fintype.card ((Fin 3→Bool)→F)≤2^W)
    (apart : tmp+2*((G).cells+(o+o)) ≤ src ∨ src+W*(2*((G).cells+(o+o)))≤tmp)
    (scratch : tmp+2*((G).cells+(o+o))<2^W) (source : src+W*(2*((G).cells+(o+o)))<2^W)
    (banks : tmp+2*((G).cells+(o+o))≤ ids ∨ dict+rows≤tmp)
    (rawScratch : raw+11*(N).cells≤tmp ∨ tmp+2*((G).cells+(o+o))≤raw)
    (rawBanks : raw+11*(N).cells≤ ids ∨ dict+rows≤raw) :
    let n := (G).cells+(o+o)
    (EffectSeed.procedure W src tmp n).Spec
      (fun m => EffectSeed.Input src tmp (es ids masks dict) m ∧ RawTickBuilder.loaded N code raw m)
      (fun m after => (Banks hF hw hp base st hs hf r k fit ids masks dict after ∧
          RawTickBuilder.loaded N code raw after) ∧
        ∀ i, (i<tmp ∨ tmp+2*n≤ i) → (i< ids ∨ dict+rows≤ i) → after i=m i)
      ((2*n)*(5*W+6)+6+(4+6*n)) := by
  intro n
  let records := es ids masks dict
  have len : records.length=n := (P).seedRecords_length _ _ _ _
  have safe : Safe tmp records := (P).seed_safe ids masks dict tmp (fun j : Fin (G).cells => ((HistoryCompiledRows.library G).id j).val) room banks
  have runner : (EffectSeed.procedure W src tmp n).Spec (EffectSeed.Input src tmp records)
      (fun m out => out=after (fillSegment tmp (2*n) (packedWord tmp records) m) (events records))
      (2*n*(5*W+6)+6+(4+6*n)) := by
    rw [← len]
    exact EffectSeed.seed_spec src tmp records (by simpa only [len] using apart)
      (by simpa only [len] using scratch) (by simpa only [len] using source) safe
  intro pcCount regCount slotCount M pc reg pub exit installed publicData c m entry input
  obtain ⟨time,ht,out,result,run,done,body⟩ :=
    runner M pc reg pub exit installed publicData c m entry input.1
  subst result
  let packed := fillSegment tmp (2*n) (packedWord tmp records) m
  have frame (a : ℕ) (outsideTmp : a<tmp ∨ tmp+2*n≤a) (outsideBanks : a < ids ∨ dict+rows≤a) :
      after packed (events records) a=m a := by
    have unchanged := (P).seed_outside ids masks dict
      (fun j : Fin (G).cells => ((HistoryCompiledRows.library G).id j).val) packed room a outsideBanks
    exact unchanged.trans (ite_eq_right (by omega : ¬(tmp≤a ∧ a<tmp+2*n)))
  refine ⟨time,ht,out,_,run,done,⟨⟨seed_image hF hw hp base st hs hf r k fit ids masks dict packed room lib,?_⟩,frame⟩⟩
  intro i j
  let a := raw+11*i.val+j.val
  have ri := i.isLt
  have rj := j.isLt
  have dis1 : a<tmp ∨ tmp+2*n≤a := by dsimp [a,n]; omega
  have dis2 : a < ids ∨ dict+rows≤a := by dsimp [a]; omega
  exact (frame a dis1 dis2).trans (input.2 i j)


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
