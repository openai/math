import OAI.Hierarchy.ProbeStageChoiceReads
import OAI.Hierarchy.ProbeStageHistoryCost

namespace OAI
/-! # The actual chosen color and charged probes of a physical stage record -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section
attribute [local instance] Classical.decEq

variable {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => wordBits h d copies
local notation "S" => recordScratch h d j.val
local notation "R" => recordRow h d j.val i.val
local notation "A" => recordAdvice h d j.val

def queryGood (π : Equiv.Perm (Fin (2^h))) :=
  let p := (history h d π j.val).tiles
  let pos := radix_pos h d
  Greedy.available (leftBlock p pos) (rightBlock p pos) (Greedy.before _ i.val)
    (Greedy.colors pos ((formatAdvice h d).pick p pos) (leftBlock p pos) (rightBlock p pos) i.val) i

theorem query_good_iff (π : Equiv.Perm (Fin (2^h))) (c : Fin (radix h d)) :
    c∈queryGood j i π ↔ c∉queryFull j i π true∪queryFull j i π false := by
  let p := (history h d π j.val).tiles
  let pos := radix_pos h d
  exact Greedy.available_prefix pos ((formatAdvice h d).pick p pos) (leftBlock p pos) (rightBlock p pos) i c

theorem query_good_nonempty (π : Equiv.Perm (Fin (2^h))) : (queryGood j i π).Nonempty := by
  apply Greedy.available_nonempty (radix_pos h d)
  · intro x
    simpa only [Fintype.card_subtype,Fintype.card_fin] using
      Fintype.card_le_of_injective _ (leftBlockFiber (history h d π j.val).tiles (radix_pos h d) x).injective
  · intro x
    simpa only [Fintype.card_subtype,Fintype.card_fin] using
      Fintype.card_le_of_injective _ (rightBlockFiber (history h d π j.val).tiles (radix_pos h d) x).injective

include hd in
theorem quota_fits : quota (radix h d)<2^W := by
  rw [quota_radix]
  have scale := Nat.mul_le_mul_right (digit h d) (show 8≤9*d by omega)
  have sub : 9*d*digit h d≤h := Nat.mul_div_le _ _
  exact ((Nat.pow_le_pow_right (by decide : 0<2) (show 2+8*digit h d≤roomBits h d by
    unfold roomBits;omega)) : 2^(2+8*digit h d)≤extent h d).trans_lt (extent_word h d copies)

include hd j in
theorem length_fits : stringLength h<2^W := by
  have cap := (region_room (h:=h) hd j.isLt.le).2.2.2.1
  exact ((Nat.le_mul_of_pos_left _ (pow_pos (radix_pos h d) 4)).trans cap).trans_lt (regionSize_fits j)

theorem choice_packed (π : Equiv.Perm (Fin (2^h))) (m : Memory W) (rom : immutable h d W j m)
    (ids : ordinalIDs j i hd π m) (pre : PrefixState hd π j i.val m) :
    FastField.Represents (Record.find A S) (preparedMemory j i m) ((formatAdvice h d).row (queryRow j i π))
      (queryFull j i π true) (queryFull j i π false) := by
  let p := preparedMemory j i m
  let s := Record.find A S
  let row := (formatAdvice h d).row (queryRow j i π)
  have left := fun k hk => prepared_mask j i hd π m rom ids pre true ⟨k,hk⟩
  have right := fun k hk => prepared_mask j i hd π m rom ids pre false ⟨k,hk⟩
  refine ⟨left,right,?_⟩
  intro k hk
  let v := FastField.availableWord s p k
  have exactWord : v.val=PackedMask.word row (queryFull j i π true∪queryFull j i π false) (fieldWidth h) k := by
    dsimp only [v,FastField.availableWord,BinaryOp.eval]
    simp only [Fin.val_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.and_le_left.trans_lt (p _).isLt)]
    exact (congrArg₂ (fun x y : ℕ => x &&& y) (left k hk) (right k hk)).trans (PackedMask.and_word ..)
  have small : v.val<2^(fieldWidth h) := exactWord ▸ PackedMask.word_lt ..
  have addr : ((region h d j 7:Word W)+v).val=region h d j 7+v.val := by
    have fit := region_word j.isLt (7:Fin 16) (small.trans_le (least_size h d))
    simpa using add_word fit
  change p ((region h d j 7:Word W)+v).val=_
  rw [addr,show p (region h d j 7+v.val)=m _ from prepared_region j i m _ _,least_word j m rom _ small]

theorem choice_string (π : Equiv.Perm (Fin (2^h))) (m : Memory W) (rom : immutable h d W j m)
    (ids : ordinalIDs j i hd π m) (k : Fin (stringLength h)) :
    Record.stringWord A S (fastMemory j i m) (k.val:Word W)=
      (((formatAdvice h d).row (queryRow j i π) k).val:Word W) := by
  let r := queryRow j i π
  let b := fun u => blockNumber hd j π (queryBlock j i π u)
  have so : preparedMemory j i m (scratch h d j 5)=((rowCode r*stringLength h:ℕ):Word W) := by
    exact prepared_word j i hd m rom (b true) (b false) r ids 5
  have small : rowCode r*stringLength h+k.val<regionSize h d := by
    apply lt_of_lt_of_le _ (region_room (h:=h) hd j.isLt.le).2.2.2.1
    exact (Nat.add_lt_add_left k.isLt _).trans_le (by
      rw [←Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (rowCode_lt r))
  have fit := region_word j.isLt (6:Fin 16) small
  change fastMemory j i m ((region h d j 6 : Word W)+fastMemory j i m (scratch h d j 5:Word W).val+
    (k.val:Word W)).val=_
  rw [Fin.val_cast_of_lt (scratch_fits j 5),fast_frame j i m _ (scratch_ne j (by decide : (5:Fin 12)≠6)),
    so,←Nat.cast_add,←Nat.cast_add,Fin.val_cast_of_lt (by simpa only [Nat.add_assoc] using fit),Nat.add_assoc,
    fast_frame j i m _ (by have := scratch_separate h d j.val 6 6;omega),prepared_region,string_word hd j m rom r k]

theorem choice_input (π : Equiv.Perm (Fin (2^h))) (m : Memory W) (rom : immutable h d W j m)
    (ids : ordinalIDs j i hd π m) (pre : PrefixState hd π j i.val m) :
    Record.ChoiceInput A R S m ((formatAdvice h d).row (queryRow j i π))
      (queryFull j i π true) (queryFull j i π false) (queryGood j i π) := by
  have deg := (region_room (h:=h) hd j.isLt.le).2.1.trans_lt (regionSize_fits j)
  refine ⟨rfl,rfl,lt_of_lt_of_le (by decide : 0<1) (le_max_left ..),(chunks_cover h).1,
    query_good_iff j i π,choice_packed hd j i π m rom ids pre,choice_string hd j i π m rom ids,
    ?_,?_,deg,length_fits hd j,scratch_fits j 6,(chosen_low j i 0).trans (scratch_fits j 0),
    scratch_fits j 7,(chosen_low j i 6).ne',(chosen_low j i 7).ne'⟩
  · intro c
    rw [query_good_iff]
    let n := fun side => (scanningMemory j i m
      (scanningMemory j i m (scratch h d j (countPtr side):Word W).val+(c.val:Word W)).val).val
    change (n true < (quota (radix h d):Word W).val ∧ n false < (quota (radix h d):Word W).val) ↔ _
    have read (side : Bool) : n side=Greedy.prefixCount (endpointKey j π side) (assigned j π).color i.val (queryBlock j i π side) c :=
      scanning_count j i hd π m rom ids pre side c
    rw [read true,read false,Fin.val_cast_of_lt (quota_fits hd)]
    simp [queryFull,Greedy.prefixFull,not_or]
  · intro c x hx
    have fits := scratch_fits (h:=h) j
    let b := fun a => blockNumber hd j π (queryBlock j i π a)
    have below (t : Bool) (q : Fin 12) : scratch h d j q<counterLocation h d j.val t (b t) c := by
      unfold counterLocation
      have := scratch_separate h d j.val q (countArea t)
      omega
    have above (q : Fin 12) := chosen_low j i q
    change x ∈ [(scratch h d j 0:Word W).val,(scratch h d j 1:Word W).val,
      (scanningMemory j i m (scratch h d j (countPtr true):Word W).val+(c.val:Word W)).val,
      (scanningMemory j i m (scratch h d j (countPtr false):Word W).val+(c.val:Word W)).val] at hx
    rw [scanning_count_address j i hd π m rom ids true c,scanning_count_address j i hd π m rom ids false c,
      Fin.val_cast_of_lt (fits 0),Fin.val_cast_of_lt (fits 1)] at hx
    change x≠(scratch h d j 7:Word W).val ∧ x≠(R).chosen
    rw [Fin.val_cast_of_lt (fits 7)]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · exact ⟨scratch_ne j (by decide : (0:Fin 12)≠7),(above 0).ne'⟩
    · exact ⟨scratch_ne j (by decide : (1:Fin 12)≠7),(above 1).ne'⟩
    · exact ⟨(below true 7).ne',((above 7).trans (below true 7)).ne'⟩
    · exact ⟨(below false 7).ne',((above 7).trans (below false 7)).ne'⟩

/-- The native fallback charge and chosen word for the actual advised allocation. -/
theorem ordinal_choice (π : Equiv.Perm (Fin (2^h))) (m : Memory W) (rom : immutable h d W j m)
    (stored : ∀ q,m (argumentAddr j i q)=
      (Endpoints.words (history h d π j.val).tiles (radix_pos h d) (history h d π j.val).encode i q : Word W))
    (pre : PrefixState hd π j i.val m) :
    Record.scans A S R m=expectedScans h d π j.val i ∧
      Record.leftInput A S R m (R).chosen=(((assigned j π).color i).val:Word W) := by
  classical
  obtain ⟨ticks,c⟩ := Record.physical_choice A S R m _ _ _ _ (radix_pos h d) (query_good_nonempty j i π)
    (choice_input hd j i π m rom (ordinalIDs_of_words j i hd π m stored) pre)
  constructor
  · let bits := freeBits ((formatAdvice h d).row (queryRow j i π)) (queryGood j i π)
    have member : i∈(formatAdvice h d).fallbacks (radix_pos h d) (history h d π j.val).tiles ↔ bits=∅ := by
      simp only [MaskAdvice.fallbacks,Finset.mem_filter,Finset.mem_univ,true_and]
      rfl
    change (Record.scans A S R m)=(if i∈_ then radix h d else 0)
    rw [ticks]
    change (if bits.Nonempty then 0 else radix h d)=(if i∈_ then radix h d else 0)
    by_cases nonempty : bits.Nonempty
    · rw [ite_eq_left nonempty,ite_eq_right (mt member.mp nonempty.ne_empty)]
    · rw [ite_eq_right nonempty,ite_eq_left (member.mpr (Finset.not_nonempty_iff_eq_empty.mp nonempty))]
  · apply c.trans
    apply congrArg (fun c : Fin (radix h d) => (c.val:Word W))
    exact (Greedy.first_color (radix_pos h d) ((formatAdvice h d).pick _ _) _ _ i).symm

end
end Hierarchy.ProbeStage.Native

end OAI
