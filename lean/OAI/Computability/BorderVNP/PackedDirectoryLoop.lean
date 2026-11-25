import OAI.Computability.BorderVNP.PackedDirectoryEval
import OAI.Computability.BorderVNP.PackedDirectoryWriter

/-! # Running the compact directory loop on the shared team memory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.ISA

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open DiagonalResidueRAM (word word_val word_add)

variable {w : ℕ}

/-- The memory words emitted by a positive candidate; empty candidates emit none. -/
def output (w : ℕ) (r : Row) : List (Word w) :=
  if r.width = 0 then [] else r.words.map (word w)

/-- Each populated record occupies seven words; a skipped record occupies zero. -/
theorem output_length (w : ℕ) (r : Row) : (output w r).length = if r.width = 0 then 0 else 7 := by
  by_cases h : r.width = 0 <;> simp [output,h,Row.words]

private theorem prepared_congr {d : Layout} {p l : ℕ} {s t : Reg → ℕ} (h : Prepared d p l s)
    (ht : ∀ i : Reg, i.val ≤ 18 → t i = s i) : Prepared d p l t := by
  rcases h with ⟨hc,hs,hb,hd⟩
  constructor <;> simp (config := { decide := true }) [ht,hc,hs,hb,hd]

private theorem result_words (s : Bank w) :
    [32,33,34,35,36,37,38].map s = (result (readings s)).words.map (word w) := by
  simp [result,Row.words,readings,word]

/-- Execute a single candidate, skipping it if its width vanishes. The candidate counter
advances in both cases, but the output address advances only on a populated row. -/
theorem rowStep_runs {d : Layout} {p l : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (a : ℕ) (prepared : Prepared d p l (readings s))
    (ptr : (s 20).val = a) (room : a+7 < 2^w) (next : (s 19).val+1 < 2^w)
    (safe : candidate.safeReadOnly w (readings pub) (readings m) (readings s)) :
    let row := d.row (placement (readings m) p) (placement (readings m) l) (s 19).val
    ∃ es t, Runs pub macros rowStep s m es t (putWords m a (output w row)) ∧
      traceCost es ≤ candidate.slots+18 ∧ Prepared d p l (readings t) ∧
      (t 19).val = (s 19).val+1 ∧ (t 20).val = a+(output w row).length ∧ t 21 = s 21 := by
  let row := d.row (placement (readings m) p) (placement (readings m) l) (s 19).val
  obtain ⟨es,u,hcalc,hcost,hu⟩ := candidate.runReadOnly pub macros m s safe
  have hlow (i : Reg) (hi : i.val < 22) : u i = s i := by
    apply Fin.ext
    exact (congrFun hu i).trans (candidate.evalNat_protected _ _ _ (by decide : candidate.protects 22 = true) i hi)
  have hres : result (readings u) = row :=
    (congrArg result hu).trans (candidate_eval _ _ _ prepared)
  have hzero : (u 0).val = 0 := (congrArg Fin.val (hlow 0 (by decide))).trans prepared.constants.1
  have hone : u 1 = 1 := by
    have h : (u 1).val = 1 := (congrArg Fin.val (hlow 1 (by decide))).trans prepared.constants.2.1
    apply Fin.ext
    simpa only [Fin.val_one',Nat.mod_eq_of_lt (by omega : 1 < 2^w)] using h
  have hptr : u 20 = word w a := Fin.ext (by rw [hlow _ (by decide),ptr,word_val w a (by omega)])
  have hw : (u 38).val = row.width := congrArg Row.width hres
  let branch : Code := .ifLt 0 38 (pushWords [32,33,34,35,36,37,38]) .nop
  have emit : ∃ fs v, Runs pub macros branch u m fs v (putWords m a (output w row)) ∧
      traceCost fs ≤ 16 ∧ (∀ i : Reg, i ≠ 20 → v i = u i) ∧
      (v 20).val = a+(output w row).length := by
    by_cases hz : row.width = 0
    · have guard : ¬ u 0 < u 38 := by change ¬ (u 0).val < (u 38).val; omega
      have r := Runs.ifLt (pub := pub) (macros := macros) (s := u) (m := m) (x := 0) (y := 38) (a := pushWords [32,33,34,35,36,37,38]) (b := .nop)
        (by simpa only [guard,ite_false] using (Runs.localStep (pub := pub) (macros := macros)
          (c := .nop) (s := u) m rfl rfl))
      refine ⟨[tick w,tick w],u,?_,by change 2 ≤ 16; decide, fun _ _ => rfl,?_⟩
      · simpa [branch,output,hz,putWords] using r
      · simpa [output,hz] using (congrArg Fin.val (hlow 20 (by decide))).trans ptr
    · have guard : u 0 < u 38 := by change (u 0).val < (u 38).val; omega
      obtain ⟨fs,run,ct⟩ := pushWords_runs pub macros [32,33,34,35,36,37,38] u m a hptr hone room (by decide)
      have words : [32,33,34,35,36,37,38].map u = output w row := by
        rw [result_words,hres,output,ite_eq_right hz]
      rw [words] at run
      refine ⟨_,_,Runs.ifLt (by simpa only [guard,ite_true] using run),?_,
        fun i hi => Function.update_of_ne hi ..,?_⟩
      · change 1+traceCost fs ≤ 16
        simp only [List.length_cons,List.length_nil] at ct
        omega
      · rw [Function.update_self,output_length,ite_eq_right hz]
        exact word_val w (a+7) room
  obtain ⟨fs,v,r,hc,hkeep,hv⟩ := emit
  let m' := putWords m a (output w row)
  let t := Function.update v 19 (v 19 + v 1)
  have advance : Runs pub macros (.binary .add 19 19 1) v m' [tick w] t m' := Runs.localStep _ rfl rfl
  have keep (i : Reg) (hi : i.val ≤ 18) : t i = s i := by
    have h19 : i ≠ 19 := by intro e; subst i; omega
    have h20 : i ≠ 20 := by intro e; subst i; omega
    exact (Function.update_of_ne h19 ..).trans ((hkeep i h20).trans (hlow i (by omega)))
  refine ⟨_,t,.seq hcalc (.seq r advance),?_,prepared_congr prepared (fun i hi => congrArg Fin.val (keep i hi)),?_,?_,?_⟩
  · rw [show traceCost (es ++ (fs ++ [tick w])) = traceCost es + (traceCost fs + 1) by
      simp only [traceCost,VPVNP.RAMBuckets.cost_append]; rfl]
    omega
  · rw [show t 19 = v 19+v 1 from Function.update_self .., hkeep 19 (by decide), hkeep 1 (by decide),
      hlow 19 (by decide), hone, Fin.val_add]
    simp only [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < 2^w),Nat.mod_eq_of_lt next]
  · simpa [t] using hv
  · change Function.update v 19 (v 19+v 1) 21 = s 21
    rw [Function.update_of_ne (by decide : (21:Reg) ≠ 19),hkeep 21 (by decide),hlow 21 (by decide)]

end Packing.Directory.ISA

end BorderVNP
end Computability
end OAI
