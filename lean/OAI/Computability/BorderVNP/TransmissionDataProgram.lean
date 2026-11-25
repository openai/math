import OAI.Computability.BorderVNP.TransmissionDataStep
import OAI.Computability.BorderVNP.TransmissionCost

/-! # Native construction of the initial transmission table from all data demands -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission.DataWriter

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open Packing.Directory.ISA (putWords putWords_append putWords_outside putWords_read)
open DiagonalResidueRAM (word word_val)

variable {w : ℕ}

/-- Wire-format words of one lowered data row in the initial memory. -/
def encoded (d : Layout) (m : Memory w) (i : ℕ) : List (Word w) :=
  (record d (readings m) (demandAt (readings m) (d.input+i*7))).map (word w)

/-- The stream emitted through the first `i` demand rows. -/
def emittedPrefix (d : Layout) (m : Memory w) : ℕ → List (Word w)
  | 0 => []
  | i+1 => emittedPrefix d m i ++ encoded d m i

private theorem prefix_length (d : Layout) (m : Memory w) (i : ℕ) : (emittedPrefix d m i).length = i*7 := by
  induction i with
  | zero => rfl
  | succ i ih => rw [emittedPrefix,List.length_append,ih]; change i*7+7 = (i+1)*7; omega

/-- All output words and the published physical count. -/
def publish (d : Layout) (pub : Arg → Word w) (m : Memory w) : Memory w :=
  Function.update (putWords m d.output (emittedPrefix d m d.count)) ((pub 0).val+13) (word w d.count)

/-- The complete output directory is separate from the raw demands and the two owner
words used by each demand. Either ordering of the allocated intervals is supported. -/
structure Separate (d : Layout) (mem : ℕ → ℕ) : Prop where
  /-- Disjoint raw input and emitted record spans. -/
  raw : d.input+d.count*7 ≤ d.output ∨ d.output+d.count*7 ≤ d.input
  /-- Disjoint two-word owner entry for each active input record. -/
  owner : ∀ i < d.count, let atOwner := d.owners+(demandAt mem (d.input+i*7)).cell*2
    atOwner+2 ≤ d.output ∨ d.output+d.count*7 ≤ atOwner

private theorem prefix_input {d : Layout} {m : Memory w} {i : ℕ} (hi : i < d.count)
    (sep : Separate d (readings m)) :
    let m' := putWords m d.output (emittedPrefix d m i)
    demandAt (readings m') (d.input+i*7) = demandAt (readings m) (d.input+i*7) ∧
    let addr := d.owners+(demandAt (readings m) (d.input+i*7)).cell*2
    readings m' addr = readings m addr ∧ readings m' (addr+1) = readings m (addr+1) := by
  let m' := putWords m d.output (emittedPrefix d m i)
  have same (x : ℕ) (hx : x < d.output ∨ d.output+i*7 ≤ x) : readings m' x = readings m x :=
    congrArg Fin.val (putWords_outside m d.output x (emittedPrefix d m i) (by rwa [prefix_length]))
  have field (j : ℕ) (hj : j < 7) := same (d.input+i*7+j) (by rcases sep.raw with h | h <;> omega)
  have own := sep.owner i hi
  refine ⟨?_,same _ (by dsimp only at own; omega),same _ (by dsimp only at own; omega)⟩
  unfold demandAt
  congr 1
  all_goals first | exact field 0 (by decide) | exact field 1 (by decide) | exact field 2 (by decide) | exact field 3 (by decide) | exact field 4 (by decide) | exact field 5 (by decide) | exact field 6 (by decide)

private theorem finish_runs (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (count : ℕ) (hc : (s 5).val = count) (frame : (pub 0).val+13 < 2^w) :
    ∃ es t, Runs pub macros (writeFrame 5 62 63 13) s m es t
      (Function.update m ((pub 0).val+13) (word w count)) ∧ traceCost es ≤ 4 := by
  let a := Function.update s 62 (pub 0)
  let b := Function.update a 63 (13 : Word w)
  let c := Function.update b 62 (pub 0 + 13)
  have ra : Runs pub macros (.publicWord 62 0) s m [tick w] a m := Runs.localStep _ rfl rfl
  have rb : Runs pub macros (.constant 63 13) a m [tick w] b m := Runs.localStep _ rfl rfl
  have rc : Runs pub macros (.binary .add 62 62 63) b m [tick w] c m :=
    Runs.localStep _ rfl (by simp [Code.atom,BinaryOp.eval,c,b,a])
  have st := Runs.store pub macros 62 5 c m
  have addr : (c 62).val = (pub 0).val+13 := by
    change (pub 0 + Fin.ofNat _ 13).val = _
    rw [Fin.val_add,Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : 13 < 2^w),Nat.mod_eq_of_lt frame]
  have val : c 5 = word w count := by
    have bound := (s 5).isLt
    apply Fin.ext
    rw [word_val _ _ (by omega)]
    simpa [c,b,a] using hc
  rw [addr, val] at st
  have run : Runs pub macros (writeFrame 5 62 63 13) s m _ _ _ := ra.seq (rb.seq (rc.seq st))
  exact ⟨_,_,run,run.cost_le_slots (by decide)⟩

/-- The fixed native compiler lowers every actual data demand, places its seven
addressed words at the start of the output directory, and publishes the number to
frame field 13. Its charge is linear in the number of demands. -/
theorem program_runs (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) :
    let d := layout (readings pub) (readings m)
    (pub 0).val+72 < 2^w → 0 < d.pins.teams → d.pins.stride < 2^w →
    d.output+d.count*7 < 2^w → Separate d (readings m) →
    (∀ i < d.count, RowFits w d (readings m) i) →
    ∃ es t, Runs pub macros program s m es t (publish d pub m) ∧
      traceCost es ≤ setup.slots + d.count*(step.slots+1) + 5 := by
  intro d frame teams stride room sep fits
  obtain ⟨es,a,ra,ca,ha⟩ := setup.runReadOnly pub macros m s (setup_safe _ _ _ frame teams stride)
  let M (i : ℕ) := putWords m d.output (emittedPrefix d m i)
  let Inv (i : ℕ) (s : Bank w) (mt : Memory w) := Prepared d i (readings s) ∧ mt = M i
  have init : Inv 0 a m := ⟨ha ▸ setup_eval _ _ _, rfl⟩
  have next (i : ℕ) (hi : i < d.count) (v : Bank w) (mt : Memory w) (iv : Inv i v mt) :
      ∃ fs z mz, Runs pub macros step v mt fs z mz ∧ Inv (i+1) z mz ∧ traceCost fs ≤ step.slots := by
    obtain ⟨hv,rfl⟩ := iv
    obtain ⟨row,howner,hbank⟩ := prefix_input hi sep
    let r := demandAt (readings m) (d.input+i*7)
    have ok := fits i hi
    have fit' : RowFits w d (readings (M i)) i :=
      ⟨ok.input,by simpa only [M,row] using ok.owner,by simpa only [M,row,hbank] using ok.destination,
        by simpa only [M,row] using ok.source⟩
    have words : (record d (readings (M i)) (demandAt (readings (M i)) (d.input+i*7))).map (word w) = encoded d m i := by
      simp only [M, row, record, howner, hbank, encoded]
    obtain ⟨fs,z,rz,hz,cost⟩ := step_runs pub macros v (M i) hv fit' (by omega)
    rw [words] at rz
    refine ⟨fs,z,_,rz,⟨hz,?_⟩,cost⟩
    simp only [M,emittedPrefix,putWords_append,prefix_length]
  obtain ⟨fs,z,mz,loop,ih,cl⟩ := loop_runs 10 5 step d.count (fun _ => step.slots) Inv
    (fun _ _ _ iv => ⟨iv.1.index,iv.1.input.2.1⟩) next 0 (Nat.zero_le _) a m init
  obtain ⟨gs,t,finish,cf⟩ := finish_runs pub macros z mz d.count ih.1.input.2.1 (by omega)
  rw [ih.2] at loop finish
  refine ⟨_,t,ra.seq (loop.seq finish),?_⟩
  rw [cost_append,cost_append]
  simp only [Nat.Ico_zero_eq_range, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id] at cl
  omega

end RoutingISA.Transmission.DataWriter

end BorderVNP
end Computability
end OAI
