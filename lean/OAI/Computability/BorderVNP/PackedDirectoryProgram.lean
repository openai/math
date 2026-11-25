import OAI.Computability.BorderVNP.PackedDirectoryScan
import OAI.Computability.BorderVNP.PackedDirectoryFrame
import OAI.Computability.BorderVNP.PackedDirectoryBits

/-! # The executable public placement directory in Proposition 7.2 -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.ISA

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open DiagonalResidueRAM (word)

/-- Wire encoding of the populated seven-word demand rows. -/
def encodeRows (w : ℕ) (rows : List Row) : List (Word w) :=
  rows.flatMap fun r => r.words.map (word w)

/-- No hidden padding or record separator intervenes between the seven-word rows. -/
theorem encodeRows_length (w : ℕ) (rows : List Row) :
    (encodeRows w rows).length = 7*rows.length := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    change ((r.words.map (word w)) ++ encodeRows w rs).length = 7*(rs.length+1)
    rw [List.length_append,List.length_map,ih]
    change 7+7*rs.length = _
    omega

/-- The final word memory is the compact row directory together with its true populated
count. The output base remains in frame word 8. -/
def publish {w : ℕ} (m : Memory w) (frame base : ℕ) (rows : List Row) : Memory w :=
  Function.update (putWords m base (encodeRows w rows)) (frame+9) (word w rows.length)

/-- Given the reconstructed placements and word room, the actual fixed RAM table returns
the complete seven-word directory and its count. There is one constant number of native
ticks per candidate, including the empty candidates and terminal loop test. -/
theorem program_runs {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) :
    let d := frameLayout (readings pub) (readings m)
    let f := frameField (readings pub) (readings m)
    let pp := placement (readings m) (f 64)
    let lp := placement (readings m) (f 65)
    let rows := d.directory pp lp
    0 < d.teams → 0 < d.processors → 0 < d.block →
    (pub 0).val+70 < f 8 → d.stride < 2^w → f 8+7*d.candidates < 2^w →
    f 8+7*d.candidates ≤ f 64 → f 8+7*d.candidates ≤ f 65 →
    (∀ i < d.candidates, if i < 2*d.entries then LayoutFitsPrivate d w (f 64) pp i
      else LayoutFitsLive d w (f 65) lp i) →
    ∃ es t, Runs pub macros program s m es t (publish m (pub 0).val (f 8) rows) ∧
      traceCost es ≤ setup.slots + (candidate.slots+19)*d.candidates + 8 := by
  intro d f pp lp rows ht hr hb before stride room hpb hlb fits
  have safe := setup_safe (w := w) (readings pub) (readings m) (readings s) ht hr hb (by
    change (pub 0).val+70 < 2^w
    omega) (by change d.candidates < 2^w; omega) stride
  obtain ⟨es,u,hsetup,ct,values⟩ := setup.runReadOnly pub macros m s safe
  have ready := setup_eval (readings pub) (readings m) (readings s)
  rw [← values] at ready
  obtain ⟨prepared,hi,ha,base⟩ := ready
  have hf : 0 < d.fields := Nat.zero_lt_succ _
  obtain ⟨fs,v,loop,ft,ptr,end21⟩ := scan_runs d (f 64) (f 65) pp lp pub macros 0
    d.candidates (Nat.zero_add _) ⟨hr,hf⟩ fits u m (f 8) prepared hi ha rfl rfl ⟨room,hpb,hlb⟩
  have eq : stream (d.row pp lp) w 0 d.candidates = encodeRows w rows :=
    stream_directory d pp lp w
  rw [eq] at loop ptr
  rw [encodeRows_length] at ptr
  have vbase : (v 21).val = f 8 := (congrArg Fin.val end21).trans base
  obtain ⟨gs,t,finishRun,gt⟩ := finish_runs pub macros v (putWords m (f 8) (encodeRows w rows))
    (f 8) rows.length vbase ptr (by omega)
  refine ⟨_,_,.seq hsetup (.seq loop finishRun),?_⟩
  simp only [traceCost,VPVNP.RAMBuckets.cost_append] at *
  omega

/-- The populated count and every occupied output address can be read by the next stage. -/
theorem publish_read {w : ℕ} (m : Memory w) (frame base : ℕ) (rows : List Row)
    (before : frame+9 < base) :
    publish m frame base rows (frame+9) = word w rows.length ∧
      ∀ i : Fin (encodeRows w rows).length, publish m frame base rows (base+i) = (encodeRows w rows)[i] := by
  refine ⟨Function.update_self ..,fun i => ?_⟩
  rw [publish,Function.update_of_ne (by omega : base+i.val ≠ frame+9)]
  exact putWords_read ..

end Packing.Directory.ISA

end BorderVNP
end Computability
end OAI
