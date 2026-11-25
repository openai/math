import OAI.Computability.BorderVNP.PackedReportWriterRun
import OAI.Computability.BorderVNP.DiagonalTallySidecarDecode

/-! # Report rows emitted from the physically decoded site sidecar -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.Writer

open RoutingISA VPVNP.BurstRAM VPVNP.TapeWord TallySidecar DiagonalTallyBits

private theorem relative_field (ps : List Position) (i : ℕ) :
    (ps.flatMap Position.fields)[3*i+2]? = (ps[i]?).map Position.stagedReportRel := by
  induction ps generalizing i with
  | nil => simp
  | cons p ps ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa [Position.fields,Nat.mul_succ,Nat.add_assoc] using ih i

private theorem decoded_field {w : ℕ} (m : Memory w) (d H : ℕ) (ps : List Position)
    (hw : H ≤ w) (valid : TallySidecar.Fits H ps) (j : ℕ) (hj : j < (fields ps).length) :
    (outputMemory m d (words H ps) (d+j)).val = (fields ps)[j] := by
  have hi : j < (words H ps).length := by simpa [words] using hj
  have hs : (words H ps)[j].length ≤ w := by simpa [words] using hw
  rw [outputMemory_word_val _ _ _ j hi hs]
  have he := congrArg (fun (xs : List ℕ) => xs[j]?) (words_values H ps valid)
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,
    Option.map_some,Option.some.injEq] using he

/-- The memory image returned by the native sidecar decoder supplies the header and
the third word of every position, including when the list is empty. -/
theorem Frame.input_decoded {w : ℕ} (f : Frame) (m : Memory w) (H : ℕ) (ps : List Position)
    (hw : H ≤ w) (valid : TallySidecar.Fits H ps) (rel : ℕ → ℕ)
    (rows : ∀ i (hi : i < ps.length), rel i = ps[i].stagedReportRel) :
    f.input ps.length rel (readings (outputMemory m f.side (words H ps))) := by
  constructor
  · have he := decoded_field m f.side H ps hw valid 0 (by simp [fields])
    simpa [readings,fields] using he
  · intro i hi
    have hj : 3*(i+1) < (fields ps).length := by rw [fields_length]; omega
    rw [readings,decoded_field m f.side H ps hw valid _ hj,rows i hi]
    have he := relative_field ps i
    have hfield : (fields ps)[3*(i+1)]? = some ps[i].stagedReportRel := by
      rw [show 3*(i+1) = (3*i+2)+1 by omega]
      simpa [fields,List.getElem?_eq_getElem hi] using he
    simpa [List.getElem?_eq_getElem hj] using hfield

/-- Decode the actual count and position triples, then append the corresponding
sparse equality and zero records. Only the two explicitly allocated output regions
change. Each step is a native probe, arithmetic instruction or loop guard. -/
theorem decode_write_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (f : Frame) (p H : ℕ) (ps : List Position) (rel : ℕ → ℕ)
    (loaded : f.loaded (.ofWords s m)) (fit : f.Fits w ps.length rel)
    (hp : (s 16).val = p) (hh : (s 17).val = H) (hw : H ≤ w)
    (rawRoom : p+(1+3*ps.length)*H < 2^w) (sideRoom : f.side+(1+3*ps.length) < 2^w)
    (separate : p+(1+3*ps.length)*H ≤ f.side ∨ f.side+(1+3*ps.length) ≤ p)
    (valid : TallySidecar.Fits H ps) (raw : WordsAt m p (words H ps))
    (rows : ∀ i (hi : i < ps.length), rel i = ps[i].stagedReportRel) :
    BoundedRun pub mac (.seq decode program) s m
      (TallySidecar.headerSetup.slots + ticks 1 H + rowsSetup.slots + ticks (3*ps.length) H + (28*ps.length+23))
      (f.Result ps.length rel (readings (outputMemory m f.side (words H ps)))) := by
  have room := fit.dst_end
  obtain ⟨a,t,ra,ca,keep,_⟩ := decode_runs pub mac s m p f.side H ps hp hh loaded.1.2.1 hw
    (by omega) rawRoom sideRoom separate valid raw
  have ht : f.loaded (.ofWords t (outputMemory m f.side (words H ps))) := by
    simpa only [Frame.loaded,Frame.static,NatState.ofWords,readings,keep 19 (by decide),keep 20 (by decide),
      keep 21 (by decide),keep 25 (by decide),keep 26 (by decide),keep 27 (by decide),keep 24 (by decide),
      keep 28 (by decide),keep 29 (by decide)] using loaded
  obtain ⟨b,u,mu,rb,cb,h⟩ := program_runs pub mac t (outputMemory m f.side (words H ps)) f ps.length
    rel ht fit (f.input_decoded m H ps hw valid rel rows)
  exact ⟨_,u,mu,ra.seq rb,(VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add ca cb),h⟩

end Packing.BottomReports.Writer

end BorderVNP
end Computability
end OAI
