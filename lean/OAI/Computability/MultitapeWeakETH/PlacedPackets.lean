import OAI.Computability.MultitapeWeakETH.ChildPackets

/-! # The joint old half-wire argument at a selected output site -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid.ChildScan

open IntegerMultiplication Code VPVNP Compression NetworkKernel PairSimulation LocalHistory NodeArguments
open private fiber_encode from OAI.Computability.VPVNP.PairNodeArguments
noncomputable section

variable {a g : ℕ} (X : State a g) {R : Type} (t : Term R X.network) (v : t.output.Site)
  (o : Order (t.Preimage v))

def packetWidths := List.ofFn fun j => tally (RefreshHalfDecoder.width X (o.entries j).val)

def packets (h : Placed t.place X.network.Half v) :=
  List.ofFn fun j => packed X (o.entries j).val (h _ (o.entries j).prop)

theorem packets_encode (h : Placed t.place X.network.Half v) :
    (packets X t v o h).flatten =
      ((fiber t.place v o (fun u => RefreshHalfDecoder.reader X u)).encode h) := by
  rw [fiber_encode]
  simp only [packets,packed_eq_encode,RefreshHalfDecoder.reader]

/-- An accepted subdivision represents precisely one joint tuple of independent half-wires
at the sites of the placement fiber. The following private choices are left untouched. -/
theorem placed_packets_iff (bits : Bits.Word) (rows : List Bits.Word) (tail : Bits.Word) :
    splitPackets (packetWidths X t v o,bits) = some (rows,tail) ↔
      ∃ h : Placed t.place X.network.Half v, rows = packets X t v o h ∧ bits = rows.flatten ++ tail := by
  rw [splitPackets_iff]
  constructor
  · rintro ⟨sizes,suffix⟩
    have len : rows.length = o.length := by simpa [packetWidths] using congrArg List.length sizes
    let atRow (j : Fin o.length) := rows[j.val]'(len.symm ▸ j.isLt)
    have width (j : Fin o.length) : (atRow j).length = RefreshHalfDecoder.width X (o.entries j).val := by
      have p := congrArg (fun ws : List Tally => ws[j.val]?) sizes
      have valid : j.val < (rows.map (tally ∘ List.length)).length := by simp [len]
      simp only [packetWidths,List.getElem?_eq_getElem valid,List.getElem_map,Function.comp_apply,
        List.getElem?_ofFn,j.isLt,↓reduceDIte,Option.some.injEq] at p
      simpa only [tally_length] using congrArg List.length p
    choose vals same _ using fun j : Fin o.length =>
      existsUnique_half X (o.entries j).val (atRow j) (width j)
    let h : Placed t.place X.network.Half v := fun u hu =>
      Equiv.piCongrLeft (fun z : t.Preimage v => X.network.Half z.val) o.entries vals ⟨u,hu⟩
    have one (j : Fin o.length) : h _ (o.entries j).prop = vals j := Equiv.piCongrLeft_apply_apply ..
    refine ⟨h,List.ext_getElem (by simpa [packets] using len) ?_,suffix⟩
    intro i hi hj
    let j : Fin o.length := ⟨i,len ▸ hi⟩
    simp only [packets,List.getElem_ofFn]
    exact (same j).symm.trans (congrArg (packed X _) (one j).symm)
  · rintro ⟨h,rfl,suffix⟩
    exact ⟨by simp [packets,packetWidths,List.map_ofFn,Function.comp_def,packed_length,RefreshHalfDecoder.width],suffix⟩

end
end OAI.Computability.MultitapeWeakETH.NativeGrid.ChildScan
