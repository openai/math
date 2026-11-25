import OAI.Computability.BorderVNP.RoutingISASignedReaderArena
import OAI.Computability.BorderVNP.TransmissionPacketOperands
import OAI.Computability.BorderVNP.TransmissionJointHeaderBoot

/-! # Ordinary length-only operands of the complete signed evaluator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM TeamContraction.ProcessorSlots TeamContraction.JointHeader

/-- The preselected ordinary words for the seven-word demand and routing
directories, private calls, and physical residue-entry bank. All remaining
ordinary operands are initialized by the existing signed site-data encoder. -/
noncomputable def Layout.ordinary {w : ℕ} (l : Layout) (A : StartupArena)
    (cable plan u v k : ℕ) (old : Arg → Word w) (j : Arg) : Word w :=
  let own := l.bootOperand A.frame j.val
  let value := own.orElse fun _ => match j.val with
    | 7 => some cable | 8 => some l.cube.cables | 9 => some A.next | 10 => some 0
    | 11 => some plan | 12 => some l.cube.cells | 20 => some (l.entry w u v k) | _ => none
  value.elim (old j) (TeamTapeInputEmit.word w)

/-- The ordinary entry source in the actual packet-operand bank is its
length-only absolute address, and all three geometric and call pointers
agree with the genuine allocated output arrays. -/
theorem Layout.ordinary_receipts {w : ℕ} (l : Layout) (A : StartupArena) (B : PacketOperands)
    (cable plan u v k : ℕ) (old : Arg → Word w) :
    let pub := B.bank (l.ordinary A cable plan u v k old)
    pub 7 = TeamTapeInputEmit.word w cable ∧ pub 9=TeamTapeInputEmit.word w A.next ∧
      pub 13=TeamTapeInputEmit.word w l.cube.records ∧ pub 15=TeamTapeInputEmit.word w l.before.limit ∧
      pub 16=TeamTapeInputEmit.word w l.cube.cells ∧ pub 20=TeamTapeInputEmit.word w (l.entry w u v k) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The allocations installed by the two overlays agree on each extended
word outside the report-specific fields. -/
theorem Layout.report_other (l : Layout) (raw team subt : ℕ) (old : ℕ → ℕ) (i : ℕ)
    (other : i ∉ ([33,34,35,36,38,39,40,44,45,46,71,80,89,90,95] : List ℕ)) :
    l.reportFields raw team subt old i = old i := by
  simp only [reportFields,DiagonalTallyAllocation.AfterTasks.frameFields]
  split
  all_goals first | exact (other (by decide)).elim | skip
  split <;> first | exact (other (by decide)).elim | rfl

/-- A report-unclaimed word comes directly from the geometric cube overlay. -/
theorem Layout.extension_cube {w : ℕ} (l : Layout) (raw team subt : ℕ) (old : Fin 81 → Word w)
    (i : Fin 81) (report : 31+i.val ∉ ([33,34,35,36,38,39,40,44,45,46,71,80,89,90,95] : List ℕ)) :
    l.extension raw team subt old i = l.cube.extension old i := by
  let prev : ℕ → ℕ := fun k ↦ (l.cube.extension old ⟨min (k-31) 80,by omega⟩).val
  change TeamTapeInputEmit.word w (l.reportFields raw team subt prev (31+i.val)) = _
  rw [l.report_other raw team subt prev _ report]
  have idx : (⟨min (31+i.val-31) 80,by omega⟩ : Fin 81)=i := by
    apply Fin.ext
    have := i.isLt
    dsimp
    omega
  dsimp only [prev]
  rw [idx]
  exact Fin.ext (by simp [TeamTapeInputEmit.word])

/-- Physical words belonging to the geometry, header, or residue packet
survive both overlays. -/
theorem Layout.extension_other {w : ℕ} (l : Layout) (raw team subt : ℕ) (old : Fin 81 → Word w)
    (i : Fin 81) (cube : l.cube.operand (31+i.val)=none)
    (report : 31+i.val ∉ ([33,34,35,36,38,39,40,44,45,46,71,80,89,90,95] : List ℕ)) :
    l.extension raw team subt old i = old i :=
  (l.extension_cube raw team subt old i report).trans (l.cube.extension_other old i cube)

/-- Every genuine static cube operand surviving the report overlay has the
announced physical value on the installed 81-word startup. -/
theorem Layout.read_cube_operand {w : ℕ} (l : Layout) (raw team subt : ℕ) (old : Fin 81 → Word w)
    (m : ℕ → ℕ) (frame : ℕ)
    (resident : ∀ j : Fin 81,m (frame+31+j.val) = (l.extension raw team subt old j).val)
    {k x : ℕ} (bounds : 31 ≤ k ∧ k ≤ 111) (operand : l.cube.operand k=some x)
    (report : k ∉ ([33,34,35,36,38,39,40,44,45,46,71,80,89,90,95] : List ℕ)) (fit : x<2^w) :
    m (frame+k)=x := by
  let i : Fin 81 := ⟨k-31,by omega⟩
  have eq : 31+i.val=k := by dsimp [i]; omega
  have hr := resident i
  rw [Nat.add_assoc,eq,l.extension_cube raw team subt old i (eq ▸ report)] at hr
  simpa [CubeArena.Layout.extension,eq,operand,TeamTapeInputEmit.word,Nat.mod_eq_of_lt fit] using hr

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
