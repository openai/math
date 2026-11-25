import OAI.Computability.BorderVNP.RoutingISACompactPacketSeed
import OAI.Computability.BorderVNP.RoutingISASparseCells
import OAI.Computability.BorderVNP.CellDirectoryWire

/-!
# Compiling a genuine typed sparse packet entirely inside its private call

The burst carries a single framed metadata packet and an address-ordered list of
external wire values. The private translator consumes the metadata once, preserving
the external values. Literal preparation and sparse command expansion then execute on
the private stacks; neither instruction stream is supplied on the exterior RAM.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactPacket

open CellMacro CellMacro.Generator CellSparse VPVNP.RAMTape VPVNP.BurstRAM
open RationalHitting.StackLanguage

private def translatorPorts : IO → Port
  | .row => scratch | .env => row | .out => env

private def generatorPorts : IO → Port
  | .row => env | .env => row | .out => out

private theorem translator_inj : Function.Injective translatorPorts := by
  intro x y h; cases x <;> cases y <;> simp_all [translatorPorts,row,env,scratch]
private theorem generator_inj : Function.Injective generatorPorts := by
  intro x y h; cases x <;> cases y <;> simp_all [generatorPorts,row,env,out]

/-- A fixed driver splits the packet from its external bank, invokes the private
translator, seeds the signed bytecode and expands the translated sparse directory. -/
noncomputable def driver (translate : Fragment IO) (d h : ℕ) : Fragment IO :=
  ((Fragment.split row scratch).seq ((translate.mount translatorPorts).seq
    (seed.seq ((generate d h).mount generatorPorts)))).hide

/-- Cost before the physical word decoder, final reversal and signed bytecode interpreter. -/
noncomputable def generationCost (d : ℕ) (metadata external : List Bool) (body : Stmt)
    (translatorCost : ℕ) :=
  2*(7*metadata.length+10) + translatorCost + (5*external.length+2) +
    scanCost (jobs (clocks d) d body [])

/-- The driver supplies the physical external suffix to its translator, which may
restore a sparse encoding to the logical assignment before seeding the bytecode. -/
theorem driver_run_external (translate : Fragment IO) (d h : ℕ) (metadata physical external : List Bool)
    (body : Stmt) (depth : body.FitsDepth d h) {t : ℕ}
    (compiled : translate.Runs t (io metadata physical []) (io [] external (serialized d body))) :
    ∃ cost ≤ generationCost d metadata external body t, (driver translate d h).Runs cost
      (io (codeWord metadata ++ physical) [] [])
      (io [] [] (stream ((CompactMachine.withExternal external body).expand [])).reverse) := by
  let cmds := serialized d body
  let first := bank (codeWord metadata ++ physical) [] [] []
  obtain ⟨a,ha,split⟩ := Fragment.split_run (src := row) (dst := scratch) (by decide)
    first metadata physical rfl rfl
  have mid : Function.update (Function.update first row physical) scratch metadata = bank physical [] [] metadata := by
    funext i; rcases i with (j|u)
    · cases j <;> rfl
    · cases u; rfl
  rw [mid] at split
  have translation : (translate.mount translatorPorts).Runs t
      (bank physical [] [] metadata) (bank external cmds [] []) := by
    apply translate.runs_mount translator_inj compiled
    · intro i; cases i <;> rfl
    · intro i; cases i <;> rfl
    · rintro (i|u) hi
      · cases i with
        | row => exact (hi .env rfl).elim
        | env => exact (hi .out rfl).elim
        | out => rfl
      · cases u; exact (hi .row rfl).elim
  let rev := (stream (external.reverse.map Op.literal)).reverse
  have hs : seed.Runs (5*external.length+2) (bank external cmds [] []) (bank [] cmds rev []) := by
    simpa only [List.append_nil] using seed_run external cmds []
  obtain ⟨b,hb,generated⟩ := generate_run d h body [] rev depth
  have gen : ((generate d h).mount generatorPorts).Runs b (bank [] cmds rev [])
      (bank [] [] ((stream (body.expand [])).reverse ++ rev) []) := by
    apply Fragment.runs_mount _ generator_inj generated
    · intro i; cases i <;> rfl
    · intro i; cases i <;> rfl
    · rintro (i|u) hi
      · cases i with
        | row => rfl
        | env => exact (hi .row rfl).elim
        | out => exact (hi .out rfl).elim
      · rfl
  have target : (stream ((CompactMachine.withExternal external body).expand [])).reverse =
      (stream (body.expand [])).reverse ++ rev := by
    unfold CompactMachine.withExternal
    simp [CompactMachine.expand_push,stream,rev]
  refine ⟨a+(t+((5*external.length+2)+b)),?_,?_⟩
  · unfold generationCost
    omega
  · rw [target]
    exact Fragment.runs_hide (Fragment.runs_seq _ _ split
      (Fragment.runs_seq _ _ translation (Fragment.runs_seq _ _ hs gen)))

/-- The driver preserves every external assignment bit while materializing the true
sparse bytecode on the private output stack. The translator may use its own scratch. -/
theorem driver_run (translate : Fragment IO) (d h : ℕ) (metadata external : List Bool)
    (body : Stmt) (depth : body.FitsDepth d h) {t : ℕ}
    (compiled : translate.Runs t (io metadata external []) (io [] external (serialized d body))) :
    ∃ cost ≤ generationCost d metadata external body t, (driver translate d h).Runs cost
      (io (codeWord metadata ++ external) [] [])
      (io [] [] (stream ((CompactMachine.withExternal external body).expand [])).reverse) :=
  driver_run_external translate d h metadata external external body depth compiled

/-- The finite table installed at slot zero consumes the packed typed packet, runs
the private translator, and counts all internal assignments with their local weights. -/
theorem typed_cell_sum {w n d h : ℕ} (translate : Fragment IO) (D : Directory)
    (k : ℕ) (ext : List Bool) (hw : 0 < w) (depth : (D.program k).FitsDepth d h)
    {t : ℕ} (compiled : translate.Runs t (io (Packet.bits D k) ext [])
      (io [] ext (serialized d (D.program k))))
    (time : let input := Packet.input D k ext
      let ops := (CompactMachine.withExternal ext (D.program k)).expand []
      2*(3*((CompactFrame.pack w input).length*w) + generationCost d (Packet.bits D k) ext (D.program k) t +
        (2*(stream ops).length+1) + budget ops) ≤ n^25) :
    ∑ o ∈ CompactMachine.choices (driver translate d h) n
        (CompactFrame.pack w (Packet.input D k ext)), o.2.value =
      ∑ x : Fin k → Bool, D.weight (lookup (List.ofFn x ++ ext)) := by
  obtain ⟨cost,hc,run⟩ := driver_run translate d h (Packet.bits D k) ext (D.program k) depth compiled
  exact (CompactMachine.sum_choices_packed _ n hw _ _ run (by dsimp only [Packet.input] at time; omega)).trans
    (CompactMachine.value_external_directory ..)

end RoutingISA.CompactPacket

end BorderVNP
end Computability
end OAI
