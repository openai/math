import OAI.Hierarchy.GridStructuralHeader
import OAI.Hierarchy.TraceReceiverTemplateMount
import OAI.ThreeFlat.RAM.TickMountedPins
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Reading the authentic verifier template inside the selected receiver tape -/

namespace Hierarchy.TraceReceiverHeaderMount

open ThreeFlat Diagonal Diagonal.PhysicalStage RAM Computability.VPVNP.BurstRAM PrivateRAM
open RAM.PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

def tape (header tail : List Bool) : Fin (header++tail).length → Bool := fun i => (header++tail)[i.val]

variable {F : Type} [Field F] [Fintype F] {w pc regs slots S base d fuel ell : ℕ}
variable (B : Block F) (axes n cap : ℕ) (M : Machine (64*w) pc regs slots)
    (fit : NativeTrace.Fits M S base d fuel) (hF : Fintype.card F ≤ 2^(64*w)) (st : Word (64*w))
    (raw gateBase text : ℕ) (textFit : text ≤ w^2) (self : Fin (w^2) → Bool)
    (index : Word (64*w)) (sel : Fin ell → Bool) (suffix : List Bool)
set_option quotPrecheck false
local notation "W" => 64*w
local notation "G" => TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs slots d
local notation "dir" => GridStructuralHeader.directory (w:=w) B axes n cap
local notation "v" => TraceReceiverTemplate.words M fit hF st (FieldCode.ofCardLe hF) raw gateBase
local notation "args" => GridStructuralHeader.parameters B axes n cap M fit hF st raw gateBase
local notation "head" => GridReceiverHeader.header text textFit self index args sel
local notation "src" => 2+text+W*((dir).length+1)

omit [Field F] in
/-- A receiver consumes exactly its authentic prefix even when its actual
pin vector carries arbitrary assigned coordinates and unused padding. -/
theorem frame_prefix {wordWidth p : ℕ} (header : List Bool) (input : ℕ→Bool)
    (length : header.length≤p) (read : ∀ i : Fin header.length,input i.val=header[i.val])
    (z : ℕ) (low : z<2+header.length) :
    TickMountedPins.memory (w:=wordWidth) (fun j : Fin p=>input j.val) z=
      TickMountedPins.memory (w:=wordWidth) (TraceReceiverHeaderMount.tape header []) z := by
  cases z with
  | zero=>exact (TickMountedPins.memory_constants (w:=wordWidth) _).1.trans (TickMountedPins.memory_constants _).1.symm
  | succ z=>
    cases z with
    | zero=>exact (TickMountedPins.memory_constants (w:=wordWidth) _).2.trans (TickMountedPins.memory_constants _).2.symm
    | succ n=>
      have inside : n<header.length := by omega
      let i : Fin p:=⟨n,inside.trans_le length⟩
      let j : Fin (header++[]).length:=⟨n,by simpa only [List.append_nil] using inside⟩
      rw [show n+1+1=2+i.val by dsimp [i]; omega]
      change TickMountedPins.memory (w:=wordWidth) (fun j : Fin p=>input j.val) (2+i.val)=
        TickMountedPins.memory (TraceReceiverHeaderMount.tape header []) (2+j.val)
      rw [TickMountedPins.memory_at,TickMountedPins.memory_at]
      apply congrArg (BitLayout.bitWord wordWidth)
      change input n=(header++[])[n]'(j.isLt)
      rw [List.getElem_append_left inside]
      exact read ⟨n,inside⟩

/-- After the two-literal header shift, the selected input contains the fixed
verifier operand vector, even when the selector and assigned bits vary. -/
theorem reads (i : Fin (TraceReceiverTemplate.count G)) (j : Fin W) :
    TickMountedPins.memory (w:=W) (TraceReceiverHeaderMount.tape head suffix) (src+W*i.val+j.val) =
      (((v i).val.testBit (W-1-j.val)).toNat : Word W) := by
  let h := Fin.natAdd (dir).length (i.castAdd ((dir).length+HistoryStageBody.Physical.libraryWords B W))
  let b := finProdFinEquiv (h.succ,j)
  have bound : text+b.val < (head).length := by
    rw [GridReceiverHeader.length]
    simp only [GridStructuralHeader.wordCount]
    have := b.isLt
    omega
  let nbit : Fin (head++suffix).length := ⟨text+b.val,by simp only [List.length_append]; omega⟩
  have addr : src+W*i.val+j.val = 2+nbit.val := by
    change _ = 2+(text+(j.val+W*((dir).length+i.val+1)))
    ring
  rw [addr,TickMountedPins.memory_at]
  have hb : TraceReceiverHeaderMount.tape head suffix nbit = (v i).val.testBit (W-1-j.val) := by
    change (head++suffix)[text+b.val]'(nbit.isLt) = _
    rw [List.getElem_append_left bound]
    have arg : args h=v i :=
      GridStructuralHeader.second B axes n cap M fit hF st raw gateBase i
    exact (TraceReceiverTemplate.header_param text textFit self index args sel h j).trans
      (congrArg (fun z : Word W => z.val.testBit (W-1-j.val)) arg)
  rw [hb]
  cases hbit : (v i).val.testBit (W-1-j.val) <;> rfl

/-- The last bit consumed by the packer lies in the actual local pin tape.
The trailing second directory, thresholds, selector and assigned pins are retained. -/
theorem covered : src+W*TraceReceiverTemplate.count G≤2+(head++suffix).length := by
  rw [List.length_append,GridReceiverHeader.length]
  simp only [GridStructuralHeader.wordCount]
  ring_nf
  omega

/-- The same four-parameter packing loop works after native archive replay,
using the scheduler's genuine frame on its preserved lower input prefix. -/
theorem run_after (mem : Memory W) (safe : ℕ)
    (frame : ∀ z,z < safe → mem z=TickMountedPins.memory (w:=W) (TraceReceiverHeaderMount.tape head suffix) z)
    (covered : src+W*TraceReceiverTemplate.count G ≤ safe)
    (apart : gateBase+TraceReceiverTemplate.count G ≤ src ∨ src+W*TraceReceiverTemplate.count G≤gateBase)
    (dstFit : gateBase+TraceReceiverTemplate.count G<2^W) (srcFit : src+W*TraceReceiverTemplate.count G<2^W) :
    (PhysicalInputPhases.packing W src gateBase (TraceReceiverTemplate.count G)).Exec
      mem (TraceReceiverTemplate.image gateBase v mem) (TraceReceiverTemplate.count G*(5*W+6)+6) := by
  intro P R K machine pcMap reg pub exit rom data cfg memory start same
  apply Procedure.Spec.exec (TraceReceiverTemplate.mount v src gateBase apart dstFit srcFit) mem ?_
    machine pcMap reg pub exit rom data cfg memory start same
  intro i j
  have bounded : src+W*i.val+j.val < src+W*TraceReceiverTemplate.count G := by
    calc
      _ < src+W*i.val+W := Nat.add_lt_add_left j.isLt _
      _ = src+W*(i.val+1) := by ring
      _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left W i.isLt) _
  rw [frame _ (bounded.trans_le covered)]
  exact reads B axes n cap M fit hF st raw gateBase text textFit self index sel suffix i j

/-- The ordinary packing procedure decodes the genuine directory-suffixed
machine parameters starting from the actual local pin frame. -/
theorem run (apart : gateBase+TraceReceiverTemplate.count G ≤ src ∨
      src+W*TraceReceiverTemplate.count G ≤ gateBase)
    (dstFit : gateBase+TraceReceiverTemplate.count G < 2^W)
    (srcFit : src+W*TraceReceiverTemplate.count G < 2^W) :
    let beginMem := TickMountedPins.memory (w:=W) (TraceReceiverHeaderMount.tape head suffix)
    (PhysicalInputPhases.packing W src gateBase (TraceReceiverTemplate.count G)).Exec beginMem
      (TraceReceiverTemplate.image gateBase v beginMem) (TraceReceiverTemplate.count G*(5*W+6)+6) := by
  dsimp only
  intro P R K machine pcMap reg pub exit rom data cfg memory start same
  exact Procedure.Spec.exec (TraceReceiverTemplate.mount v src gateBase apart dstFit srcFit) _
    (reads B axes n cap M fit hF st raw gateBase text textFit self index sel suffix)
    machine pcMap reg pub exit rom data cfg memory start same

end
end Hierarchy.TraceReceiverHeaderMount

end OAI
