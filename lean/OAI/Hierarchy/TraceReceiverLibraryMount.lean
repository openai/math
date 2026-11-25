import OAI.Hierarchy.TraceReceiverHeaderMount
import OAI.Hierarchy.TraceDistributionScale
import OAI.Hierarchy.TraceReceiverAge

namespace OAI
/-! # Loading the selected stage codebook from the receiver's structural tape -/

namespace Hierarchy.TraceReceiverLibraryMount
open ThreeFlat Diagonal Diagonal.PhysicalStage RAM Computability.VPVNP.BurstRAM PrivateRAM
open RAM.PhysicalProcedure HistoryStageBody.Physical TraceReceiverHeaderMount Filter TraceAdmission
open scoped Classical Fin.CommRing
noncomputable section

variable {F : Type} [Field F] [Fintype F] {w pc regs slots S base d fuel ell : ℕ}
variable (B : Block F) (axes n cap : ℕ) (M : Machine (64*w) pc regs slots)
    (fit : NativeTrace.Fits M S base d fuel) (hF : Fintype.card F ≤ 2^(64*w)) (st : Word (64*w))
    (raw gateBase text : ℕ) (textFit : text ≤ w^2) (self : Fin (w^2) → Bool)
    (index : Word (64*w)) (sel : Fin ell → Bool) (suffix : List Bool)
set_option quotPrecheck false
local notation "W" => 64*w
local notation "G" => TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs slots d
local notation "dir" => GridStructuralHeader.directory (w:=w) B axes n cap
local notation "cnt" => TraceReceiverTemplate.count G
local notation "lib" => libraryWords B W
local notation "v" => data B W W
local notation "args" => GridStructuralHeader.parameters B axes n cap M fit hF st raw gateBase
local notation "head" => GridReceiverHeader.header text textFit self index args sel
local notation "src" => (2+text+W*((dir).length+1))+W*(cnt+(dir).length)
local notation "dst" => TickWorkspace.base (receiverAge w) 38

/-- The scan's first word follows both archive directories and the verifier template. -/
theorem reads (i : Fin lib) (j : Fin W) :
    TickMountedPins.memory (w:=W) (TraceReceiverHeaderMount.tape head suffix) (src+W*i.val+j.val) =
      (((v i).val.testBit (W-1-j.val)).toNat : Word W) := by
  let h := Fin.natAdd (dir).length (Fin.natAdd cnt (Fin.natAdd (dir).length i))
  let b := finProdFinEquiv (h.succ,j)
  have bound : text+b.val < (head).length := by
    rw [GridReceiverHeader.length]
    simp only [GridStructuralHeader.wordCount]
    have := b.isLt
    omega
  let bit : Fin (head++suffix).length := ⟨text+b.val,by simp only [List.length_append]; omega⟩
  have addr : src+W*i.val+j.val = 2+bit.val := by
    change _=2+(text+(j.val+W*((dir).length+(cnt+((dir).length+i.val))+1)))
    ring
  rw [addr,TickMountedPins.memory_at]
  have read : TraceReceiverHeaderMount.tape head suffix bit=(v i).val.testBit (W-1-j.val) := by
    change (head++suffix)[text+b.val]'(bit.isLt)=_
    rw [List.getElem_append_left bound]
    have arg : args h=v i := GridStructuralHeader.fourth B axes n cap M fit hF st raw gateBase i
    exact (TraceReceiverTemplate.header_param text textFit self index args sel h j).trans
      (congrArg (fun z : Word W=>z.val.testBit (W-1-j.val)) arg)
  rw [read]
  cases hb : (v i).val.testBit (W-1-j.val) <;> rfl

theorem covered : src+W*lib ≤ 2+(head++suffix).length := by
  rw [List.length_append,GridReceiverHeader.length]
  simp only [GridStructuralHeader.wordCount]
  ring_nf
  omega

/-- Decode the S38 word list after replay and verifier setup, preserving every
address outside the actual polynomial-size codebook in its own memory. -/
theorem run_after (m : Memory W) (safe : ℕ)
    (frame : ∀ z,z < safe → m z=TickMountedPins.memory (w:=W) (TraceReceiverHeaderMount.tape head suffix) z)
    (source : src+W*lib ≤ safe) (apart : src+W*lib ≤ dst) (room : dst+lib<2^W) :
    (PhysicalInputPhases.packing W src dst lib).Exec m (TraceReceiverTemplate.image dst v m)
      (lib*(5*W+6)+6) ∧ Mounted B W W dst (TraceReceiverTemplate.image dst v m) ∧
      ∀ z,z<dst ∨ dst+lib≤z → TraceReceiverTemplate.image dst v m z=m z := by
  refine ⟨?_,⟨?_⟩,?_⟩
  · intro P R K machine pcMap reg pub exit rom data cfg memory start same
    apply Procedure.Spec.exec (TraceReceiverTemplate.mount v src dst (Or.inr apart) room (by omega)) m ?_
      machine pcMap reg pub exit rom data cfg memory start same
    intro i j
    have a : src+W*i.val+j.val<src+W*lib := calc
      _ < src+W*i.val+W := Nat.add_lt_add_left j.isLt _
      _ = src+W*(i.val+1) := by ring
      _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left W i.isLt) _
    rw [frame _ (a.trans_le source)]
    exact reads B axes n cap M fit hF st raw gateBase text textFit self index sel suffix i j
  · exact TraceReceiverTemplate.image_at dst v m
  · exact fun z hz=>TraceReceiverTemplate.image_outside dst v m hz

/-- The actual selected input can have arbitrary length and suffix. Replay
and prior verifier setup only need to frame the original local header. -/
theorem run_on_header {p : ℕ} (input : ℕ→Bool) (m : Memory W)
    (headerFits : (head).length≤p) (inputFits : 2+p≤dst)
    (stored : ∀ i : Fin (head).length,input i.val=(head)[i.val])
    (frame : ∀ z,z<2+(head).length → m z=TickMountedPins.memory (w:=W) (fun j : Fin p=>input j.val) z)
    (room : dst+lib<2^W) :
    (PhysicalInputPhases.packing W src dst lib).Exec m (TraceReceiverTemplate.image dst v m)
      (lib*(5*W+6)+6) ∧ Mounted B W W dst (TraceReceiverTemplate.image dst v m) ∧
      ∀ z,z<dst ∨ dst+lib≤z → TraceReceiverTemplate.image dst v m z=m z := by
  have span : src+W*lib≤2+(head).length := by
    simpa only [List.append_nil] using covered B axes n cap M fit hF st raw gateBase text textFit self index sel []
  exact run_after B axes n cap M fit hF st raw gateBase text textFit self index sel [] m (2+(head).length)
    (fun z hz=>(frame z hz).trans (TraceReceiverHeaderMount.frame_prefix (F:=F) (w:=w) (text:=text) (head) input headerFits stored z hz))
    span (by omega) room

/-- At every sufficiently large width the physical static words occupy only S38,
and its last used address fits the receiver's word datatype. -/
theorem sector_room : ∀ᶠ w : ℕ in atTop,
    libraryWords B (64*w)≤TickWorkspace.stride (receiverAge w) ∧
    TickWorkspace.base (receiverAge w) 38+libraryWords B (64*w)<2^(64*w) := by
  filter_upwards [TraceDistribution.polynomial_room (GridStructuralHeader.libraryCoefficient B) 14,
    eventually_receiverAge,eventually_ge_atTop 1] with w poly age large
  let step:=TickWorkspace.stride (receiverAge w)
  have eqn : step=2^(4*(receiverAge w)^10) := by
    dsimp [step,TickWorkspace.stride]
    rw [←pow_mul,Nat.mul_comm ((receiverAge w)^10) 4]
  have low : 2^(w/100) ≤ step := by
    rw [eqn]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have sized : libraryWords B (64*w) ≤ step := (GridStructuralHeader.library_count B).trans (poly.trans low)
  refine ⟨sized,?_⟩
  change 39*step+libraryWords B (64*w)<2^(64*w)
  calc
    _ ≤ 40*step := by omega
    _ < 2^6*step := by
      have : 0 < step := by dsimp [step,TickWorkspace.stride]; positivity
      omega
    _ = 2^(6+4*(receiverAge w)^10) := by rw [eqn,pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- The navigation, selected interval, node, metadata and positive-template
receiver banks all precede the virtual verifier and dictionary sectors. -/
theorem workspace_below : ∀ᶠ w : ℕ in atTop,∀ i : ℕ,i≤63 →
    TickWorkspace.base (receiverAge w) i≤2^(32*w) := by
  filter_upwards [eventually_receiverAge,eventually_ge_atTop 1] with w age large
  intro i hi
  have geom : (2^(receiverAge w)^10)^4=2^((receiverAge w)^10*4) :=
    (pow_mul (2:ℕ) _ _).symm
  change (i+1)*(2^(receiverAge w)^10)^4≤2^(32*w)
  rw [geom]
  calc
    _ ≤ 2^6*(2^((receiverAge w)^10*4)) := Nat.mul_le_mul_right _ (by omega)
    _ = 2^(6+(receiverAge w)^10*4) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- The low selected input precedes S38. Its last codebook word also
precedes the 26J verifier bank at every sufficiently large width. -/
theorem placement : ∀ᶠ w : ℕ in atTop,
    2+2^(16*w)≤TickWorkspace.base (receiverAge w) 38 ∧
    TickWorkspace.base (receiverAge w) 38+libraryWords B (64*w)≤26*(2^(32*w)) := by
  filter_upwards [sector_room B,eventually_receiverAge,eventually_ge_atTop 1] with w size age large
  let step:=TickWorkspace.stride (receiverAge w)
  have eqn : step=2^(4*(receiverAge w)^10) := by
    dsimp [step,TickWorkspace.stride]
    rw [←pow_mul,Nat.mul_comm ((receiverAge w)^10) 4]
  have pos : 0 < step := by dsimp [step,TickWorkspace.stride]; positivity
  have lower : 2^(16*w) ≤ step := by
    rw [eqn]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have higher : 2^6*step≤2^(32*w) := by
    rw [eqn,←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  change 2+2^(16*w)≤39*step ∧ 39*step+libraryWords B (64*w)≤26*2^(32*w)
  have small : libraryWords B (64*w) ≤ step := size.1
  constructor <;> omega

/-- The fourth compact structural block costs only a fixed polynomial in w
on the one-time tick preparation path. -/
theorem work_bound (w : ℕ) : libraryWords B (64*w)*(5*(64*w)+6)+6≤
    (326*GridStructuralHeader.libraryCoefficient B+6)*(w+1)^15 :=
  TraceReceiverTemplate.packing_work_of_count (GridStructuralHeader.library_count (w:=w) B)

theorem eventual_work : ∀ᶠ w : ℕ in atTop,
    libraryWords B (64*w)*(5*(64*w)+6)+6≤2^(w/100) := by
  filter_upwards [TraceDistribution.polynomial_room (326*GridStructuralHeader.libraryCoefficient B+6) 15]
    with w small using (work_bound B w).trans small

end
end Hierarchy.TraceReceiverLibraryMount

end OAI
