import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenReady
import OAI.Computability.BorderVNP.CubeRouteAllTaskControls
import OAI.Computability.BorderVNP.CubeRouteProfileDataFrame

/-! # The signed profile and the native private placement supply the open-suffix frame

The primary team and cell counts are ordinary packet operands. The actual
reference extension supplies the live, bundle, control and cell-bank fields.
The native demand publication preserves these words and the two physical sort
banks while populating its own seven-word directory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA Evaluator Packing RoutingOutputs GeometryAdvice DiagonalResidueRAM
open TeamContraction ProcessorSlots

variable {w d : ℕ}

/-- Recover every frame operand of the two directory writers from a genuine
selected-profile boot return with the pinned scalar bank and signed reference. -/
theorem BootResidence.open_fields (t : SignedTaskArena.Layout) (a : StartupArena) (team : Fin a.teams)
    (slot : ℕ) (p : ReferencePacket w d) (D : Directory.Layout) (other : Arg → Word w) (old : Fin 81 → Word w)
    (origin raw subtotal fresh profile gates outputs width off ell : ℕ)
    (teams : D.teams=a.teams)
    (selected : p.extension = signedProfileExtension t old D origin t.cube.cables t.cube.cells raw team.val
      subtotal fresh profile gates outputs width off ell) {f : BroadcastFrame} {A : AdviceLayout}
    {mac : TeamOpcode.Macros w 8} {bits : List Bool} {bank : Bank w} {initial after : Memory w}
    {k b : ℕ} {g : Fin k → Bool} :
    let B := a.operands team slot p
    let args := core (withDemandBase (t.routeBank a.frame other) a.next) origin t.cube.cables t.cube.cells
    let pub := B.bank args
    let table := bases origin t.cube.cables t.cube.cells D.entries
    let control := controlsBase origin t.cube.cables t.cube.cells D.entries (D.teams*D.sites)
    B.Fits w → ∀ {F : Pins.ProcessorFields B.layout},
      BootResidence (F:=F) a team slot p f A pub mac bits initial bank g after →
      t.OpenRoom a.frame table.ends control table.livePairs (D.teams*D.sites) D.entries (2^b) w →
      t.OpenFields team.val a.frame table.ends control table.livePairs (D.teams*D.sites) D.entries (readings after) := by
  intro B args pub table control fits F path room
  obtain ⟨_,_,_,_,boot,resident⟩ := path
  have fp : (pub 0).val=a.frame := B.frameBase_word args fits
  obtain ⟨ordinary,extended⟩ := resident_frames a team slot p (Pins.extendGuess g) fp boot resident
  rw [fp] at ordinary extended
  have val (i : Fin 31) : readings after (a.frame+i.val)=(pub (Fin.ofNat 32 (i.val+1))).val :=
    congrArg Fin.val (ordinary i)
  have ext (i : Fin 81) : readings after (a.frame+(31+i.val)) =
      (signedProfileExtension t old D origin t.cube.cables t.cube.cells raw team.val subtotal fresh profile
        gates outputs width off ell i).val := by
    rw [←Nat.add_assoc,readings,extended,selected]
  have teamFit : a.teams < 2^w := fits B.layout.teams (by simp [PacketOperands.values])
  have teamBound := team.isLt.trans teamFit
  have ⟨_,host,pre⟩ := t.open_table_order
  have controlFit := room.bundle_fit.controlEnd
  change control+21 < 2^w at controlFit
  have top := room.top
  have post : t.before.start ≤ t.before.limit := by rw [DiagonalTallyAllocation.BeforeTasks.footprint]; omega
  have hdir : t.cube.hostDirectory < 2^w := by omega
  have cells : t.cube.cells < 2^w := by omega
  have sizes := room.markers
  have endSort := room.bundle_fit.rankEnd
  have entries : D.entries < 2^w := by omega
  have offBound : table.ends < 2^w := by dsimp [table,control,controlsBase,bases] at controlFit ⊢; omega
  have liveBound : table.livePairs < 2^w := by dsimp [table,control,controlsBase,bases] at controlFit ⊢; omega
  have liveFit : D.teams*D.sites ≤ control := by dsimp [control,controlsBase,bases]; omega
  have positive : 1 ≤ D.teams := by rw [teams]; have := team.isLt; omega
  have sites : D.sites < 2^w := by
    have h := Nat.mul_le_mul_right D.sites positive
    rw [Nat.one_mul] at h; omega
  have cables : t.cube.cables < 2^w := by dsimp [control,controlsBase,bases] at controlFit; omega
  have proc : readings after a.frame=team.val := by
    have e := val 0
    exact e.trans (Nat.mod_eq_of_lt teamBound)
  have nr : readings after (a.frame+1)=D.teams :=
    (val 1).trans ((Nat.mod_eq_of_lt teamFit).trans teams.symm)
  have c72 := ext 41
  rw [signedProfileExtension_taskWord t old D origin t.cube.cables t.cube.cells raw team.val subtotal fresh profile gates outputs width off ell 41 (by decide)] at c72
  refine ⟨proc,(val 15).trans (Nat.mod_eq_of_lt cells),(ext 35).trans (Nat.mod_eq_of_lt entries),
    c72.trans (signed_hostWord t old raw team.val subtotal hdir),
    (ext 56).trans (Nat.mod_eq_of_lt offBound),(val 7).trans (Nat.mod_eq_of_lt cables),
    (ext 34).trans (Nat.mod_eq_of_lt liveBound),?_,(ext 61).trans (Nat.mod_eq_of_lt (by omega : control < 2^w))⟩
  rw [nr,show readings after (a.frame+67)=D.sites from (ext 36).trans (Nat.mod_eq_of_lt sites)]

/-- Both parts of the emitted literal control vector are read from the same
geometry return, before the private placement and directory stores. -/
theorem profile_open_controlWords {S Z : Type*} [Fintype S] [Fintype Z]
    {s edges n cells e k b J ports o origin : ℕ} (t : SignedTaskArena.Layout)
    (fits : ∀ i : Fin 37, t.controls i.val < 2^b)
    (F : CellAddressCircuit.Fields s edges n cells e k b (S ⊕ Bool)) (hk : k ≤ b)
    (old : Fin J → Fin s) (live : Fin ports → Fin n)
    (rest : VerifierNetwork.Frame (S ⊕ Bool) (GeometryFrameEncoding.Outputs o b))
    (source : VerifierNetwork.Frame Z S) (input : Z → Bool) (width : b ≤ w) (profile : Memory w) :
    let vector := allTaskControls t b fits
    let head := fun i : Fin 28 => vector (i.castAdd 9)
    let tail := fun i : Fin 9 => vector (Fin.natAdd 28 i)
    (∀ i, readings profile (origin+i.val)=ParseBatchSort.value (fun j =>
      (controlEmitter F hk old live (withControls tail rest) source head).eval input (i,j))) →
    ∀ i : Fin 37, readings profile (controlsBase origin edges cells J ports+i.val)=t.controls i.val := by
  intro vector head tail output
  obtain ⟨primary,extra,_⟩ := sparse_argument_controls F hk old live rest source head tail input origin profile width output
  refine Fin.addCases (m:=28) (n:=9) (fun i => primary i) (fun j => ?_)
  have h : readings profile (controlsBase origin edges cells J ports+28+j.val)=t.controls (28+j.val) := extra j
  simpa only [Fin.val_natAdd,Nat.add_assoc] using h

/-- The stable marker certificate and signed directory fields survive the real
private-prefix stores and publication of the demand records before the geometry. -/
theorem open_directory_published {t : SignedTaskArena.Layout} {D : Directory.Layout} {frame origin next gap team b : ℕ}
    {m placed : Memory w} (pp lp : ℕ → ℕ × ℕ)
    (owner : Fin D.entries → Fin t.cube.cells) (header : Fin D.entries → BottomReports.BundleHeader)
    (rect : t.cube.cells+6*D.entries+t.cube.cells ≤ 2^b)
    (place : (privateLayout frame origin t.cube.cables t.cube.cells D.entries D.description gap).Image
      (readings m) D.entries (readings placed))
    (low : frame+112 ≤ next) (reserve : next+7*D.candidates ≤ origin) :
    let control := controlsBase origin t.cube.cables t.cube.cells D.entries (D.teams*D.sites)
    let table := bases origin t.cube.cables t.cube.cells D.entries
    let fields := t.OpenFields team frame table.ends control table.livePairs (D.teams*D.sites) D.entries
    let published := readings (Directory.ISA.publish placed frame next (D.directory pp lp))
    fields (readings m) → (∀ i : Fin 37, readings m (control+i.val)=t.controls i.val) →
      BottomReports.BundleSort.SectionSpec rect owner header (readings m) t.p.bundlePayload → control ≤ t.p.bundlePayload →
      fields published ∧ (∀ i : Fin 37, published (control+i.val)=t.controls i.val) ∧
      BottomReports.BundleSort.SectionSpec rect owner header published t.p.bundlePayload := by
  intro control table fields published frameOk controls sort payload
  have row := Nat.mul_le_mul_left 7 (D.directory_length_le pp lp)
  have geometry (addr : ℕ) (hi : control ≤ addr) : published addr=readings m addr := by
    have eq : addr=control+(addr-control) := by omega
    rw [eq]
    exact congrArg Fin.val (directoryPublished_control (live:=D.teams*D.sites) (D.directory pp lp)
      place low (by omega) (addr-control))
  refine ⟨frameOk.transfer t (fun i hi => ?_),fun i => (geometry _ (Nat.le_add_right ..)).trans (controls i),
    sort.transfer (fun addr lo _ => geometry _ (payload.trans lo))⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  exact congrArg Fin.val (directoryPublished_low (D.directory pp lp) place (by omega) _ (by omega) (by omega))

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
