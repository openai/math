import OAI.Computability.BorderVNP.FiniteDiagonalUnitTraceSelected
import OAI.Computability.BorderVNP.PackedHistoryReservedPaths

/-! # The finite-field wide startup reads the actual adaptive pack profile

The finite prefix carries the branch bit, profile and ordinary public declaration. Its
secondary frame is striped across all processors, including a single-processor batch.
The same true pin and geometry program is then run on the populated memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM VerifierNetwork TeamContraction ProcessorSlots Routing RoutingISA RoutingISA.Pins
open RoutingISA.Evaluator JointHeader GeometryAdvice GeometryFrameEncoding PackedHistoryCircuit

/-- All finite-mode declarations are carried in the auxiliary bit bank. The profile is
immediately after the mode bit, and the unused suffix of the full header is zero. -/
def profileHeader {reserve : ℕ} (profile : Fin reserve → Bool) (decl : List Bool) (extra : ℕ) :=
  padded (true :: (List.ofFn profile ++ decl)) extra

private theorem profileHeader_eval {reserve teams : ℕ} (profile : Fin reserve → Bool) (decl : List Bool) (extra : ℕ) :
    profileHeader profile decl extra =
      padded (evaluation (List.ofFn profile++decl) 0 (fun (_ : Fin teams) (i : Fin 0) => i.elim0)) extra := by
  simp [profileHeader,evaluation,spelling,DiagonalTallyRAM.broadcast]

/-- The verified wide boot and branch copy at the exact state on which profile validation
runs. Resident low words include the actual pin assignment for that very path. -/
def CheckedProfileBoot {R r t d link inner n W o : ℕ} {Edge : Type}
    (G : Wiring R r t d link inner n Edge) (u : Fin (R+1)) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (ib hb sb header dst : ℕ) (pub : Arg → Word W) (mac : TeamOpcode.Macros W 8) (bank : Bank W)
    (count : ℕ) (extension : Fin 81 → Word W) (bits : List Bool) (ok : Prop) (clock fresh dest : ℕ) (words : Fin o → ℕ) : Prop :=
  let f := G.transferFrame u header dst
  let loc := G.pinLayout u ib hb sb
  ∃ (snap : BootSnapshot G u pin ext ib hb sb header dst wideStartup pub mac bank)
    (events : List (TeamRAM.Event W)) (ready : Bank W) (saved : Memory W),
    traceCost snap.events ≤ wideStartupBudget W count ∧ Runs pub mac readBroadcast snap.registers snap.mem events ready saved ∧
    traceCost events ≤ f.readTicks ∧ f.Stable (readings ready) ∧ (saved dst).val = 1 ∧
    (∀ i : Fin 31, saved ((pub 0).val+i.val) = pub (Fin.ofNat 32 (i.val+1))) ∧
    (∀ i : Fin 81, saved ((pub 0).val+31+i.val) = extension i) ∧ JointHeader.FlatAt saved dst bits ∧
    ProfilePaths pinGeometry loc.guessWidth pub mac (Function.update ready 10 (saved dst)) saved ok clock dest words
      (fun guess after => ∀ i < fresh, after i = preparedMemory loc (extendGuess guess) saved loc.count i)

section

variable {reserve o b W : ℕ}
variable {R r literal d link inner n : ℕ} {Edge : Type}
variable (G : Wiring R r literal d link inner n Edge) (L : WireLayout (R+1) r link)
variable (t : Table (Fin reserve ⊕ Fin 0) o b)
variable (profile : Fin reserve → Bool) (decl : List Bool) (extra : ℕ)
local notation "bits" => profileHeader profile decl extra
local notation "table" => t
variable (extBits : Exterior R r link → Bool)
variable (u : Fin (R+1)) (pin : Fin d → Bool) (ib hb sb dst : ℕ)
local notation "loc" => G.pinLayout u ib hb sb
local notation "f" => G.transferFrame u L.header dst
local notation "F" => G.processorFields u pin extBits ib hb sb
variable (pub : Arg → Word W) (mac : TeamOpcode.Macros W 8) (bank : Bank W) (A : AdviceLayout)
variable (pre : List (Word W)) (old : Fin 81 → Word W) (fresh off ell : ℕ)
local notation "st" => Allocation.stripe fresh reserve (Table.size table) o b off ell
local notation "extension" => Allocation.fields old fresh reserve (Table.size table) o b off ell
local notation "boot" => FiniteBoot.bootStripe A f (pre.length+81)
local notation "codeBits" => serialized (packet (w := W) fresh (Allocation.packed fresh reserve (Table.size table) o b W) table (profileSources f))
variable (D : Packing.Directory.Layout) (head free : ℕ) (strings : Fin D.entries → Fin D.description → Bool)

set_option maxRecDepth 3500 in
/-- Run the wide boot and common broadcast, then check the actual serialized
geometry table. The result retains all native register, header and low-memory
readbacks, for every returning private pin trace. -/
theorem wide_table_boot (length : (bits).length = L.header)
    (common : ∀ j, (L.exteriorEquiv extBits).broadcast j = headerBits bits length)
    (scalar : PacketFrame loc f A pre.length W (fun _ => 0) (operand pub)) (fit : (f).Fits W (pub 0).val)
    (count : A.count = (pre.length+81)*W) (bootRoom : A.offset+FiniteBoot.width A.count (f).processors ≤ (f).literal)
    (space : ExtendedFrame.Fits W (pub 0).val A.dst pre.length)
    (image : JointImage D head free boot st (serialized (pre++List.ofFn extension)) codeBits strings u.val F)
    (frameEnd : (pub 0).val+112 ≤ dst) (profileEnd : dst+1+reserve ≤ fresh)
    (width : b ≤ W) (positive : 0 < ell) (literalRoom : off+ell ≤ (f).literal)
    (capacity : GeometryOutput.packetCount reserve (table).size o b*W ≤ (f).processors*ell)
    (stop : Allocation.stop fresh reserve (table).size o b W < 2^W)
    (inputClear : PinClear loc 0 (F).header.length) (frameClear : PinClear loc (pub 0).val 112)
    (headerClear : PinClear loc dst (bits).length) (pinWidth : (loc).width ≤ (loc).count) (loopFit : LoopFits W loc) :
    let ok := GeometryOutput.validBit t (Sum.elim profile Fin.elim0)=true
    CheckedProfileBoot G u pin extBits ib hb sb L.header dst pub mac bank A.count extension bits ok
      ((pinSetup.slots+17*(loc).count+1)+GeometryAdviceRate.ticks (table).size reserve o b W) fresh
      (Allocation.dest fresh reserve (table).size o b) (nativeTableWords t profile) := by
  intro ok
  obtain ⟨snap,frame,extAt,coreAt,paid⟩ := wideBootSnapshot_fields G u pin extBits ib hb sb L.header dst pub mac bank A pre extension
    D head free st codeBits strings scalar fit count bootRoom space image
  have hw : 0 < W := by
    have bound : 1 < 2^W := (by omega : 1 ≤ (pub 0).val+112).trans_lt space.frameBound
    by_contra! bad; rw [Nat.eq_zero_of_le_zero bad] at bound; omega
  obtain ⟨events,ready,saved,read,time,stable,copied,values⟩ :=
    JointHeader.native_copy L G u pin extBits bits length common
      ib hb sb dst pub mac snap.registers snap.mem hw snap.input frame.broadcast fit
  have flat := flatAt_of_values hw saved dst bits values
  have mode := values ⟨0,by simp [profileHeader,padded]⟩
  have modeOne : (saved dst).val = 1 := by simpa [profileHeader,padded,NatState.ofWords,readings] using mode
  have keep (i : ℕ) (hi : i < dst) : saved i = snap.mem i := by
    apply Fin.ext
    exact (congrFun copied i).trans ((f).copied_before _ _ _ hi)
  have frameKeep (i : ℕ) (hi : i < 112) : saved ((pub 0).val+i) = snap.mem ((pub 0).val+i) := keep _ (by omega)
  have core (i : Fin 31) : saved ((pub 0).val+i.val) = pub (Fin.ofNat 32 (i.val+1)) :=
    (frameKeep _ (by have := i.isLt; omega)).trans (coreAt i)
  have ext (i : Fin 81) : saved ((pub 0).val+31+i.val) = extension i :=
    (keep _ (by have := i.isLt; omega)).trans (extAt i)
  have seen : (F).ContainsInput saved := by
    have before : (F).header.length ≤ (pub 0).val := by rw [Pins.ProcessorFields.header_length,scalar.input_extent]; exact fit.input
    exact fun a ha => (keep _ (by omega)).trans (snap.input a ha)
  let rp : ReferencePacket W d := ⟨pre,extension,pin⟩
  let claims : Fin (R+1) → Fin 0 → ℕ := fun _ i => i.elim0
  have hp : ProfileOperands F f A rp pub (padded (evaluation (List.ofFn profile++decl) 0 claims) extra) saved := by
    refine ⟨seen,frame.congr (fun i hi => congrArg Fin.val (frameKeep i (by omega))),ext,?_⟩
    exact (profileHeader_eval (teams := R+1) profile decl extra) ▸ flat
  have alloc : ProfileAllocation F f rp pub D head free u.val boot (serialized (pre++List.ofFn extension)) strings table fresh off ell old :=
    ⟨image,rfl,fit,frameEnd,profileEnd,width,positive,literalRoom,capacity,stop⟩
  have headerClear' : PinClear loc dst (padded (evaluation (List.ofFn profile++decl) 0 claims) extra).length :=
    (profileHeader_eval (teams := R+1) profile decl extra) ▸ headerClear
  exact ⟨snap,events,ready,saved,paid,read,time,stable,modeOne,core,ext,flat,
    profile_paths_table t F f A rp pub mac (Function.update ready 10 (saved dst)) saved
      profile decl 0 extra claims hp D head free u.val boot (serialized (pre++List.ofFn extension)) strings
      fresh off ell old alloc inputClear frameClear headerClear' pinWidth loopFit⟩

end

variable {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] {active reserve o b W : ℕ}
variable {R r literal d link inner n : ℕ} {Edge : Type}
variable (G : Wiring R r literal d link inner n Edge) (L : WireLayout (R+1) r link)
variable (history : VerifierNetwork.Frame (X ⊕ Y) (V ⊕ Unit)) (order : Y ≃ Fin active) (fits : active ≤ reserve)
variable (emit : VerifierNetwork.Frame ((X ⊕ Fin reserve) ⊕ V) (Fin o × Fin b)) (x : X → Bool)
variable (profile : Fin reserve → Bool) (decl : List Bool) (extra : ℕ)
local notation "bits" => profileHeader profile decl extra
local notation "table" => geometryTable history order fits emit x
variable (extBits : Exterior R r link → Bool)
variable (u : Fin (R+1)) (pin : Fin d → Bool) (ib hb sb dst : ℕ)
local notation "loc" => G.pinLayout u ib hb sb
local notation "f" => G.transferFrame u L.header dst
local notation "F" => G.processorFields u pin extBits ib hb sb
variable (pub : Arg → Word W) (mac : TeamOpcode.Macros W 8) (bank : Bank W) (A : AdviceLayout)
variable (pre : List (Word W)) (old : Fin 81 → Word W) (fresh off ell : ℕ)
local notation "st" => Allocation.stripe fresh reserve (Table.size table) o b off ell
local notation "extension" => Allocation.fields old fresh reserve (Table.size table) o b off ell
local notation "boot" => FiniteBoot.bootStripe A f (pre.length+81)
local notation "codeBits" => serialized (packet (w := W) fresh (Allocation.packed fresh reserve (Table.size table) o b W) table (profileSources f))
variable (D : Packing.Directory.Layout) (head free : ℕ) (strings : Fin D.entries → Fin D.description → Bool)

set_option maxRecDepth 3500 in
/-- The real wide boot and broadcast expose the canonical public profile at its physical
address and the exact geometry source words, retaining the original processor input. Every
return of the following actual pin and geometry code is characterized on that state. -/
theorem wide_profile_boot (length : (bits).length = L.header)
    (common : ∀ j, (L.exteriorEquiv extBits).broadcast j = headerBits bits length)
    (scalar : PacketFrame loc f A pre.length W (fun _ => 0) (operand pub)) (fit : (f).Fits W (pub 0).val)
    (count : A.count = (pre.length+81)*W) (bootRoom : A.offset+FiniteBoot.width A.count (f).processors ≤ (f).literal)
    (space : ExtendedFrame.Fits W (pub 0).val A.dst pre.length)
    (image : JointImage D head free boot st (serialized (pre++List.ofFn extension)) codeBits strings u.val F)
    (frameEnd : (pub 0).val+112 ≤ dst) (profileEnd : dst+1+reserve ≤ fresh)
    (width : b ≤ W) (positive : 0 < ell) (literalRoom : off+ell ≤ (f).literal)
    (capacity : GeometryOutput.packetCount reserve (table).size o b*W ≤ (f).processors*ell)
    (stop : Allocation.stop fresh reserve (table).size o b W < 2^W)
    (inputClear : PinClear loc 0 (F).header.length) (frameClear : PinClear loc (pub 0).val 112)
    (headerClear : PinClear loc dst (bits).length) (pinWidth : (loc).width ≤ (loc).count) (loopFit : LoopFits W loc) :
    let ok := validProfile order fits (fun q => history.eval (Sum.elim x q) (.inr ()) = true) profile
    CheckedProfileBoot G u pin extBits ib hb sb L.header dst pub mac bank A.count extension bits ok
      ((pinSetup.slots+17*(loc).count+1)+GeometryAdviceRate.ticks (table).size reserve o b W) fresh
      (Allocation.dest fresh reserve (table).size o b) (emittedWords history order fits emit x profile) := by
  intro ok
  obtain ⟨guard,words⟩ := geometry_semantics history order fits emit x profile
  simpa only [guard,words] using wide_table_boot G L table profile decl extra extBits u pin ib hb sb dst pub mac bank A
    pre old fresh off ell D head free strings length common scalar fit count bootRoom space image frameEnd profileEnd
    width positive literalRoom capacity stop inputClear frameClear headerClear pinWidth loopFit

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
