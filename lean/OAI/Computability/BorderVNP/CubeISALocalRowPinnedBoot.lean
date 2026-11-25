import OAI.Computability.BorderVNP.CubeISALocalRowPublicBoot
import OAI.Computability.BorderVNP.CubeISALocalRowDecoderRoom
import OAI.Computability.BorderVNP.RoutingISACubeArenaFields
import OAI.Computability.BorderVNP.PackedRoutingChooserHeader

/-! # Resident cube pins and copied declaration through public placement

The private placement changes slots and counters. Publishing the delivery rows also
changes primary word nine. The team identifier, broadcast pointer, extended frame,
and physical copy of the common header survive these writes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally
open CubeHeaderInstall TeamContraction.JointHeader TeamContraction.ProcessorSlots
open PackedHistoryCircuit

/-- Physical words needed from the original pin loader and common broadcast. -/
structure BootPins {w : ℕ} (pub : Arg → Word w) (f : BroadcastFrame)
    (ext : Fin 81 → Word w) (bits : List Bool) (m : Memory w) : Prop where
  /-- The executing team's identifier. -/
  team : frameField (readings pub) (readings m) 0 = f.team
  /-- The common number of physical teams, used by group assignment. -/
  teams : frameField (readings pub) (readings m) 1 = f.teams
  /-- Address of the common broadcast copy. -/
  saved : frameField (readings pub) (readings m) 25 = f.dst
  /-- All extended words, with their original unsigned spelling. -/
  extension : ∀ j : Fin 81, m ((pub 0).val+31+j.val) = ext j
  /-- Every bit of the actual common header. -/
  copy : FlatAt m f.dst bits

variable {w : ℕ} {pub : Arg → Word w} {f : BroadcastFrame} {ext : Fin 81 → Word w}
variable {bits : List Bool} {m : Memory w}

/-- The real branch input already contains the chosen pins and common copy. -/
theorem BootPins.ofProfile {D : ℕ} {L : Pins.Layout} {F : Pins.ProcessorFields L}
    {A : AdviceLayout} {rp : ReferencePacket w D} (p : ProfileOperands F f A rp pub bits m)
    (pins : rp.extension = ext) : BootPins pub f ext bits m :=
  ⟨p.frame.broadcast.1,p.frame.broadcast.2.1,p.frame.broadcast.2.2.2.2.2.2,fun j => (p.extension j).trans (congrFun pins j),p.header⟩

/-- The original boot state can be transported across writes outside its actual reads. -/
theorem BootPins.congr {m' : Memory w} (pins : BootPins pub f ext bits m)
    (fields : ∀ k ∈ [0,1,25], m' ((pub 0).val+k) = m ((pub 0).val+k))
    (extended : ∀ j : Fin 81, m' ((pub 0).val+31+j.val) = m ((pub 0).val+31+j.val))
    (copied : ∀ j : Fin bits.length, m' (f.dst+j.val) = m (f.dst+j.val)) : BootPins pub f ext bits m' :=
  ⟨(congrArg Fin.val (fields 0 (by simp))).trans pins.team,
    (congrArg Fin.val (fields 1 (by simp))).trans pins.teams,
    (congrArg Fin.val (fields 25 (by simp))).trans pins.saved,
    fun j => (extended j).trans (pins.extension j),fun j => (copied j).trans (pins.copy j)⟩

/-- Transport through a pass writing only above a common cutoff. -/
theorem BootPins.below {m' : Memory w} (pins : BootPins pub f ext bits m) {limit : ℕ}
    (frame : (pub 0).val+112 ≤ limit) (stream : f.dst+bits.length ≤ limit)
    (keep : ∀ a < limit, readings m' a = readings m a) : BootPins pub f ext bits m' := by
  apply pins.congr
  · intro k hk
    simp at hk
    exact Fin.ext (keep _ (by omega))
  · intro j
    exact Fin.ext (keep _ (by have := j.isLt; omega))
  · intro j
    exact Fin.ext (keep _ (by have := j.isLt; omega))

/-- The successful guarded geometry interpreter preserves the full pin vector and copied bits. -/
theorem BootPins.geometry {o fresh dest clock : ℕ} {output : Fin o → ℕ} {bank after : Bank w}
    {trace : List (TeamRAM.Event w)} {mac : TeamOpcode.Macros w 8} {result : Memory w}
    (pins : BootPins pub f ext bits m) (run : GeometryReturn pub mac bank m fresh dest clock output trace after result)
    (frame : (pub 0).val+112 ≤ fresh) (stream : f.dst+bits.length ≤ fresh) : BootPins pub f ext bits result :=
  pins.below frame stream fun a h => congrArg Fin.val (run.preserved a h)

/-- Private-slot placement and the compacting delivery writer preserve the joint boot
operands, including the common-header bits beyond the primary frame. -/
theorem BootPins.placedDirectory {m' : Memory w} (pins : BootPins pub f ext bits m)
    (origin cableCount cells entries desc gap deliveries : ℕ) (rows : List Packing.Directory.Row)
    (place : (Packing.RoutingOutputs.privateLayout (pub 0).val origin cableCount cells entries desc gap).Image
      (readings m) entries (readings m'))
    (frame : (pub 0).val+112 ≤ origin) (stream : f.dst+bits.length ≤ origin)
    (before : (pub 0).val+112 ≤ deliveries) (copied : f.dst+bits.length ≤ deliveries)
    (apart : (pub 0).val+9 < f.dst ∨ f.dst+bits.length ≤ (pub 0).val+9) :
    BootPins pub f ext bits (Packing.Directory.ISA.publish m' (pub 0).val deliveries rows) := by
  have low (a : ℕ) (h : a < origin) : readings m' a = readings m a :=
    Packing.RoutingOutputs.private_before_ends place a (by dsimp [Packing.RoutingOutputs.bases]; omega)
  have prev := pins.below frame stream low
  apply prev.congr
  · intro k hk
    simp at hk
    exact Packing.CableTriples.published_outside m' _ _ _ _ (by omega) (.inl (by omega))
  · intro j
    exact Packing.CableTriples.published_outside m' _ _ _ _ (by omega) (.inl (by have := j.isLt; omega))
  · intro j
    have := j.isLt
    exact Packing.CableTriples.published_outside m' _ _ _ _ (by omega) (.inl (by omega))

/-- Decode any native arena operand from its actual joint extension. Geometry and the
secondary-header bootstrap override disjoint fields in the same 81-word literal. -/
theorem BootPins.arenaOperand (a : CubeArena.Layout) (old : Fin 81 → Word w)
    (fresh profile gates outputs width off ell : ℕ)
    (pins : BootPins pub f (jointFields (a.extension old) fresh profile gates outputs width off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) bits m)
    {k value : ℕ} (field : a.operand k = some value) (fit : value < 2^w) :
    frameField (readings pub) (readings m) k = value := by
  have clean : 31 ≤ k ∧ k ≤ 111 ∧ k ∉ [96,97,98,99,100,101,104,105,106,107,108] ∧
      k ∉ [59,60,61,63,109,110,111] := by
    unfold CubeArena.Layout.operand at field
    split at field <;> simp_all
  let j : Fin 81 := ⟨k-31,by omega⟩
  have shift : j.val+31 = k := by dsimp [j]; omega
  have addr : (pub 0).val+31+j.val = (pub 0).val+k := by omega
  have h := pins.extension j
  unfold jointFields at h
  rw [GeometryAdvice.Allocation.fields_other _ _ _ _ _ _ _ _ j (shift ▸ clean.2.2.1),
      pinFields_other _ _ _ _ _ _ _ _ j (shift ▸ clean.2.2.2),addr] at h
  have lit : (a.extension old j).val = value := by
    simp only [CubeArena.Layout.extension,Nat.add_comm 31 j.val,shift,field,Option.elim_some]
    exact Nat.mod_eq_of_lt fit
  exact (congrArg Fin.val h).trans lit


/-- The team budget scalar in primary word 31 comes from the original reference
packet. All three overlays preserve that first extension word. -/
theorem BootPins.budgetWord (a : CubeArena.Layout) (old : Fin 81 → Word w)
    (fresh profile gates outputs width off ell : ℕ)
    (pins : BootPins pub f (jointFields (a.extension old) fresh profile gates outputs width off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) bits m) :
    frameField (readings pub) (readings m) 31 = (old 0).val := by
  have resident := pins.extension 0
  unfold jointFields at resident
  rw [GeometryAdvice.Allocation.fields_other _ _ _ _ _ _ _ _ 0 (by decide),
    pinFields_other _ _ _ _ _ _ _ _ 0 (by decide),a.extension_other old 0 rfl] at resident
  exact congrArg Fin.val resident

/-- All resident fields and the copied stream below the header survive native power
installation, the secondary header stores, compact decoding and column totals. -/
theorem BootPins.powerHeader {m' : Memory w} (a : CubeArena.Layout) (pins : BootPins pub f ext bits m)
    (image : readings m' = powerHeaderImage a f.dst (readings m))
    (frame : (pub 0).val+112 ≤ a.header.header) (stream : f.dst+bits.length ≤ a.header.header) :
    BootPins pub f ext bits m' := by
  have ex := arenaExtents a
  have low : a.header.header ≤ a.header.packetBase := by unfold Inputs.packetBase; omega
  have p : a.packetEnd+8+a.h ≤ a.powerBase := ex.2.1
  apply pins.below frame stream
  intro addr haddr
  rw [image]
  unfold powerHeaderImage
  rw [headerImage_outside _ _ _ _ _ _ (.inl haddr)]
  simp [CubePowers.image,show ¬a.powerBase ≤ addr by have := ex.1; omega]

/-- Exact row operands, dense claims, and directional totals resulting from a successful
power-table and declaration run, relative to its actual starting memory. -/
def DecodedRows (a : CubeArena.Layout) (pub : Arg → ℕ) (saved : ℕ)
    (decl : Broadcast a.n a.header.d a.header.cap) (before : ℕ → ℕ) (z : NatState) : Prop :=
  let stat := a.header
  let dyn := stat.decoder saved
  z.mem = powerHeaderImage a saved before ∧ (rowLayout stat a.b a.h a.powerBase).Loaded a.n pub z.mem ∧
    z.mem stat.header = stat.header+13 ∧ z.mem (stat.header+1) = stat.header+13+stat.entries ∧
    z.mem (stat.header+5) = readCode (a.n+1) decl.1 ∧
    CubeLengths.StoredRows z.mem dyn.dense (fun pair j => readCode _ (decl.2 pair j)) ∧
    ∀ j : Fin (a.n+1), z.mem (dyn.totals+j.val) = ∑ pair, readCode _ (decl.2 pair j)

/-- Native clock for the powers, static header, compact decoder and aggregation. -/
def publicBootCost (a : CubeArena.Layout) (saved : ℕ) :=
  (16+5*(a.n+1))+(a.header.cost a.n (selectorWidth a.n a.K a.h)+
    (HeaderDecode.cost (a.header.decoder saved) + HeaderTotals.cost (a.n+1) (a.header.d*a.header.d)))

/-- Binary coordinate and row-field checks on a possibly malformed declaration. -/
def declarationInRange {n d cap : ℕ} (decl : Broadcast n d cap) : Prop :=
  readCode (n+1) decl.1 < n+1 ∧ ∀ pair j, readCode (cap+1) (decl.2 pair j) < cap+1

/-- Recover the public boot's frame and broadcast from the actual overlaid literal,
including the separately allocated power pointer in field 62. -/
theorem publicBoot_pinned (a : CubeArena.Layout) (old : Fin 81 → Word w)
    (fresh gates outputs width off ell : ℕ) (mac : TeamOpcode.Macros w 8) (r : Bank w)
    (G : List Bool) (claims : List (List Bool)) (pad : ℕ) (decl : Broadcast a.n a.header.d a.header.cap) :
    let raw := padded (TeamContraction.JointHeader.spelling (G++DeclarationBits.spelling decl) claims) pad
    let physical := geometryInputs fresh G.length gates outputs width w a.header.d a.n a.header.blocks a.b a.h a.s
    BootPins pub f (jointFields (a.extension old) fresh G.length gates outputs width off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) raw m →
    a.header = physical → (pub 0).val+112 ≤ a.header.header → f.dst+raw.length ≤ a.header.header →
    0 < a.header.d → 0 < a.header.blocks → 0 < bankWidth a.n a.b a.h a.K a.s → a.stop < 2^w →
    TestRun pub mac (publicBoot a.n (selectorWidth a.n a.K a.h)) r m (publicBootCost a f.dst)
      (declarationInRange decl) (DecodedRows a (readings pub) f.dst decl (readings m)) := by
  intro raw physical pins eq frame stream alphabet blocks stride endRoom
  have axes : a.header.a = a.n+1 := congrArg Inputs.a eq
  have prof : a.header.profile = G.length := congrArg Inputs.profile eq
  have fit := staticFits_of_arena a w (pub 0).val frame alphabet stride endRoom
  have room := decoderFits_of_copy a.header w a.n (selectorWidth a.n a.K a.h) (pub 0).val f.dst
    G claims pad decl axes prof stream fit
  obtain ⟨block,labels⟩ := bootScalars_of_arena a w alphabet blocks endRoom
  have sumRoom := columnSum_room a w endRoom
  have geoFit : physical.Fits w a.n (selectorWidth a.n a.K a.h) (pub 0).val := eq ▸ fit
  have plen : G.length ≤ raw.length := by
    simp only [raw,TeamContraction.JointHeader.padded,TeamContraction.JointHeader.spelling,List.length_append,List.length_cons,List.length_replicate]; omega
  have bank : a.header.header < 2^w := by
    have b := fit.bank
    unfold Inputs.packetBase at b
    omega
  obtain ⟨loaded,bc⟩ := resident_inputs pub m (a.extension old) fresh G.length gates outputs width off ell
    a.header.d a.n a.header.blocks a.b a.h a.s pins.extension geoFit (by omega) block
  have powerFit : a.powerBase < 2^w := by have := (arenaExtents a).2.2; omega
  exact publicBoot_run pub mac r m a f.dst G claims pad decl (eq ▸ loaded) axes prof bc
    (pins.arenaOperand a old fresh G.length gates outputs width off ell rfl powerFit)
    pins.saved pins.copy frame stream alphabet endRoom labels fit room sumRoom

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
