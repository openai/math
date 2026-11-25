import OAI.Computability.BorderVNP.DiagonalSignedWriterReceipt
import OAI.Computability.BorderVNP.FiniteEvaluatorSharedCubeSource

/-! # The signed finite-field operands at the selected header writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube Physical Tally TeamContraction JointHeader
open PackedHistoryCircuit Packing Packing.Directory LocalRow Transmission

variable {w R X : ℕ} (task : SignedTaskArena.Layout)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w} {m : Memory w}
    {D : Packing.Directory.Layout} {pp lp refP refL : ℕ → ℕ × ℕ} {pins : Pins.Layout}
    {slotted : Memory w} {base : ℕ} {I : Type*} [Fintype I] {host : I → Fin task.cube.cells}
    {id : I ↪ ℕ} {width : I → ℕ}
    (P : SlottedWriter task.cube D pp lp pins pub slotted base host id width)
    (f : BroadcastFrame) (old : Fin 81 → Word w) (origin edges cells raw subtotal fresh gates outputs bits off ell controls : ℕ)
    (profile : List Bool) (claims : List (List Bool)) (pad : ℕ)
    (word : Broadcast task.cube.n task.cube.header.d task.cube.header.cap)
local notation3 (prettyPrint := false) "prev" =>
  routingExtension (task.extension raw f.team subtotal old) D origin edges cells
local notation3 (prettyPrint := false) "idx" => readCode (task.cube.n+1) word.1
local notation3 (prettyPrint := false) "axis" => Fin.ofNat (task.cube.n+1) idx
local notation3 (prettyPrint := false) "decl" => Prod.mk axis
  (fun (p : Sym2 (Fin task.cube.header.d)) (j : Fin (task.cube.n+1)) =>
    readCode (task.cube.header.cap+1) (word.2 p j))
local notation3 (prettyPrint := false) "ram" => ISA.publish slotted (pub 0).val base (D.directory pp lp)

include P in
set_option maxHeartbeats 1200000 in
/-- The directory cells and interval scanner at the input of the data writer
are from the very label pass recorded on this exterior. -/
theorem HeaderWriterReceipt.native_entry
    {owner : ℕ → Fin (R+1)} {group : Fin task.cube.header.d → Fin (R+1)}
    (H : HeaderWriterReceipt task.cube D refP refL owner decl group pins f pub mac reg m)
    (published : m=ram)
    (room : PinnedRawInput (ar := task.cube) (D := D) (pp := pp) (lp := lp) (pub := pub)
      (slotted := slotted) (base := base) f prev fresh gates outputs bits off ell controls profile claims pad word R X) :
    NativeEntry task.cube (pub 0).val controls axis R (powerHeaderImage task.cube f.dst (readings H.labeling.val.2.2))
      (readings m) (readings H.history.dataInput) := by
  subst m
  obtain ⟨es,z,m₀,run,_,_,cert,_⟩ :=
    P.raw_schedule f prev fresh gates outputs bits off ell controls mac reg profile claims pad word R X
      room.boot room.geometry room.frameSpace room.copied room.alphabet room.blocks room.bank room.arena
      room.labels room.cells room.teamCount room.teamArena room.budget room.million room.scaled room.controlLow
      room.pointers room.processors room.payload room.fields room.rawSpace room.records
  obtain ⟨_,_,same⟩ := run.unique_of_deterministic (by decide) H.labeling.property
  rw [←same]
  exact ((cert.sound H.history.prefixRun).2).1

include P in
set_option maxHeartbeats 1800000 in
/-- For the writer that actually ran at this header, recover the symbols,
scanner words, lookup pointers, and field constants on its own shared-input
RAM. Its common record length includes all the reference directory's slots. -/
theorem HeaderWriterReceipt.shared_cube_words
    {owner : ℕ → Fin (R+1)} {group : Fin task.cube.header.d → Fin (R+1)}
    (H : HeaderWriterReceipt task.cube D refP refL owner decl group pins f pub mac reg m)
    (published : m=ram)
    (room : PinnedRawInput (ar := task.cube) (D := D) (pp := pp) (lp := lp) (pub := pub)
      (slotted := slotted) (base := base) f prev fresh gates outputs bits off ell controls profile claims pad word R X)
    (range : declarationInRange word) (axes : task.cube.header.a=task.cube.n+1)
    (space : task.after.packed ≤ 2^w) {src : ℕ → ℕ} (selected : src=readings H.history.sharedInput) :
    SharedCubeWords task decl group f.team (readings pub) src (D.directory refP refL).length := by
  subst m
  rw [selected]
  obtain ⟨es,z,m₀,run,_,_,cert,_⟩ :=
    P.raw_schedule f prev fresh gates outputs bits off ell controls mac reg profile claims pad word R X
      room.boot room.geometry room.frameSpace room.copied room.alphabet room.blocks room.bank room.arena
      room.labels room.cells room.teamCount room.teamArena room.budget room.million room.scaled room.controlLow
      room.pointers room.processors room.payload room.fields room.rawSpace room.records
  obtain ⟨_,_,same⟩ := run.unique_of_deterministic (by decide) H.labeling.property
  have coordinate : (axis).val=idx := Nat.mod_eq_of_lt range.1
  have ownerMap :
      (fun j : Fin task.cube.header.d => TeamNative.owner R
        ((weightLayout task.cube (pub 0).val idx).weight (powerHeaderImage task.cube f.dst (readings m₀))) j.val)=group := by
    funext j
    rw [same]
    simpa only [coordinate] using H.groups j
  rw [ownerMap] at cert
  exact H.history.shared_cube_words task old D origin edges cells raw f.team subtotal fresh profile.length gates outputs
    bits off ell decl group H.done room.boot space room.frameSpace axes controls f.team _ cert

/-- The three scalar operands used by the private report setup are read from
the signed hardware packet by this same returned directory. -/
theorem HeaderWriterReceipt.report_input_words
    {owner : ℕ → Fin (R+1)} {group : Fin task.cube.header.d → Fin (R+1)}
    (H : HeaderWriterReceipt task.cube D refP refL owner decl group pins f pub mac reg m)
    (published : m=ram)
    (room : PinnedRawInput (ar := task.cube) (D := D) (pp := pp) (lp := lp) (pub := pub)
      (slotted := slotted) (base := base) f prev fresh gates outputs bits off ell controls profile claims pad word R X)
    (descriptors : task.after.descriptors<2^w) (parameters : task.p.parameters<2^w) :
    readings H.history.dataInput ((pub 0).val+44)=task.after.descriptors ∧
      readings H.history.dataInput ((pub 0).val+81)=task.cube.stop ∧
      readings H.history.dataInput ((pub 0).val+95)=task.p.parameters := by
  subst m
  have scalar (i : Fin 81) := congrArg Fin.val
    ((H.done.low ((pub 0).val+31+i.val) (by have := room.frameSpace; omega)).trans (room.boot.extension i))
  have d := scalar 13
  have z := scalar 50
  have p := scalar 64
  change _ = task.after.descriptors % 2^w at d
  change _ = task.cube.stop % 2^w at z
  change _ = task.p.parameters % 2^w at p
  refine ⟨d.trans (Nat.mod_eq_of_lt descriptors),?_,p.trans (Nat.mod_eq_of_lt parameters)⟩
  exact z.trans (Nat.mod_eq_of_lt room.arena)

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
