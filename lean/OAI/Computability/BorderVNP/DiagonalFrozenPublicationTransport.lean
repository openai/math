import OAI.Computability.BorderVNP.DiagonalBootedProfilePublication

/-! # Reusing one returned packet at the deployed operand addresses -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots Packing
open Crossing RoutingOutputs CellAddressCircuit CellAddressPhysical

/-- Reindex the actual scan and the emitted routing image along the allocator's
address and clock identities. The witness is the same full profile return. -/
theorem published_pin_at_operands {w d p dim k o : ℕ} {Port σ : Type} [Fintype Port] [Fintype σ]
    {bits : Port → ℕ} (task : SignedTaskArena.Layout) (dir : Directory.Layout) (N : Network dim Port bits)
    (tile : N.Site → Fin task.cube.cells) (edge : N.Edge ↪ Fin task.cube.cables) (port : Port ↪ Fin p)
    (original : Fin dir.entries → N.Site) (live : Fin dir.teams × Fin dir.sites ↪ Port)
    (a : StartupArena) (u : Fin a.teams) (slot : ℕ) (pk : ReferencePacket w d)
    (dataGap : ℕ) (f : BroadcastFrame) (header : List Bool) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (initial : Memory w) (bank : Bank w) (sub : Fin k → Bool) (pinBank : Bank w) (pinRAM : Memory w) (used : ℕ)
    {fs pf : Pins.ProcessorFields (a.operands u slot pk).layout} (physical : HEq pf fs)
    {dest target time charge : ℕ} (atTarget : dest=target) (atCharge : time=charge)
    {ad installed : AdviceLayout} (advice : ad=installed) (values : Fin o → ℕ)
    (paths : ProfilePaths (withStartup pinGeometry) k pub mac bank initial True time dest values
      (BootResidence (F:=pf) a u slot pk f ad pub mac header initial bank))
    (ret : Returns (withStartup pinGeometry) pub mac bank initial)
    (spelling : ret.val.1.flatMap TeamRAM.Event.choices=List.ofFn sub)
    (published : PublishedPin task dir N tile edge port original live a u slot pk dest dataGap f header pf pub mac sub
      pinBank pinRAM ret.val.2.1 ret.val.2.2 used (traceCost ret.val.1))
    {n depth nSites w0 : ℕ} (site : N.Site ↪ Fin nSites)
    (F : Fields nSites task.cube.cables p task.cube.cells depth n w0 σ) (z : σ → Bool)
    (image : Image F (site ∘ original) (port ∘ live ∘ finProdFinEquiv.symm) z dest (readings ret.val.2.2))
    (controls : ∀ j : Fin 37, readings ret.val.2.2
      (controlsBase dest task.cube.cables task.cube.cells dir.entries (dir.teams*dir.sites)+j.val)=task.controls j.val) :
    ∃ r : Returns (withStartup pinGeometry) pub mac bank initial,
      ProfilePaths (withStartup pinGeometry) k pub mac bank initial True charge target values
        (BootResidence (F:=fs) a u slot pk f installed pub mac header initial bank) ∧
      r.val.1.flatMap TeamRAM.Event.choices=List.ofFn sub ∧
      PublishedPin task dir N tile edge port original live a u slot pk target dataGap f header fs pub mac sub
        pinBank pinRAM r.val.2.1 r.val.2.2 used (traceCost r.val.1) ∧
      Image F (site ∘ original) (port ∘ live ∘ finProdFinEquiv.symm) z target (readings r.val.2.2) ∧
      ∀ j : Fin 37, readings r.val.2.2
        (controlsBase target task.cube.cables task.cube.cells dir.entries (dir.teams*dir.sites)+j.val)=task.controls j.val := by
  cases eq_of_heq physical
  subst target charge installed
  exact ⟨ret,paths,spelling,published,image,controls⟩

/-- Reindex the emitted packet on its equal physical machine inputs. The chosen return
retains its event trace, final registers, memory, complete image and all controls. -/
theorem published_pin_at_native_inputs {w d p dim k o : ℕ} {Port σ : Type} [Fintype Port] [Fintype σ]
    {bits : Port → ℕ} (task : SignedTaskArena.Layout) (dir : Directory.Layout) (N : Network dim Port bits)
    (tile : N.Site → Fin task.cube.cells) (edge : N.Edge ↪ Fin task.cube.cables) (port : Port ↪ Fin p)
    (original : Fin dir.entries → N.Site) (live : Fin dir.teams × Fin dir.sites ↪ Port)
    (a : StartupArena) (u : Fin a.teams) (slot : ℕ) (pk : ReferencePacket w d)
    (dataGap : ℕ) (f : BroadcastFrame) (header : List Bool) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (initial : Memory w) (bank : Bank w) (sub : Fin k → Bool) (pinBank : Bank w) (pinRAM : Memory w) (used : ℕ)
    {fs pf : Pins.ProcessorFields (a.operands u slot pk).layout} (physical : HEq pf fs)
    {dest target time charge : ℕ} (atTarget : dest=target) (atCharge : time=charge)
    {ad installed : AdviceLayout} (advice : ad=installed) (values : Fin o → ℕ)
    {rawPub : Arg → Word w} {rawMac : TeamOpcode.Macros w 8} {rawBank : Bank w} {rawInitial : Memory w}
    (atPub : rawPub=pub) (atMac : rawMac=mac) (atRegs : rawBank=bank) (atMem : rawInitial=initial)
    (paths : ProfilePaths (withStartup pinGeometry) k rawPub rawMac rawBank rawInitial True time dest values
      (BootResidence (F:=pf) a u slot pk f ad rawPub rawMac header rawInitial rawBank))
    (ret : Returns (withStartup pinGeometry) rawPub rawMac rawBank rawInitial)
    (spelling : ret.val.1.flatMap TeamRAM.Event.choices=List.ofFn sub)
    (published : PublishedPin task dir N tile edge port original live a u slot pk dest dataGap f header pf rawPub rawMac sub
      pinBank pinRAM ret.val.2.1 ret.val.2.2 used (traceCost ret.val.1))
    {n depth nSites w0 : ℕ} (site : N.Site ↪ Fin nSites)
    (F : Fields nSites task.cube.cables p task.cube.cells depth n w0 σ) (z : σ → Bool)
    (image : Image F (site ∘ original) (port ∘ live ∘ finProdFinEquiv.symm) z dest (readings ret.val.2.2))
    (controls : ∀ j : Fin 37, readings ret.val.2.2
      (controlsBase dest task.cube.cables task.cube.cells dir.entries (dir.teams*dir.sites)+j.val)=task.controls j.val) :
    ∃ r : Returns (withStartup pinGeometry) pub mac bank initial,
      ProfilePaths (withStartup pinGeometry) k pub mac bank initial True charge target values
        (BootResidence (F:=fs) a u slot pk f installed pub mac header initial bank) ∧
      r.val.1.flatMap TeamRAM.Event.choices=List.ofFn sub ∧
      PublishedPin task dir N tile edge port original live a u slot pk target dataGap f header fs pub mac sub
        pinBank pinRAM r.val.2.1 r.val.2.2 used (traceCost r.val.1) ∧
      Image F (site ∘ original) (port ∘ live ∘ finProdFinEquiv.symm) z target (readings r.val.2.2) ∧
      ∀ j : Fin 37, readings r.val.2.2
        (controlsBase target task.cube.cables task.cube.cells dir.entries (dir.teams*dir.sites)+j.val)=task.controls j.val := by
  subst rawPub rawMac rawBank rawInitial
  exact published_pin_at_operands task dir N tile edge port original live a u slot pk dataGap f header pub mac
    initial bank sub pinBank pinRAM used physical atTarget atCharge advice values paths ret spelling published site F z image controls

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
