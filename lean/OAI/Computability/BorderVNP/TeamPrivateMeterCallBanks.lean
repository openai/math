import OAI.Computability.BorderVNP.TeamPrivateMeterReset
import OAI.Computability.BorderVNP.TeamPrivateTimeout
import OAI.Computability.BorderVNP.TeamSitePrivate

/-! # Physical banks of a private call with a trusted time budget -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPrivateMeterCall

open VPVNP.RAMTape TeamPrivateTape
variable {Q Γ : Type} {m g : ℕ}

/-- The caller's template, three reset stacks, and the entire private data bank. -/
inductive Port (m g : ℕ) where
  | template | copyScratch | meterRaw | meterScratch
  | native (p : TeamPrivateInput.NativePort (m+1) g)
  deriving DecidableEq, Fintype

/-- The physical data tape is shifted by one position to leave tape zero for the timer. -/
def dataPorts (i : Fin m) (p : TeamPrivateInput.Port g) : Port m g :=
  .native (TeamPrivateInput.ports i.succ p)

/-- The private track bank including the additional clock tape. -/
def trackPort (p : TeamPrivateTape.Port ((m+1)*g)) : Port m g := .native (.inr p)

/-- The reset routine writes the right neighbors of the first tape. -/
def meterPorts : TeamPrivateMeterReset.Port g → Port m g
  | .template => .template
  | .copyScratch => .copyScratch
  | .loader .raw => .meterRaw
  | .loader .scratch => .meterScratch
  | .loader (.lane j) => trackPort (finProdFinEquiv ((0 : Fin (m+1)),j),true)

/-- Independent input loader ports. -/
theorem dataPorts_injective (i : Fin m) : Function.Injective (dataPorts (g := g) i) :=
  fun _ _ h => TeamPrivateInput.ports_injective i.succ (Port.native.inj h)

/-- Independent private tape ports. -/
theorem trackPort_injective : Function.Injective (trackPort (m := m) (g := g)) :=
  fun _ _ h => Sum.inr_injective (Port.native.inj h)

/-- Independent meter reset ports. -/
theorem meterPorts_injective : Function.Injective (meterPorts (m := m) (g := g)) := by
  rintro (_ | _ | (_ | _ | i)) (_ | _ | (_ | _ | j)) h <;> simp_all [meterPorts,trackPort]

/-- Install the call in the processor containing the startup-generated template. -/
def wired (reg k m g : ℕ) : Port m g → TeamClocked.Port (TeamSite.Layout.Port reg k ((m+1)*g))
  | .template => .tally .fuel
  | .copyScratch => .reader .tmp
  | .meterRaw => .reader .input
  | .meterScratch => .reader .size
  | .native p => .user (TeamSite.Layout.site (TeamSite.privateTape p))

/-- Every private port has its own physical stack. -/
theorem wired_injective (reg k m g : ℕ) : Function.Injective (wired reg k m g) := by
  rintro (_ | _ | _ | _ | i) (_ | _ | _ | _ | j) h <;> simp_all [wired]
  exact TeamSite.privateTape_injective (TeamSite.Layout.site_injective h)

/-- Before loading, the true burst and the trusted template are on disjoint stacks. -/
def initial (bs : List Bool) (N : ℕ) : Stacks (Port m g)
  | .template => List.replicate N true
  | .native p => TeamPrivateInput.initial bs p
  | _ => []

/-- Input has been loaded, the timer tape is still blank. -/
def loaded (M : TeamSite.Macro Q Γ m g) (bs : List Bool) (N : ℕ) : Stacks (Port m g)
  | .template => List.replicate N true
  | .native p => TeamPrivateInput.loaded M.alphabet M.digit M.inputTape.succ bs p
  | _ => []

/-- The actual binary tracks of the loaded data and the separate clock tape. -/
def timedInput (M : TeamSite.Macro Q Γ m g) (mark : Γ) (bs : List Bool) (N : ℕ) :=
  tracks M.alphabet (TeamPrivateTimeout.timedTapes M.alphabet.blank mark [] N
    (input M.alphabet.blank M.digit M.inputTape bs))

/-- The physical bank immediately before entering the bounded native simulator. -/
def clocked (M : TeamSite.Macro Q Γ m g) (mark : Γ) (bs : List Bool) (N : ℕ) : Stacks (Port m g)
  | .template => List.replicate N true
  | .native (.inr p) => bank (timedInput M mark bs N) p
  | _ => []

/-- After a return the persistent clock template is ready for the next call. -/
def finished (N : ℕ) : Stacks (Port m g)
  | .template => List.replicate N true
  | _ => []

/-- Initial scanned bits are computed from the first pop of each loader. -/
def timedHeads (M : TeamSite.Macro Q Γ m g) (mark : Γ) (data timer : Option Bool) :
    Fin ((m+1)*g) → Bool := fun i =>
  let (t,j) := finProdFinEquiv.symm i
  Fin.cases (M.alphabet.bits (timer.elim M.alphabet.blank (fun _ => mark)) j)
    (fun v => TeamPrivateInput.headBits M.alphabet M.digit M.inputTape data (finProdFinEquiv (v,j))) t

/-- The two returned loader heads are the actual scanned symbols of the timed machine. -/
theorem timedHeads_eq (M : TeamSite.Macro Q Γ m g) (mark : Γ) (bs : List Bool) (N : ℕ) :
    timedHeads M mark bs.head? (List.replicate N true).head? = heads (timedInput M mark bs N) := by
  funext i
  obtain ⟨⟨t,j⟩,rfl⟩ := finProdFinEquiv.surjective i
  refine Fin.cases ?_ (fun v => ?_) t
  · cases N <;> simp [timedHeads,timedInput,heads,tracks,TeamPrivateTimeout.timedTapes,
      TeamPrivateTimeout.meter,SymbolTape.track,List.replicate_succ]
  · simp [timedHeads,TeamPrivateInput.headBits_eq,heads,timedInput,tracks,TeamPrivateTimeout.timedTapes]

open private loaded_at loaded_outside from OAI.Computability.BorderVNP.TeamPrivateInput

/-- Installing the small loader's terminal image gives the full loaded bank. -/
theorem install_data (M : TeamSite.Macro Q Γ m g) (bs : List Bool) (N : ℕ) :
    installStacks (dataPorts M.inputTape) (initial bs N)
      (TeamPrivateInput.store [] [] (fun j => bs.tail.map (fun b => M.alphabet.bits (M.digit b) j))) =
      loaded M bs N := by
  apply installStacks_frame (dataPorts_injective M.inputTape)
  · exact loaded_at M.alphabet M.digit M.inputTape.succ bs
  · intro p outside
    cases p with
    | native p =>
      exact loaded_outside M.alphabet M.digit M.inputTape.succ bs p
        (fun j h => outside j (congrArg Port.native h))
    | _ => rfl

/-- The clock reset encounters the saved true template and empty private reset scratch. -/
theorem loaded_meter (M : TeamSite.Macro Q Γ m g) (bs : List Bool) (N : ℕ)
    (p : TeamPrivateMeterReset.Port g) :
    loaded M bs N (meterPorts p) = TeamPrivateMeterReset.initial g N p := by
  cases p with
  | template | copyScratch => rfl
  | loader p =>
    cases p with
    | raw | scratch => rfl
    | lane j => simp [loaded,meterPorts,trackPort,TeamPrivateInput.loaded,bank,tracks,input,SymbolTape.track]
                rfl

/-- Installing the restored meter preserves the burst tape and produces the timed bank. -/
theorem install_meter (M : TeamSite.Macro Q Γ m g) (mark : Γ) (bs : List Bool) (N : ℕ) :
    installStacks meterPorts (loaded M bs N) (TeamPrivateMeterReset.filled (M.alphabet.bits mark) N) =
      clocked M mark bs N := by
  apply installStacks_frame meterPorts_injective
  · rintro (_ | _ | (_ | _ | j)) <;> try rfl
    cases N <;> simp [clocked,meterPorts,trackPort,timedInput,bank,tracks,SymbolTape.track,
      TeamPrivateTimeout.timedTapes,TeamPrivateTimeout.meter,TeamPrivateMeterReset.filled]
  · rintro (_ | _ | _ | _ | (b | ⟨i,side⟩)) outside <;> try rfl
    obtain ⟨⟨t,j⟩,rfl⟩ := finProdFinEquiv.surjective i
    revert outside
    refine Fin.cases ?_ (fun v => ?_) t
    · intro outside
      cases side with
      | true => exact (outside (.loader (.lane j)) rfl).elim
      | false => cases N <;> simp [clocked,loaded,TeamPrivateInput.loaded,timedInput,bank,tracks,
          SymbolTape.track,input,TeamPrivateTimeout.timedTapes,TeamPrivateTimeout.meter,Ne.symm (Fin.succ_ne_zero M.inputTape)]
    · intro _
      cases side <;> simp [clocked,loaded,TeamPrivateInput.loaded,timedInput,bank,tracks,
        input,TeamPrivateTimeout.timedTapes]

/-- Cleaning all simulated tracks leaves only the trusted caller template. -/
theorem install_empty (M : TeamSite.Macro Q Γ m g) (mark : Γ) (bs : List Bool) (N : ℕ) :
    installStacks trackPort (clocked M mark bs N) (fun _ => []) = finished N := by
  apply installStacks_frame trackPort_injective
  · intro _; rfl
  rintro (_ | _ | _ | _ | (b | p)) outside <;> try rfl
  exact (outside p rfl).elim

end TeamPrivateMeterCall

end BorderVNP
end Computability
end OAI
