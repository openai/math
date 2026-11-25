import OAI.Computability.BorderVNP.TeamSiteTimedInstalled

/-! # The signed coefficient on the actual clocked processor rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP BurstRAM RAMTape UniversalMachine Filter
open TeamContraction TeamContraction.ProcessorSlots TeamTapeHandoff

variable {pc reg k routines m g : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → Macro Q Γ m g) (mark : Fin routines → Γ)

local notation "physical" => machine P lib mark
local notation "body" => code P lib mark
local notation "input" => Layout.input (r := reg) (k := k) (d := (m+1)*g)

/-- One length threshold works for every team, live pin, exterior and interior
assignment, private site data and installed scalar values. The true polynomial
coefficient runs the timed table on the physically constructed input. -/
theorem eventually_wired_value :
    ∀ᶠ n : ℕ in atTop, ∀ {R r w a d link e : ℕ} (S : SiteData R r reg k w a)
      (fit : fitsWith physical reg k r w a R link n e) (u : Fin (R+1)) (j : Fin r)
      (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (int : Wires.Edge r reg w e (w+1) → Bool),
      let G := wiringWith physical P S d link n e fit
      let raw := List.ofFn (G.word pin ext int u j)
      signedCount (G.word pin ext int u j) =
        TeamStack.paths body (negative P) (n^36-TeamClocked.prepSteps 25 n)
          (.site Processor.start) (TrustedClock.installed input raw) := by
  filter_upwards [physical_value P lib mark] with n sized
  intro R r w a d link e S fit u j pin ext int G raw
  let F := G.processorFields u pin ext 0 0 0
  let pad := List.replicate (n-(entryStride physical (w+1) n (prefixCapacity r k reg w n+1+a) R link+
    Wires.innerWidth r reg w e (w+1))) false
  let tail := List.ofFn (G.literal u j) ++ (F.exterior j).flatten ++ F.pins j ++ ownerStream int j ++ pad
  have row := wordEqWith physical P S d link n e fit u j pin ext int 0 0 0
  have eq : raw = programPrefix physical ++ tail := by
    change raw = F.row j ++ ownerStream int j ++ pad at row
    rw [row]
    change ((((programPrefix physical ++ List.ofFn (G.literal u j)) ++ (F.exterior j).flatten) ++ F.pins j)
      ++ ownerStream int j) ++ pad = _
    simp only [tail,List.append_assoc]
  have len : (programPrefix physical ++ tail).length = n := eq ▸ List.length_ofFn
  have value := sized tail len
  rw [← eq] at value
  change signedCount (List.ofFn (G.word pin ext int u j)).get = _ at value
  simpa only [signedCount,List.ofFn_get,List.length_ofFn,List.get_ofFn,Fin.cast_cast,Fin.cast_eq_self] using value

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
