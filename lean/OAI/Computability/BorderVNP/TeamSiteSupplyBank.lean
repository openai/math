import OAI.Computability.BorderVNP.TeamSiteSupply

/-! # Exact register banks on every processor clock exit

This calculation covers admitted callbacks even when their arithmetic guard or
private address check subsequently fails. On all earlier refusals the complete
physical word bank is restored to its fetch representation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.SupplyRun

open VPVNP BurstRAM RAMTape TeamTapeHandoff

variable {w p r k a : ℕ}

/-- Physical register bank returned by the guarded fetch. -/
abbrev outputBank (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (s : TeamOpcode.State w p r) (c : Window w) :=
  (TeamLocalClock.Loop.result P pub s c.block c.global c.elapsed c.cap).2

private def expected (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (s : TeamOpcode.State w p r) (c : Window w) : TeamLocalClock.Loop.Exit p r a → Stacks (TeamLocalClock.Port r k)
  | .callback _ => (c.charge (opcodeBurst P s).val).callbackBank pub (TeamOpcode.prepare P pub s).2.reg c.first
  | _ => c.bank pub s

private theorem guarded (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (s : TeamOpcode.State w p r) (c : Window w) (q : Word w) (burst : q = opcodeBurst P s) :
    let result := TeamLocalClock.Loop.afterGuard P pub s c.block c.global c.elapsed q c.cap
    result.2 = expected P pub s c result.1 := by
  intro result
  cases h : decision c.block.val c.global.val q.val with
  | handoff | reject => simp [result,TeamLocalClock.Loop.afterGuard,h,expected,Window.bank]
  | execute =>
    simp only [result,TeamLocalClock.Loop.afterGuard,h,expected]
    funext u
    obtain ⟨persist,writes⟩ := prepared_clean P pub s
    cases u with
    | isa j => simp [TeamLocalClock.banks, Window.callbackBank, ISA.configBank,persist,writes]
    | meter j => simp [TeamLocalClock.banks, Window.callbackBank,Window.charge,burst]
    | stamp | copyScratch | maxBurst => rfl

private theorem bank_exit (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (s : TeamOpcode.State w p r) (c : Window w) :
    outputBank P pub s c = expected P pub s c (exit P pub s c) := by
  have burst := kind_burst P s
  cases h : TeamLocalClock.Loop.kind P s.pc with
  | accept | reject => simp [outputBank,exit,TeamLocalClock.Loop.result,h,expected,Window.bank]
  | ordinary =>
    exact (show (TeamLocalClock.Loop.result P pub s c.block c.global c.elapsed c.cap).2 = _ by
      simpa only [outputBank,exit,TeamLocalClock.Loop.result,h] using guarded P pub s c 0 (by simpa only [h] using burst))
  | burst len =>
    by_cases cap : s.reg len ≤ c.cap
    · simpa only [outputBank,exit,TeamLocalClock.Loop.result,h,cap,↓reduceIte] using
        guarded P pub s c (s.reg len) (by simpa only [h] using burst)
    · simp [outputBank,exit,TeamLocalClock.Loop.result,h,cap,expected,Window.bank]

/-- Terminal acceptance, a refused handoff, and pre-instruction rejection each preserve
the complete architectural registers and both countdowns. -/
theorem noncallback_bank (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (s : TeamOpcode.State w p r) (c : Window w)
    (terminal : ∀ out, exit P pub s c ≠ .callback out) :
    outputBank P pub s c = c.bank pub s := by
  rw [bank_exit]
  cases h : exit P pub s c with
  | accepted | reject | handoff => rfl
  | callback out => exact (terminal out h).elim

/-- Every admitted callback sees the prepared architecture, charged clock and exact
first-probe word. No valid-event or positive-sign hypothesis is required. -/
theorem callback_bank (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (s : TeamOpcode.State w p r) (c : Window w) (out : TeamOpcode.Exit p r a)
    (admitted : exit P pub s c = .callback out) :
    outputBank P pub s c = (c.charge (opcodeBurst P s).val).callbackBank pub (TeamOpcode.prepare P pub s).2.reg c.first := by
  rw [bank_exit,admitted]; rfl

end TeamSite.SupplyRun

end BorderVNP
end Computability
end OAI
