import OAI.ThreeFlat.RAM.TickReadFields
import OAI.ThreeFlat.RAM.TickReadBits

namespace OAI
/-! # Loading both public identifiers of a tick into native word registers -/

namespace ThreeFlat.RAM.TickReadBits

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory Diagonal.ApproximateImage

variable {w p r k d nt ns np a : ℕ}

/-- A location of the fixed two-block bit reader in an enclosing machine. -/
structure Site (p r k : ℕ) where
  setup : Fin 6 → Fin p
  loopPC : Fin 6 → Fin p
  reg : Fin 6 ↪ Fin r
  base : Fin k
  width : Fin k

def Site.Installed (s : Site p r k) (M : Machine w p r k) (exit : Fin p) : Prop :=
  (∀ i, M.code (s.setup i) = header s.setup s.reg (s.loopPC 0) s.base s.width i) ∧
  ∀ i, M.code (s.loopPC i) = loop s.loopPC s.reg exit i

/-- The native code reads one external word for each team bit, then one for
each step bit. Both decoded natural values survive in registers at the exit. -/
theorem advance_identifiers
    (M : Machine w p r k) (T U : Site p r k) (exit : Fin p)
    (hT : T.Installed M (U.setup 0)) (hU : U.Installed M exit)
    (keep : ∀ j, T.reg 2 ≠ U.reg j)
    (D : Fin d → Bool) (params : Fin np → Bool) (oldA newA oldC newC : Fin a → Bool)
    (team step off S : ℕ) (hdr : ℕ → Word w)
    (loc : TickReadFields.HasFields (nt:=nt) (ns:=ns) D params oldA newA oldC newC team step hdr off)
    (bound : off+pinCount d nt ns np a ≤ S)
    (addr : off+d+nt+ns < 2^w) (ft : team < 2^nt) (fs : step < 2^ns)
    (wt : team < 2^w) (ws : step < 2^w)
    (tb : (M.publicData T.base).val = off+d) (tw : (M.publicData T.width).val = nt)
    (ub : (M.publicData U.base).val = off+d+nt) (uw : (M.publicData U.width).val = ns)
    (c : Config w p r) (hc : c.pc = T.setup 0) :
    ∃ out, advance M.program (14+6*(nt+ns)) c (initialMemory S hdr) =
      some (out,initialMemory S hdr) ∧ out.pc = exit ∧ (out.reg (T.reg 2)).val = team ∧
      (out.reg (U.reg 2)).val = step ∧ out.persistent = c.persistent ∧
      out.privateMem = c.privateMem ∧
      ∀ i, (∀ j, i ≠ T.reg j) → (∀ j, i ≠ U.reg j) → out.reg i = c.reg i := by
  obtain ⟨mid,runT,entry,valueT,frameT⟩ := advance_public M T.setup T.loopPC T.reg (U.setup 0)
    T.base T.width hT.1 hT.2 c (initialMemory S hdr) team hc (by rw [tb,tw]; omega)
    (by rwa [tw]) wt (by
      rw [tb,tw]
      exact fun i hi => TickReadFields.team_bit loc bound ⟨i,hi⟩)
  obtain ⟨out,runU,atExit,valueU,frameU⟩ := advance_public M U.setup U.loopPC U.reg exit
    U.base U.width hU.1 hU.2 mid (initialMemory S hdr) step entry (by rwa [ub,uw])
    (by rwa [uw]) ws (by
      rw [ub,uw]
      exact fun i hi => TickReadFields.step_bit loc bound ⟨i,hi⟩)
  rw [tw] at runT
  rw [uw] at runU
  refine ⟨out, ?_, atExit, ?_, valueU, frameU.persistent.trans frameT.persistent,
    frameU.privateMem.trans frameT.privateMem, ?_⟩
  · rw [show 14+6*(nt+ns) = (7+6*nt)+(7+6*ns) by omega]
    exact advance_trans runT runU
  · rw [frameU.registers (T.reg 2) keep]
    exact valueT
  · intro i hi hj
    exact (frameU.registers i hj).trans (frameT.registers i hi)

end ThreeFlat.RAM.TickReadBits

end OAI
