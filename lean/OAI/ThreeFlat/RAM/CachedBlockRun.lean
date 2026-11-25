import OAI.ThreeFlat.RAM.CachedBlockMass
import OAI.ThreeFlat.RAM.CachedBlockLoader

namespace OAI
/-! # Executing an installed block with public operands from live external cells -/

namespace ThreeFlat.RAM.CachedBlock
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
variable {w p r k P R K : ℕ} {F : Type*} [Semiring F]

def lower (loc : Fin k→Word w) (b : Block w p r k) : Block w (2*k+p) (r+k) 0 :=
  CachedBlockLoader.prepend loc (Fin.natAddEmb r) (body b)

/-- Any original continuation lemma may be invoked on the actual source
installation in the numerical-parameter machine. Every source exit becomes
the physical host continuation at the same residual fuel. -/
theorem mass_at_exit (b : Block w p r k) (M : Machine w P R K) (reg : Fin (r+k) ↪ Fin R)
    (exit : Fin P) (values : Fin k→Word w) (field : FieldCode F w) (fuel : ℕ)
    (z : Config w (p+P) R) (m : Memory w) (arrived : z.pc=Fin.natAdd p exit) :
    mass field (shadow b M reg exit values).program fuel z m=
      mass field M.program fuel (atPC exit z) m := by
  have same : liftPC (Fin.natAdd p) (atPC exit z)=z := by
    cases z with
    | mk pc s vals pm =>
      change pc=Fin.natAdd p exit at arrived
      subst pc
      rfl
  simpa only [same] using mass_right b M reg exit values field fuel (atPC exit z) m

/-- Loading the header costs two instructions per parameter. The weighted
body has identical residual time on every accept, reject, or choice path.
All registers outside the cache and the two forms of private state retain
their prior values on entry to the body. -/
theorem run_mass (b : Block w p r k) (nat : Natural b) (loc : Fin k→Word w)
    (M : Machine w P R K) (pc : Fin (2*k+p) ↪ Fin P) (reg : Fin (r+k) ↪ Fin R)
    (pub : Fin 0→Fin K) (exit : Fin P) (ins : (lower loc b).Installed M pc reg pub exit)
    (field : FieldCode F w) (fuel : ℕ) (c : Config w P R) (m : Memory w)
    (start : c.pc=pc (lower loc b).first) :
    ∃ z,advance M.program (2*k) c m=some (z,m) ∧
      z.pc=pc (CachedBlockLoader.bodyPc k p b.first) ∧
      Cached reg (fun j => m (loc j).val) z ∧
      (∀ a,(∀ j,a≠reg (Fin.natAdd r j)) → z.reg a=c.reg a) ∧
      z.persistent=c.persistent ∧ z.privateMem=c.privateMem ∧
      mass field M.program (fuel+2*k) c m=
        mass field (shadow b M reg exit (fun j => m (loc j).val)).program fuel (atPC (b.first.castAdd P) z) m := by
  obtain ⟨z,go,enter,cache,same,st,pm⟩ := CachedBlockLoader.advance loc (Fin.natAddEmb r) (body b)
    M pc reg pub exit ins c m start
  have rom := CachedBlockLoader.body_installed loc (Fin.natAddEmb r) (body b) M pc reg pub exit ins
  refine ⟨z,go,enter,cache,same,st,pm,(mass_of_advance field M.program go fuel).trans ?_⟩
  exact (mass_body b nat M _ reg pub exit rom _ field fuel b.first z m enter cache).symm

end ThreeFlat.RAM.CachedBlock

end OAI
