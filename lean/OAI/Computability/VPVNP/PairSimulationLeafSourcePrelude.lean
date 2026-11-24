import OAI.Computability.VPVNP.PairSimulationLeafCacheRead

/-! # Staging the leaf address, full header, and private cache pointer -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafSourceLoad

open BurstRAM PrivateRAM LeafRegisterBank PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {k w r p pubs : ℕ}

/-- Five native instructions initializing the site, header and cache-read registers. -/
def prelude (ports : Source k ↪ Fin r) (site hdr base cursor unit : Fin r)
    (pc : Fin 5 → Fin p) (done : Fin p) : Fin 5 → Instr w p r pubs :=
  ![.copy (ports .address) site (pc 1), .copy (ports .header) hdr (pc 2),
    .constant (ports .initial) 0 (pc 3), .copy cursor base (pc 4), .constant unit 1 done]

theorem prelude_resize (ports : Source k ↪ Fin r) (site hdr base cursor unit : Fin r)
    (pc : Fin 5 → Fin p) (done : Fin p) (i : Fin 5) :
    (prelude (w := 1) (pubs := pubs) ports site hdr base cursor unit pc done i).resize w =
      prelude ports site hdr base cursor unit pc done i := by fin_cases i <;> rfl

/-- Register disjointness needed to read each input before it can be overwritten. -/
structure Wiring (ports : Source k ↪ Fin r) (hdr base cursor unit : Fin r) : Prop where
  header : hdr ≠ ports .address
  baseAddress : base ≠ ports .address
  baseHeader : base ≠ ports .header
  baseInitial : base ≠ ports .initial
  cursor_disjoint : ∀ j, cursor ≠ ports j
  unit_disjoint : ∀ j, unit ≠ ports j
  different : cursor ≠ unit

/-- Register file after the five scalar-reader initialization instructions. -/
def prepBank (ports : Source k ↪ Fin r) (site hdr base cursor unit : Fin r) (bank : Fin r → Word w) :=
  Function.update (Function.update (Function.update (Function.update (Function.update bank
    (ports .address) (bank site)) (ports .header) (bank hdr)) (ports .initial) 0) cursor (bank base)) unit 1

theorem prep_run (M : Machine w p r pubs) (ports : Source k ↪ Fin r) (site hdr base cursor unit : Fin r)
    (pc : Fin 5 → Fin p) (done : Fin p)
    (link : ∀ i, M.code (pc i) = prelude ports site hdr base cursor unit pc done i)
    (wires : Wiring ports hdr base cursor unit) (c : Config w p r) (entry : c.pc = pc 0) :
    Prefix M c (List.replicate 5 .tick) {c with pc := done, reg := prepBank ports site hdr base cursor unit c.reg} := by
  let a := c.put (pc 1) (ports .address) (c.reg site)
  let b := a.put (pc 2) (ports .header) (c.reg hdr)
  let z := b.put (pc 3) (ports .initial) 0
  let t := z.put (pc 4) cursor (c.reg base)
  have row (i : Fin 5) (s : Config w p r) (he : s.pc = pc i) :
      M.program.step s = (prelude ports site hdr base cursor unit pc done i).run M.publicData s := by
    change (M.code s.pc).run M.publicData s = _
    rw [he,link]
  refine .tick (next := a) ?_ (.tick (next := b) ?_ (.tick (next := z) ?_ (.tick (next := t) ?_ (.tick ?_ (.nil _)))))
  · rw [row 0 c entry]; rfl
  · rw [row 1 a rfl]
    change CallAction.localStep (a.put (pc 2) (ports .header) (a.reg hdr)) = _
    rw [show a.reg hdr = c.reg hdr from Function.update_of_ne wires.header ..]
  · rw [row 2 b rfl]; rfl
  · rw [row 3 z rfl]
    change CallAction.localStep (z.put (pc 4) cursor (z.reg base)) = _
    have he : z.reg base = c.reg base := by
      simp only [z,b,a,Config.put,Function.update_of_ne wires.baseInitial,Function.update_of_ne wires.baseHeader,
        Function.update_of_ne wires.baseAddress]
    rw [he]
  · rw [row 4 t rfl]; rfl

theorem prep_preserve (ports : Source k ↪ Fin r) (site hdr base cursor unit : Fin r) (bank : Fin r → Word w)
    (j : Fin r) (h : ∀ i, j ≠ ports i) (hc : j ≠ cursor) (hu : j ≠ unit) :
    prepBank ports site hdr base cursor unit bank j = bank j := by
  simp only [prepBank,Function.update_of_ne hu,Function.update_of_ne hc,
    Function.update_of_ne (h .initial), Function.update_of_ne (h .header), Function.update_of_ne (h .address)]

end PairSimulation.LeafSourceLoad

end VPVNP
end Computability
end OAI
