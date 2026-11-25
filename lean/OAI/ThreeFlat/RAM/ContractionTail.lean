import OAI.ThreeFlat.RAM.ContractionRelocate
import OAI.ThreeFlat.RAM.ContractionStartup

namespace OAI
/-! # Tail entry to the contraction kernel after generating a network -/

namespace ThreeFlat.RAM.ContractionTail

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM BitLayout Contraction

variable {F : Type*} [Fintype F] [Field F] {p w P R K : ℕ}

/-- The caller tail-enters the contraction code with the generated layout in external memory.
The previous computational state and every register may have arbitrary values. -/
theorem mass_eq_network (pc : Fin 35 ↪ Fin P) (reg : Fin 10 ↪ Fin R) (pub : Fin 5 → Fin K)
    (M : Machine w P R K) (N : BitNetwork F p) (fit : Fits N w)
    (hcode : ∀ i, M.code (pc i) = relocate pc reg pub (instruction i))
    (hpub : ∀ i, M.publicData (pub i) = parameters N fit i)
    (c : Config w P R) (hc : c.pc = pc 0) (pin : Fin p → Bool)
    (initialBits : Fin N.internal → Bool) (fuel : ℕ) (tailMem : Memory w := fun _ => 0) :
    mass (codec N fit) M.program (fuel + 9 + 5*N.internal + 22*N.cells)
      c (memoryWithTail tailMem N (codec N fit) pin initialBits) = N.eval pin := by
  rw [mass_eq_eval pc reg pub M (parameters N fit) hcode hpub _ _ c _ 0 hc]
  exact eval_zero_eq_network N fit pin initialBits fuel _ tailMem

/-- Only the generated descriptor prefix needs to agree with the network layout. -/
theorem mass_eq_network_of_prefix (pc : Fin 35 ↪ Fin P) (reg : Fin 10 ↪ Fin R) (pub : Fin 5 → Fin K)
    (M : Machine w P R K) (N : BitNetwork F p) (fit : Fits N w)
    (hcode : ∀ i, M.code (pc i) = relocate pc reg pub (instruction i))
    (hpub : ∀ i, M.publicData (pub i) = parameters N fit i)
    (c : Config w P R) (hc : c.pc = pc 0) (pin : Fin p → Bool)
    (initialBits : Fin N.internal → Bool) (fuel : ℕ) (m : Memory w)
    (hm : ∀ i < footprint N, m i = memory N (codec N fit) pin initialBits i) :
    mass (codec N fit) M.program (fuel + 9 + 5*N.internal + 22*N.cells) c m = N.eval pin := by
  rw [← memoryWithTail_eq_of_prefix N (codec N fit) pin initialBits m hm]
  exact mass_eq_network pc reg pub M N fit hcode hpub c hc pin initialBits fuel
    (fun j => m (footprint N+j))

end ThreeFlat.RAM.ContractionTail

end OAI
