import OAI.Computability.VPVNP.RAMProcessorProbeReader
import OAI.Computability.VPVNP.RAMProcessorProbePayload
import OAI.Computability.VPVNP.RAMProcessorGuardedPayload

/-!
# External-probe stages of the burst processor

Only a complete guessed word enters the register-update and record staging
routine. The successful path consumes exactly that word and preserves the
rest of the private stream. A write consumes no private bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ProbeStages

open BurstRAM

variable {r k w : ℕ} {L : Type}

/-- On a read, resume at the caller's successful label or short-input label. -/
def read (dst addr : Fin r) (next reject : L) : Fragment (Port r k) L :=
  (reader addr).withPayload (readPayload dst addr) next reject

theorem read_run (dst addr : Fin r) (next reject : L) (s : Bank r k) (p a v : Word w) (tail : List Bool)
    (hp : s.isa .persistent = wordBits p) (ha : s.isa (.reg addr) = wordBits a)
    (hs : s.choices = wordBits v ++ tail) :
    (read dst addr next reject).Runs
      (s.value.length+s.tag.length+s.address.length+(s.isa (.reg dst)).length+29*w+13) s.stacks next
      ({s with
        choices := tail, value := wordBits v, tag := wordBits (Fin.ofNat (2^w) 2),
        address := wordBits a, isa := Function.update s.isa (.reg dst) (wordBits v)} : Bank r k).stacks := by
  let staged : Bank r k := {s with choices := tail, value := wordBits v}
  have word := reader_run addr s a v tail ha hs
  have payload := readPayload_run dst addr staged p a v hp ha rfl
  have result := Fragment.withPayload_ok next reject word payload
  dsimp only [staged] at result
  unfold read
  convert result using 1
  omega

theorem read_short (dst addr : Fin r) (next reject : L) (s : Bank r k) (a : Word w)
    (ha : s.isa (.reg addr) = wordBits a) (hs : s.choices.length < w) :
    ∃ out, (read dst addr next reject).Runs (s.value.length+4*s.choices.length+3) s.stacks reject out := by
  obtain ⟨out, run⟩ := reader_short addr s a ha hs
  exact ⟨out, Fragment.withPayload_reject (readPayload dst addr) next reject run⟩

/-- In a normal architectural bank the destination is one word, and the
record fields are empty or left over from a single preceding record. -/
theorem read_work_le (dst : Fin r) (s : Bank r k)
    (hv : s.value.length ≤ w) (ht : s.tag.length ≤ w) (ha : s.address.length ≤ w)
    (hd : (s.isa (.reg dst)).length ≤ w) :
    s.value.length+s.tag.length+s.address.length+(s.isa (.reg dst)).length+29*w+13 ≤ 33*w+13 := by omega

theorem write_work_le (s : Bank r k)
    (hv : s.value.length ≤ w) (ht : s.tag.length ≤ w) (ha : s.address.length ≤ w) :
    s.tag.length+s.address.length+s.value.length+21*w+9 ≤ 24*w+9 := by omega

end RAMTape.ProbeStages

end VPVNP
end Computability
end OAI
