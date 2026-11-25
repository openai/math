import OAI.Optimization.LinearProgramming.BitRAM.Ops

/-! Shared physical request and reply registers for the numerical sign protocol. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM

/-- The public VM owns three application descriptors in addition to its two
message buffer pointers. These raw addresses persist over a native callback. -/
structure PublicPorts {K : Type*} (p send receive raw base : ℕ) (m : Memory K) : Prop where
  query : m.index 43=send
  answer : m.index 47=receive
  count : m.index 51=p
  source : m.index 53=raw
  target : m.index 55=4*base+2

theorem PublicPorts.transfer {K : Type*} {p send receive raw base : ℕ} {m t : Memory K}
    (h : PublicPorts p send receive raw base m)
    (f : ∀ i, i=43 ∨ i=47 ∨ i=51 ∨ i=53 ∨ i=55 → t.index i=m.index i) :
    PublicPorts p send receive raw base t :=
  ⟨(f 43 (by decide)).trans h.query,(f 47 (by decide)).trans h.answer,
    (f 51 (by decide)).trans h.count,(f 53 (by decide)).trans h.source,(f 55 (by decide)).trans h.target⟩

theorem PublicPorts.headers {K : Type*} {p send recv raw base : ℕ} {m t : Memory K}
    (h : PublicPorts p send recv raw base m) (f : BitRAM.StableHeaders m t) :
    PublicPorts p send recv raw base t :=
  h.transfer (fun i hi => f i (by omega) (by omega))

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
