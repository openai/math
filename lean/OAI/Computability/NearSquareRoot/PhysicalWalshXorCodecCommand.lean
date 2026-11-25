import OAI.Computability.NearSquareRoot.PhysicalWalshXorDusk
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # Fixed physical packing and unpacking commands shared by every Walsh plan -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow
open IntegerMultiplication Code Space EffectiveBoundedTask PhysicalWalshSwapCodec

private structure Packet where
  n : ℕ
  n_pos : 0 < n
  s : ℕ
  s_pos : 0 < s
  w : ℕ
  data : ℕ → Dusk.Grain w

private theorem packTask :
    let V (p:Packet) := (p.n*p.s+1)*(p.w+1)
    BoundedTask V V (fun p => send ((tally p.n,tally (p.s*(2*(p.w+1)))),
      (List.range (p.n*p.s)).map (Dusk.mark ∘ p.data)))
      (fun p => send ((List.range p.n).map (payload p.s p.data))) :=
  packOrdinal Packet.w Packet.s Packet.n Packet.data Packet.n_pos Packet.s_pos

private theorem unpackTask :
    let V (p:Packet) := (p.n*p.s+1)*(p.w+1)
    BoundedTask V V (fun p => send ((tally (p.n*p.s),tally (2*(p.w+1))),
      (List.range p.n).map (payload p.s p.data)))
      (fun p => send ((List.range (p.n*p.s)).map (Dusk.mark ∘ p.data))) :=
  unpackOrdinal Packet.w Packet.s Packet.n Packet.data Packet.n_pos Packet.s_pos

/-- The physical codec does not depend on arity, exponent, or component width. -/
noncomputable def packCmd : Cmd := packTask.choose
noncomputable def unpackCmd : Cmd := unpackTask.choose

variable {I : Type} (n s w : I → ℕ) (x : (i:I) → ℕ → Dusk.Grain (w i))
    (hn : ∀ i, 0 < n i) (hs : ∀ i, 0 < s i)

include hn hs in
theorem packRuns :
    let V i := (n i*s i+1)*(w i+1)
    EffectiveBoundedTask.Runs packCmd V V (fun i => send ((tally (n i),tally (s i*(2*(w i+1)))),
      (List.range (n i*s i)).map (Dusk.mark ∘ x i)))
      (fun i => send ((List.range (n i)).map (payload (s i) (x i)))) := by
  let pick (i:I) : Packet := ⟨n i,hn i,s i,hs i,w i,x i⟩
  exact (show EffectiveBoundedTask.Runs packCmd _ _ _ _ from packTask.choose_spec).on pick

include hn hs in
theorem unpackRuns :
    let V i := (n i*s i+1)*(w i+1)
    EffectiveBoundedTask.Runs unpackCmd V V (fun i => send ((tally (n i*s i),tally (2*(w i+1))),
      (List.range (n i)).map (payload (s i) (x i))))
      (fun i => send ((List.range (n i*s i)).map (Dusk.mark ∘ x i))) := by
  let pick (i:I) : Packet := ⟨n i,hn i,s i,hs i,w i,x i⟩
  exact (show EffectiveBoundedTask.Runs unpackCmd _ _ _ _ from unpackTask.choose_spec).on pick

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
