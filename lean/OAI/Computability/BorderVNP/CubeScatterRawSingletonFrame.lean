import OAI.Computability.BorderVNP.CubeScatterRawFrame
import OAI.Computability.BorderVNP.CubeScatterSingleton
import OAI.Computability.BorderVNP.RoutingISACallInversion

/-! # Write confinement for singleton scatters on arbitrary routed words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA RoutingISA.CellDispatch VPVNP.BurstRAM DiagonalResidueRAM
/-- Inverting a real singleton family scatter gives its exact write interval without
any precondition on the routed source. -/
theorem scatterSingle_raw_outside {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {r : Bank w} {m : Memory w} {es t mt} (bank alphabet len u v : ℕ)
    (ru : readings r 24 = u) (rv : readings r 25 = v) (rl : readings r 21 = len)
    (alphabetAt : readings m ((pub 0).val+56) = alphabet) (bankAt : readings m ((pub 0).val+88) = bank)
    (frameFit : (pub 0).val+88 < 2^w) (keyFit : u*alphabet+v < 2^w)
    (destFit : singleBase bank alphabet len u v+len < 2^w) (run : Runs pub mac scatterSingle r m es t mt) :
    ∀ x, x < singleBase bank alphabet len u v ∨ singleBase bank alphabet len u v+len ≤ x → mt x = m x := by
  obtain ⟨_,r',m',_,_,init,body⟩ := seq_split run
  obtain ⟨_,z,native,_,dst,stop,one,_⟩ := startSingle_run pub mac r m bank alphabet len u v ru rv rl
    alphabetAt bankAt frameFit keyFit destFit
  obtain ⟨_,rfl,rfl⟩ := native.unique_of_deterministic (by decide) init
  obtain ⟨ds,modes,_,_,image⟩ := (singleBody_iff len _ z m one dst stop destFit).mp body
  have size : ds.length = len := by simpa only [List.length_map,List.length_replicate] using congrArg List.length modes
  intro x hx
  rw [image]
  exact (result_frame ds z m _ one dst (size ▸ destFit.le)).2.2.1 x (size ▸ hx)

end Cube.Scatter

end BorderVNP
end Computability
end OAI
