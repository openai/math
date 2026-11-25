import OAI.Computability.NearSquareRoot.PhysicalWalshGrid
import OAI.Computability.NearSquareRoot.PhysicalWalshRelease

/-! # Framing a physical packing pass, window sweep, and unpacking pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow
open IntegerMultiplication Code Space PhysicalWalshGrid

def framePack (z : (Tree × Tree × Tree) × Tree) := ((z.1.1,z.2),z.1.2)
def frameGate (z : Tree × Tree × Tree) := ((z.2.1,z.1),z.2.2)
def frameUnpack (z : Tree × Tree) := (z.2,z.1)

theorem easy_framePack : Easy framePack :=
  ((Easy.fst.compose Easy.fst).pair Easy.snd).pair (Easy.fst.compose Easy.snd)

theorem easy_frameGate : Easy frameGate :=
  ((Easy.snd.compose Easy.fst).pair Easy.fst).pair (Easy.snd.compose Easy.snd)

theorem easy_frameUnpack : Easy frameUnpack := Easy.snd.pair Easy.fst

noncomputable def framePackCmd : Cmd := easy_framePack.choose
noncomputable def frameGateCmd : Cmd := easy_frameGate.choose
noncomputable def frameUnpackCmd : Cmd := easy_frameUnpack.choose

/-- The three input keys are consumed in order. The slow intermediate stage
has a separate time budget; all five transient packets fit in the same arena. -/
theorem threeKeys {I : Type} {time space : I → ℕ} (fits : ∀ i, space i ≤ time i)
    {a h b p x y q : I → Tree}
    (first : BoundedTask space space (fun i => .fork (a i) (p i)) x)
    (middle : BoundedTask time space (fun i => .fork (h i) (x i)) y)
    (last : BoundedTask space space (fun i => .fork (b i) (y i)) q) :
    BoundedTask time space (fun i => .fork (.fork (a i) (.fork (h i) (b i))) (p i)) q := by
  obtain ⟨A,Aa⟩ := first.endpointSize
  obtain ⟨H,Hh⟩ := middle.endpointSize
  obtain ⟨B,Bb⟩ := last.endpointSize
  let K := A+H+B+5
  have parts i := And.intro (Aa i) (And.intro (Hh i) (Bb i))
  simp only [Tree.count,max_le_iff] at parts
  let v (i:I) := ((a i,(h i,b i)),p i)
  have init := easyWithin space (show Easy framePack from ⟨framePackCmd,easy_framePack.choose_spec⟩) v K (fun i => by
    have := parts i; dsimp only [v]; simp only [size_prod]; change _ ≤ (A+H+B+5)*(space i+1)
    simp only [Nat.add_mul,size,send,id_eq]; omega)
  have packed := first.left (fun i => .fork (h i) (b i))
  let v' (i:I) := (x i,(h i,b i))
  have prep := easyWithin space (show Easy frameGate from ⟨frameGateCmd,easy_frameGate.choose_spec⟩) v' K (fun i => by
    have := parts i; dsimp only [v']; simp only [size_prod]; change _ ≤ (A+H+B+5)*(space i+1)
    simp only [Nat.add_mul,size,send,id_eq]; omega)
  have body := middle.left b
  have restore := easyWithin space (show Easy frameUnpack from ⟨frameUnpackCmd,easy_frameUnpack.choose_spec⟩)
    (fun i => (y i,b i)) K (fun i => by
      have := parts i; simp only [size_prod]; change _ ≤ (A+H+B+5)*(space i+1)
      simp only [Nat.add_mul,size,send,id_eq]; omega)
  have full := ((((init.compose packed).compose prep).compose body).compose restore).compose last
  apply full.bound 6 (K+1)
  · intro i
    have := fits i
    change space i + space i + space i + time i + space i + space i + 1 ≤ _
    omega
  · intro i
    have := parts i
    change max (max (max (max (max _ _) _) _) _) _ + 1 ≤ (A+H+B+5+1)*(space i+1)
    simp only [Tree.count,Nat.add_mul]
    omega

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
