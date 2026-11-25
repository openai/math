import OAI.Computability.NearSquareRoot.CommonAlphabetSimulation
import OAI.Computability.NearSquareRoot.CommonAlphabetLoaded

/-!
# Common-alphabet execution of a fixed-tape candidate

A finite source alphabet occupies nonempty blocks over the common physical alphabet
`Option Bool`. All input words are encoded in order and all parts of a source blank
block are physically blank. The simulation uses exactly the original tape indices.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet
open IntegerMultiplication
variable {A Q I : Type}

def loadedConfig {G R : Type} (q : R) (blank : G) (s : I → List G) : TM.Config G R I :=
  ⟨q, fun i => TM.Tape.loaded blank (s i)⟩

/-- One fixed serializer covers every input and every halting execution of the source
machine. From pre-encoded blocks it pays two initial sweeps, then five sweeps and one
dispatch step per transition. Its output is the full sequence of blocks with the
correct physical blanks outside the result, regardless of the terminal head position. -/
theorem serialize_loaded [Finite A] [Finite Q] [Finite I] (m : TM.Rule A Q I) (blank : A) :
    ∃ c : Code A, c.enc blank = (fun _ => none) ∧ Finite (PC A Q I c.width) ∧
    ∀ (q : Q) (s : I → List A) (n cells : ℕ) (y : TM.Config A Q I) (out : I) (z : List A),
       let old := loadedConfig q blank s
       let start := loadedConfig (readStart (I := I) c q) none (fun i => c.encodeList (s i))
       Trace (TM.advance m) old n y → TM.advance m y = none →
       TM.whole blank z (y.tape out) → VisitsAtMost m old n cells →
       ∃ finish, Trace (TM.advance (rule c m)) start (2*c.width+(1+5*c.width)*n) finish ∧
         TM.advance (rule c m) finish = none ∧
         TM.whole none (c.encodeList z) (finish.tape out) ∧
         (∀ i, Represents c (finish.tape i) (y.tape i)) ∧
         VisitsAtMost (rule c m) start (2*c.width+(1+5*c.width)*n)
           ((2*(1+5*c.width)+1)*cells) := by
  obtain ⟨c, hb⟩ := exists_code blank
  refine ⟨c, hb, inferInstance, fun q s n cells y out z run halt product space => ?_⟩
  let S : PhysicalTapes I := fun i => TM.Tape.loaded none (c.encodeList (s i))
  have aligned (i : I) : Represents c (S i) ((loadedConfig q blank s).tape i) :=
    c.represents_loaded blank hb (s i)
  obtain ⟨R, sim, hR⟩ := simulate c m run S aligned
  refine ⟨boundary c y R, sim, simulate_halt c m halt R,
    c.whole_of_represents blank hb product (hR out), hR, simulate_space c m run space S aligned⟩

end CommonAlphabet

end NearSquareRoot
end Computability
end OAI
