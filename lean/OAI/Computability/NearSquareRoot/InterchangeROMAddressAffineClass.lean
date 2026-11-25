import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineProject
import OAI.Computability.NearSquareRoot.InterchangeROMAffineMask
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelect

/-! # Full affine class masks from two physical field descriptors

The two descriptors need only have equal physical length. At position
`i`, the Boolean is computed from the two independently projected field
words at position `i`. All numerical parameters are supplied as data.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace AffineAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Carry
  IntegerMultiplication.Bits IntegerMultiplication.Strip IntegerMultiplication.Adic
  IntegerMultiplication.Loom IntegerMultiplication.Strip.Dims

open InterchangeAffineMask (inspect inspect_poly)

abbrev Triple := List Tally × List Tally × List Tally

structure Comparison where
  first : Geometry
  second : Geometry
  aligned : first.rows.count = second.rows.count
  scalar : InterchangeAffineMask.Header Word

namespace Comparison

abbrev desc (z : Comparison) := (z.scalar,z.first.desc,z.second.desc)

abbrev heightBound (z : Comparison) := size z.scalar + z.first.bits + z.second.bits + 2

def budget (d : ℕ) (z : Comparison) := size z.desc + z.first.budget + z.second.budget +
  (z.first.rows.count+1) * (z.heightBound + (z.heightBound+1)^d + 2) + 1

noncomputable abbrev address (g : Geometry) {α : Type} (s : Series α)
    (e : s.count = g.rows.count) (x : α) :=
  born ((layout g.field).index (g.rows.follow (Fin.cast e (s.index x))).2.1).val

private theorem aligned_stripe {α : Type} (s : Series α) (g : Geometry) (e : s.count = g.rows.count) :
    stripe s (fun x => send (address g s e x)) = g.result := by
  rw [Geometry.result,stripe_eq',stripe_eq']
  apply congrArg send
  apply List.ext_getElem (by simpa only [Series.card] using e)
  intro n hn hm
  let i : Fin s.count := ⟨n,by simpa only [Series.card] using hn⟩
  rw [s.get _ i,g.rows.get _ (⟨n, by simpa only [Series.card] using hm⟩ : Fin g.rows.count)]
  simp only [address,Series.index_symm,Series.index_follow]
  rfl

noncomputable def query (z : Comparison) (x : Pin z.first.pre × Pin z.first.field × Pin z.first.post) : InterchangeAffineMask.Query :=
  (z.scalar,address z.first z.first.rows rfl x,address z.second z.first.rows z.aligned x)

noncomputable def result (z : Comparison) := stripe z.first.rows fun x => send (inspect (z.query x))

theorem contract : ∃ d, Carries (fun z : Comparison => (budget d z : ℝ)) (fun z => send z.desc) result := by
  obtain ⟨u,⟨d,C,hcost⟩,inspectRun⟩ := inspect_poly
  refine ⟨d,?_⟩
  let w (z : Comparison) : ℝ := budget d z
  let rows (z : Comparison) := z.first.rows
  let cell (z : Comparison) := z.heightBound + (z.heightBound+1)^d + 2
  have big (z : Comparison) : ((rows z).count+1)*cell z ≤ budget d z := by dsimp [budget,cell,rows]; omega
  have pc (z : Comparison) : 1 ≤ cell z := by dsimp [cell]; omega
  have pos (z : Comparison) : 1 ≤ w z := by dsimp only [w]; exact_mod_cast (show 1 ≤ budget d z by unfold budget; omega)
  have vol : Volume w (fun z => send z.desc) := by
    refine ⟨1,fun z => ?_⟩
    simp only [Nat.cast_one,one_mul,w]
    exact_mod_cast (show size z.desc ≤ budget d z by unfold budget; omega)
  have get1 : Easy (fun p : InterchangeAffineMask.Header Word × Triple × Triple => p.2.1) := by fun_prop
  have get2 : Easy (fun p : InterchangeAffineMask.Header Word × Triple × Triple => p.2.2) := by fun_prop
  have first := (Carries.func pos vol _ get1).chain
    ((Geometry.carries.slide Comparison.first).larger (d:=w) (fun z => by
      dsimp only [Function.comp_apply,w]
      exact_mod_cast (show z.first.budget ≤ budget d z by unfold budget; omega)))
  have second := (Carries.func pos vol _ get2).chain
    ((Geometry.carries.slide Comparison.second).larger (d:=w) (fun z => by
      dsimp only [Function.comp_apply,w]
      exact_mod_cast (show z.second.budget ≤ budget d z by unfold budget; omega)))
  let v (z : Comparison) x := address z.first (rows z) rfl x
  let u' (z : Comparison) x := address z.second (rows z) z.aligned x
  have vs : Carries w (fun z => send z.desc) (stackRun rows fun z x => send (v z x)) := by
    convert first using 1
    funext z
    exact aligned_stripe (rows z) z.first rfl
  have us : Carries w (fun z => send z.desc) (stackRun rows fun z x => send (u' z x)) := by
    convert second using 1
    funext z
    exact aligned_stripe (rows z) z.second z.aligned
  have scalar := Carries.func pos vol (Prod.fst : InterchangeAffineMask.Header Word × Triple × Triple → _) Easy.fst
  have base := vs
  change Carries w _ (fun z => stripe (rows z) (fun x => send (v z x))) at base
  simp_rw [stripe_eq'] at base
  have cnt := base.chain (Carries.func base.budget base.out (ruler (X:=Word)) (by fun_prop))
  have re (z : Comparison) : ruler ((rows z).tab (v z)) = tally (rows z).count := by
    simp [ruler,List.map_const',tally]
  simp_rw [re] at cnt
  have copied := spread rows (fun z => send z.scalar) (cnt.twice scalar) (by
    refine ⟨1,fun z => ?_⟩
    simp only [Nat.cast_one,one_mul,w]
    have le : size z.scalar ≤ cell z := by dsimp [cell,heightBound]; omega
    exact_mod_cast (Nat.mul_le_mul_left ((rows z).count+1) le).trans (big z))
  have pairs := coalesce rows _ _ vs us
  have packet := coalesce rows _ _ copied pairs
  let input (z : Σ t : Comparison, Pin t.first.pre × Pin t.first.field × Pin t.first.post) := z.1.query z.2
  have cap z : size (input z) ≤ z.1.heightBound := by
    have h₁ : size (v z.1 z.2) ≤ z.1.first.bits := Geometry.bitSize ..
    have h₂ : size (u' z.1 z.2) ≤ z.1.second.bits := Geometry.bitSize ..
    change size (z.1.scalar, v z.1 z.2, u' z.1 z.2) ≤ z.1.heightBound
    change size z.1.scalar + (size (v z.1 z.2) + size (u' z.1 z.2) + 1) + 1 ≤
      size z.1.scalar + z.1.first.bits + z.1.second.bits + 2
    omega
  have test : Carries (fun z => (cell z.1 : ℝ)) (send ∘ input) (fun z => send (inspect (input z))) := by
    have cov (z : Σ t : Comparison, Pin t.first.pre × Pin t.first.field × Pin t.first.post) :
        (1 : ℝ) ≤ cell z.1 := by exact_mod_cast pc z.1
    refine ⟨⟨cov, _, inspectRun.on input, C+1, fun z => ?_⟩,1, fun z => ?_⟩
    · have h := (hcost (input z)).trans (Nat.mul_le_mul_left C
        (Nat.pow_le_pow_left (Nat.succ_le_succ (cap z)) d))
      have t : u (input z) + 1 ≤ (C+1)*cell z.1 := by
        have le : (z.1.heightBound+1)^d ≤ cell z.1 := by dsimp [cell]; omega
        have m := h.trans (Nat.mul_le_mul_left C le)
        rw [Nat.add_mul,Nat.one_mul]
        have := pc z.1
        omega
      change (u (input z) : ℝ)+1 ≤ ((C+1 : ℕ) : ℝ)*(cell z.1 : ℝ)
      exact_mod_cast t
    · simp only [Nat.cast_one,one_mul,Function.comp_apply]
      change (size (input z) : ℝ) ≤ (cell z.1 : ℝ)
      exact_mod_cast (cap z).trans (show z.1.heightBound ≤ cell z.1 by dsimp [cell]; omega)
  apply packet.chain
  apply (liftoff rows (fun z x => send (query z x)) (fun z x => send (inspect (query z x)))
    (fun z => (cell z : ℝ)) test).larger
  intro z
  have b : (rows z).count * cell z + 1 ≤ budget d z := by
    have := big z
    rw [Nat.add_mul,Nat.one_mul] at this
    have := pc z
    omega
  change ((rows z).count : ℝ) * (cell z : ℝ) + 1 ≤ (budget d z : ℝ)
  exact_mod_cast b

theorem program : ∃ d, Code.Task (budget d) (fun z => send z.desc) result := by
  obtain ⟨d,h⟩ := contract
  obtain ⟨_,u,task,K,bound⟩ := h.runs
  refine ⟨d,task.bound K fun z => ?_⟩
  have b := bound z
  change (u z : ℝ)+1 ≤ (K : ℝ)*(budget d z : ℝ) at b
  have ub : u z+1 ≤ K*budget d z := by exact_mod_cast b
  rw [Nat.mul_add]
  omega

end Comparison
end AffineAddress

end NearSquareRoot
end Computability
end OAI
