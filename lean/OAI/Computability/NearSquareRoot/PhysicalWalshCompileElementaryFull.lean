import OAI.Computability.NearSquareRoot.PhysicalWalshCompileElementaryRaw
import OAI.Computability.NearSquareRoot.PhysicalWalshElementaryRouter

/-! # A complete effective elementary router on the raw XOR operands -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileElementaryRelease
open IntegerMultiplication Code PhysicalWalsh PhysicalWalshNode
open CommonRegisters GeneratorSyntax KernelPass.ComputableSyntax

/-- The bytecode writes destination first. The elementary sweep reads source first. -/
def directed (z : Raw × Op) : ℕ × PhysicalWalshCompileXorSwap.Params :=
  (0,z.1,arg z.2 1,arg z.2 0)

theorem primrec_directed : Primrec directed :=
  (Primrec.const 0).pair (Primrec.fst.pair ((primrec_arg.comp Primrec.snd (.const 1)).pair
    (primrec_arg.comp Primrec.snd (.const 0))))

theorem full_slice {a : ℕ} (src dst : Fin (a+1)) (ne : src ≠ dst) :
    PhysicalWalshCompileXorSwap.slice (cut false 0 (a+1)) src dst = PhysicalWalshNode.xor a (dst,src) := by
  funext s x n
  exact congrArg x (ElementarySweep.address_full src dst ne s n)

private def route (flat : ℕ × PhysicalWalshCompileXorSwap.Params → Cmd) (skip : Cmd) (r : Raw) (op : Op) :=
  if arg op 0 = arg op 1 then skip else flat (directed (r,op))

private theorem route_effective (flat : ℕ × PhysicalWalshCompileXorSwap.Params → Cmd) (skip : Cmd)
    (h : Effective ltr flat) : Effective ltr (Function.uncurry (route flat skip)) := by
  have test := Primrec.eq.comp (primrec_arg.comp (Primrec.snd (α:=Raw)) (.const 0))
    (primrec_arg.comp Primrec.snd (.const 1))
  exact (Computable.cond test.decide.to_comp (Computable.const (file ltr skip))
    (h.comp primrec_directed.to_comp)).of_eq fun z => by
      rcases z with ⟨r,op⟩
      by_cases e : arg op 0 = arg op 1 <;> simp [route,Function.uncurry,e]

/-- A single computable family routes every valid operand pair, including
diagonal pairs. Its time charges one full-row scan per bit of the slot. -/
theorem full : ∃ (c : Raw → Op → Cmd) (R E : ℕ), Effective ltr (Function.uncurry c) ∧
    (∀ raw op, Within R (c raw op)) ∧ ∀ (a W : ℕ) (ops : List Op), (Packed.decode (a+1) ops).i = W →
    ∀ (op : Op) (hd : arg op 0 < a+1) (hs : arg op 1 < a+1), ∀ d, E ≤ d →
    PhysicalWalshCompileXorPacket.FlatRuns (W:=W) (nodeScan a W d (ElementarySweep.extra (a+1)))
      (nodeArena a W d) (⟨_,hd⟩,⟨_,hs⟩) (c (a+1,ops) op) := by
  obtain ⟨R,E,c,hc,rc,ok⟩ := compile false
  obtain ⟨K,M,hk⟩ := PhysicalWalshCompileXorRoute.exists_kit
  refine ⟨route c K.erase,max M R,E,route_effective c K.erase hc,fun r op => ?_,?_⟩
  · unfold route
    split
    · exact hk.within_erase (le_max_left ..)
    · exact RegisterSelect.within_mono (le_max_right ..) _ (rc _)
  intro a W ops width op hd hs d de
  let src : Fin (a+1) := ⟨_,hs⟩
  let dst : Fin (a+1) := ⟨_,hd⟩
  change PhysicalWalshCompileXorRoute.Flat (a:=a) (W:=W) _ _ (PhysicalWalshNode.xor a (dst,src)) _
  by_cases e : arg op 0 = arg op 1
  · rw [route,ite_eq_left e]
    have eq := Fin.ext (show dst.val = src.val from e)
    have skip := hk.runs_id (a:=a) (W:=W) (scan:=nodeScan a W d (ElementarySweep.extra (a+1))) (arena:=nodeArena a W d)
      (fun _ => Nat.le_add_right ..) (fun _ => le_max_right ..)
    have id_ : PhysicalWalshNode.xor a (dst,src) = fun _ x => x := by
      rw [eq]; funext s x n; simp [PhysicalWalshNode.xor]
    rwa [id_]
  · rw [route,ite_eq_right e]
    have ne : src ≠ dst := fun h => e (congrArg Fin.val h).symm
    have run := ok a W ops width src dst ne 0 d de
    rw [full_slice src dst ne] at run
    exact run

end PhysicalWalshCompileElementaryRelease

end NearSquareRoot
end Computability
end OAI
