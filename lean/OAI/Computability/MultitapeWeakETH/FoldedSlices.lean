import OAI.Computability.MultitapeWeakETH.FourCopyTensor
import OAI.Computability.MultitapeWeakETH.ProcessorWires
import OAI.Computability.MultitapeWeakETH.Processor

/-! # Original column tensors inside the common folded graph -/

namespace OAI.Computability.MultitapeWeakETH.FoldedNetwork

open VPVNP.WireTensor Finset
open scoped Classical
noncomputable section

variable {n b N : ℕ} (G : Network n b) {K : Type} [Field K]

abbrev Core := Fin 4 × Fin G.edges
def coreSrc (e : Core G) : Site G N := original G (G.src e.2)
def coreDst (e : Core G) : Site G N := original G (G.dst e.2)
abbrev CoreMessage (e : Core G) := Word (G.width e.2)

def Raw : Site G N → Type
  | .inl v => Fin 4 → G.localBits G.output v → Bool
  | .inr _ => Unit

instance (v : Site G N) : Fintype (Raw G v) := by
  cases v <;> unfold Raw Network.localBits <;> infer_instance

/-- Each original site receives only its local input indices. Each processor
receives only its four error masks. -/
def Pin : Site G N → Type
  | .inl v => G.localBits G.input v → Bool
  | .inr (.inl _) => Fin 4 → Word b
  | .inr (.inr _) => Unit

instance (v : Site G N) : Fintype (Pin G v) := by
  rcases v with _ | _ | _ <;> unfold Pin <;> first | infer_instance | unfold Network.localBits; infer_instance

def pinFor (x : Word n) (masks : Fin 4 → Block n b → Word b) : (v : Site G N) → Pin G v
  | .inl _ => fun i => x i.val
  | .inr (.inl j) => fun r => masks r j
  | .inr (.inr _) => ()

def rawFor (z : Fin 4 → Word n) : (v : Site G N) → Raw G v
  | .inl _ => fun r i => z r i.val
  | .inr _ => ()

abbrev coreSupply (K : Type) [Field K] := wireNetwork (k:=K) (coreSrc G (N:=N)) (coreDst G) (CoreMessage G)

def copyMaps (tables : Fin 4 → (v : Fin G.vertices) → G.View v → K)
    (v : Site G N) (pin : Pin G v) (ext : Raw G v) (wire : (coreSupply G K (N:=N)).Basis v) : K :=
  match v with
  | .inl v => G.parallelMap tables v pin ext
      (fun e h => wire.1 e (congrArg Sum.inl h),fun e h => wire.2 e (congrArg Sum.inl h))
  | .inr _ => 1

theorem copies_on_sites (hb : 0 < b) (tables : Fin 4 → (v : Fin G.vertices) → G.View v → K)
    (x : Word n) (masks : Fin 4 → Block n b → Word b) (z : Fin 4 → Word n) (c : Fin 4 → K)
    (returns : ∀ r w, G.contract (tables r) x w = if w = z r then c r else 0) :
    applyLocal (fun v => copyMaps G tables v (pinFor G x masks v)) (coreSupply G K (N:=N)).coeff =
      fun ext => if ext = rawFor G z then ∏ r, c r else 0 := by
  funext ext
  let old (v : Fin G.vertices) : Fin 4 → G.localBits G.output v → Bool := ext (original G v)
  have slice := congrFun (G.parallel_returns hb tables x z c returns) old
  have equiv : (old = fun _ r i => z r i.val) ↔ ext = rawFor G z := by
    refine ⟨fun h => funext (fun v => ?_),fun h => by subst ext; rfl⟩
    cases v with
    | inl v => exact congrFun h v
    | inr v => exact Subsingleton.elim (α:=Unit) _ _
  simp only [← equiv]
  trans applyLocal (fun v => G.parallelMap tables v (fun i => x i.val)) (Network.parallelSupply G K (Fin 4)).coeff old
  · erw [applyLocal_wireNetwork,applyLocal_wireNetwork]
    apply sum_congr rfl
    intro s _
    rw [Fintype.prod_sum_type]
    simp only [copyMaps,prod_const_one,mul_one,pinFor]
    rfl
  · exact slice

def indexOf (hb : 0 < b) (i : Fin n) : Block n b :=
  ⟨i.val/b,(Nat.div_lt_iff_lt_mul hb).mpr (by
    rw [mul_comm]
    exact i.isLt.trans_le ((ceilDiv_le_iff_le_mul hb).mp le_rfl))⟩

private theorem blockOwner (hb : 0 < b) (j : Block n b) (r : Fin b) (h : j.val*b+r.val < n) :
    block b ((⟨j.val*b+r.val,h⟩ : Fin n).rev) = j.val := by
  simp only [block,Fin.val_rev]
  rw [show n-1-(n-(j.val*b+r.val+1)) = j.val*b+r.val by omega,
    Nat.mul_comm j.val b,Nat.mul_add_div hb,Nat.div_eq_of_lt r.isLt,Nat.add_zero]

/-- Only the owner of j sends block j. The zero padding has no extra
degrees of freedom in the contraction sum. -/
def send (hb : 0 < b) (v : Fin G.vertices) (ext : Fin 4 → G.localBits G.output v → Bool)
    (r : Fin 4) (j : Block n b) : Word b := fun i =>
  if h : v = G.output j ∧ j.val*b+i.val < n then
    ext r ⟨(⟨_,h.2⟩ : Fin n).rev,⟨j,(blockOwner hb j i h.2).symm,h.1.symm⟩⟩
  else false

theorem send_message (hb : 0 < b) (z : Fin 4 → Word n) (r : Fin 4) (j : Block n b) :
    send G hb (G.output j) (fun c i => z c i.val) r j =
      Difference.message b j (List.ofFn (z r)).reverse := by
  funext i
  by_cases occurs : j.val*b+i.val < n
  · have bd : j.val*b+i.val < (List.ofFn (z r)).reverse.length := by simpa
    simp only [send,occurs,and_self,dite_true,Difference.message,List.getElem?_eq_getElem bd,
      Option.getD_some,List.getElem_reverse,List.getElem_ofFn,List.length_ofFn]
    apply congrArg (z r)
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  · simp [send,occurs,Difference.message]

end
end OAI.Computability.MultitapeWeakETH.FoldedNetwork
