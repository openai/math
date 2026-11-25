import OAI.Computability.MultitapeWeakETH.FoldedSlices

/-! # A pinned four-column tensor with two folded copies of its payload -/

namespace OAI.Computability.MultitapeWeakETH.FoldedNetwork

open VPVNP.WireTensor Finset
open scoped Classical
noncomputable section
variable {n b N L : ℕ} [NeZero N] {K : Type} [Field K] (G : Network n b)

def column (lane right : Bool) : Fin 4 :=
  if lane then (if right then 3 else 2) else (if right then 1 else 0)

def pairedStep (j : Block n b) (masks raw : Fin 4 → Word b) (old : Bool → Bool) :
    (Bool → Word b) × (Bool → Bool) :=
  let result (lane : Bool) := Difference.process n j.val (raw (column lane false)) (raw (column lane true))
    (masks (column lane false)) (masks (column lane true)) (old lane)
  (fun lane => (result lane).1,fun lane => (result lane).2)

def localEmit (hb : 0 < b) (v : Site G N) (ext : Raw G v) : Fin 4 → Block n b → Word b :=
  match v with
  | .inl v => send G hb v ext
  | .inr _ => fun _ _ _ => false

def localMasks (v : Site G N) (p : Pin G v) : Fin 4 → Word b :=
  match v with
  | .inr (.inl _) => p
  | _ => fun _ _ => false

def tests (hb : 0 < b) (v : Site G N) (p : Pin G v) (ext : Raw G v) :
    (auxSupply G K (N:=N)).Basis v → Prop :=
  checks G (localEmit G hb v ext) (fun j => pairedStep j (localMasks G v p)) v

def destination (hb : 0 < b) (i : Fin n) : Site G N :=
  auxDst G (.inr (.inr (indexOf hb i)))

abbrev demand (hb : 0 < b) (l r : Fin L → Fin n) :=
  wireNetwork (k:=K) (destination G (N:=N) hb ∘ l) (destination G hb ∘ r) (fun _ => Bool)

/-- Each terminal exposes precisely the bits assigned to it, in both lanes.
This includes the two distinct half-edges of a colocated pair. -/
def read (hb : 0 < b) (l r : Fin L → Fin n) (v : Site G N) (w : (auxSupply G K (N:=N)).Basis v) :
    (demand G hb l r (K:=K)).Basis v :=
  (fun j h => w.2 (.inr (.inr (indexOf hb (l j)))) h false ⟨(l j).val%b,Nat.mod_lt _ hb⟩,
   fun j h => w.2 (.inr (.inr (indexOf hb (r j)))) h true ⟨(r j).val%b,Nat.mod_lt _ hb⟩)

abbrev typedSupply (K : Type) [Field K] := TablePipeline.combined (K:=K) (coreSrc G (N:=N)) (coreDst G)
  (auxSrc G) (auxDst G) (CoreMessage G) Message

/-- Each site's matrix is a function of its own pin value only. The four
field tables and the two exposed intervals can be chosen separately per shift. -/
def maps (hb : 0 < b) (l r : Fin L → Fin n) (tables : Fin 4 → (v : Fin G.vertices) → G.View v → K)
    (v : Site G N) (p : Pin G v) (z : (demand G hb l r (K:=K)).Basis v)
    (wire : (typedSupply G K (N:=N)).Basis v) : K :=
  let prior := TablePipeline.left (coreSrc G) (coreDst G) (auxSrc G) (auxDst G) (CoreMessage G) Message v wire
  let post := TablePipeline.right (coreSrc G) (coreDst G) (auxSrc G) (auxDst G) (CoreMessage G) Message v wire
  ∑ ext, (if tests G hb v p ext post ∧ z = read G hb l r v post then 1 else 0) *
    copyMaps G tables v p ext prior

theorem display (hb : 0 < b) (l r : Fin L → Fin n)
    (tables : Fin 4 → (v : Fin G.vertices) → G.View v → K)
    (x : Word n) (masks : Fin 4 → Block n b → Word b) (z : Fin 4 → Word n) (scalar : Fin 4 → K)
    (returns : ∀ i w, G.contract (tables i) x w = if w = z i then scalar i else 0)
    (carry : Block n b → Bool → Bool) (diff : Block n b → Bool → Word b)
    (spec : ∀ j, pairedStep j (fun i => masks i j) (fun i => Difference.message b j.val (List.ofFn (z i)).reverse)
      (if j.val = 0 then fun _ => false else carry ((finRotate _).symm j)) = (diff j,carry j))
    (payload : Fin L → Bool)
    (leftBits : ∀ j, diff (indexOf hb (l j)) false ⟨(l j).val%b,Nat.mod_lt _ hb⟩ = payload j)
    (rightBits : ∀ j, diff (indexOf hb (r j)) true ⟨(r j).val%b,Nat.mod_lt _ hb⟩ = payload j) :
    applyLocal (fun v => maps G hb l r tables v (pinFor G x masks v)) (typedSupply G K (N:=N)).coeff =
      fun y => if y = edgeAssignment (destination G hb ∘ l) (destination G hb ∘ r) payload
        then ∏ i, scalar i else 0 := by
  let emit i (j : Block n b) := Difference.message b j.val (List.ofFn (z i)).reverse
  let step (j : Block n b) := pairedStep j (fun i => masks i j)
  let chosen := assignment emit carry diff
  have unique (labels) : (∀ v : Site G N, tests (K:=K) G hb v (pinFor G x masks v) (rawFor G z v)
      (edgeAssignment (auxSrc G) (auxDst G) labels v)) ↔ labels = chosen := by
    rw [← unique_assignment (K:=K) (N:=N) G emit step carry diff spec]
    apply forall_congr'
    intro v
    rcases v with v | j | t
    · change (∀ i j (h : v = G.output j), labels (.inl (i,j)) = send G hb v (fun u k => z u k.val) i j) ↔
        ∀ i j (h : v = G.output j), labels (.inl (i,j)) = emit i j
      apply forall_congr'; intro i
      apply forall_congr'; intro j
      apply forall_congr'; rintro rfl
      rw [send_message]
    · rfl
    · rfl
  have result := TablePipeline.unique_processor (coreSrc G) (coreDst G) (auxSrc G) (auxDst G)
    (CoreMessage G) Message (fun v => copyMaps G tables v (pinFor G x masks v))
    (rawFor G z) _ (copies_on_sites (N:=N) G hb tables x masks z scalar returns)
    (fun v => tests G hb v (pinFor G x masks v)) (fun v _ => read G hb l r v) chosen unique
  apply result.trans
  have correct : (fun v : Site G N => read (K:=K) G hb l r v (edgeAssignment (auxSrc G) (auxDst G) chosen v)) =
      edgeAssignment (destination G hb ∘ l) (destination G hb ∘ r) payload := by
    funext v
    apply Prod.ext
    · funext j h
      exact leftBits j
    · funext j h
      exact rightBits j
  simp only [correct]
  funext y
  split <;> split <;> first | rfl | (rename_i h₁ h₂; exact (h₁ h₂).elim) | (rename_i h₁ h₂; exact (h₂ h₁).elim)

end
end OAI.Computability.MultitapeWeakETH.FoldedNetwork
