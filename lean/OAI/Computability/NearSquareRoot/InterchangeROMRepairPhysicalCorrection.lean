import OAI.Computability.NearSquareRoot.InterchangeROMTableCorrectionEffective
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomROM
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysical
import OAI.Computability.NearSquareRoot.InterchangePayloadTemplate
import OAI.Computability.NearSquareRoot.InterchangeROMProgramEffective

/-! # The sign-conditioned correction on packed check banks

The first input row is the numerical sign mask, repeated at each payload cell.
It supplies the scaffold for both transposes, including when the check width
vanishes. A single finite lookup at each cell produces both correction blocks.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Correction

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  CommonRegisters Space LoomRegisters GeneratorSyntax InterchangeROMTable InterchangePayloadBank

variable {D A : Type} [Fintype D] [DecidableEq D] {s p w m : ℕ} {P : A → Type}

/-- Exact order of the two check blocks. Each input series may enumerate labels
and check coordinates in any order. -/
def twoBlocks (s : Series A) : Series (Bool × A) where
  explore := s.explore.map (fun a => (false,a)) ++ s.explore.map (fun a => (true,a))
  nodup := List.nodup_append.mpr ⟨s.nodup.map (fun _ _ h => congrArg Prod.snd h),
    s.nodup.map (fun _ _ h => congrArg Prod.snd h), by simp⟩
  complete := by rintro ⟨_|_,z⟩ <;> simp [s.complete]

def broadcast (rows : Series A) (payload : (a : A) → Series (P a)) (tag : A → Tree) :=
  stripe rows fun a => stripe (payload a) fun _ => tag a

def encodedRow (rows : Series A) (payload : (a : A) → Series (P a))
    (v : (a : A) → P a → ZMod (p+1)) :=
  stripe rows fun a => stripe (payload a) (fun j => numeral (v a j).val)

def encodedBank (ii : Series (D × Fin s)) (rows : Series A) (payload : (a : A) → Series (P a))
    (x : D → (a : A) → P a → Fin s → ZMod (p+1)) : List Tree :=
  ii.tab fun u => encodedRow rows payload fun a j => x u.1 a j u.2

private theorem stripe_template {U : Type} (ii : Series U) (z : Tree) (v : U → Tree) :
    stripe (templateRows ii) (fun a => a.elim z v) = Tree.fork z (stripe ii v) := by
  simp only [stripe_simple,templateRows,Task.forest_cons,Option.elim_none,Task.forest_map]
  rfl

omit [Fintype D] [DecidableEq D] in
private theorem stripe_two (q : Series (D × Fin s)) (rows : Series A) (payload : (a : A) → Series (P a))
    (v : Bool → D → (a : A) → P a → Fin s → ZMod (p+1)) :
    stripe (twoBlocks q) (fun t => encodedRow rows payload (fun a j => v t.1 t.2.1 a j t.2.2)) =
      Task.forest id (encodedBank q rows payload (v false) ++ encodedBank q rows payload (v true)) := by
  simp [twoBlocks,encodedBank,stripe,Series.tab,List.map_map,Function.comp_def]

/-- The checked cell ROM applied to the whole bank at once, with the physical
input and output orders supplied as literal lists of numbered roles. -/
def kernel (p s m : ℕ) (t : Raw.Tape) (oi ii : List CheckIndex) : Cmd :=
  romPayload 0 oi.length (spelledTable (checkTable p s m t oi ii))

theorem kernel_within (p s m : ℕ) (t : Raw.Tape) (oi ii : List CheckIndex) :
    Within 4 (kernel p s m t oi ii) := romPayload_within ..

theorem effective_kernel {X : Type} [Primcodable X] {p s m : X → ℕ} {t : X → Raw.Tape}
    {oi ii : X → List CheckIndex} (hp : Computable p) (hs : Computable s) (hm : Computable m)
    (ht : Computable t) (ho : Computable oi) (hi : Computable ii) :
    Effective ltr fun x => kernel (p x) (s x) (m x) (t x) (oi x) (ii x) :=
  effective_romPayload (Computable.const 0) (Computable.list_length.comp ho)
    (computable_spelled_checkTable hp hs hm ht ho hi)

def kernelFactor (p s m : ℕ) (t : Raw.Tape) (oi ii : List CheckIndex) :=
  romPayloadFactor (ii.length+1) oi.length (spelledTable (checkTable p s m t oi ii))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem computable_kernelFactor {X : Type} [Primcodable X] {p s m : X → ℕ} {t : X → Raw.Tape}
    {oi ii : X → List CheckIndex} (hp : Computable p) (hs : Computable s) (hm : Computable m)
    (ht : Computable t) (ho : Computable oi) (hi : Computable ii) :
    Computable fun x => kernelFactor (p x) (s x) (m x) (t x) (oi x) (ii x) := by
  have h : Primrec (fun v : ℕ × ℕ × SpellingTable => romPayloadFactor v.1 v.2.1 v.2.2) :=
    primrec_romPayloadFactor (X := ℕ × ℕ × SpellingTable) Primrec.fst
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  apply Computable.comp (f:=fun v : ℕ × ℕ × SpellingTable => romPayloadFactor v.1 v.2.1 v.2.2) (g:=fun x : X => ((ii x).length+1,(oi x).length,spelledTable (checkTable (p x) (s x) (m x) (t x) (oi x) (ii x)))) h.to_comp
  exact ((Computable.succ.comp (Computable.list_length.comp hi)).pair
    ((Computable.list_length.comp ho).pair (computable_spelled_checkTable hp hs hm ht ho hi)))

def correctValue (t : Raw.Tape) (η : A → Fin m → Bool)
    (v : Bool → D → (a : A) → P a → Fin s → ZMod (p+1))
    (o : Bool) (d : D) (a : A) (j : P a) : Fin s → ZMod (p+1) :=
  let M := (Raw.decode p w s m t).correct (η a) o
  (M false).mulVec (v false d a j) + (M true).mulVec (v true d a j)

theorem kernel_bounded (t : Raw.Tape) (η : A → Fin m → Bool)
    (src dst : Series (D × Fin s)) (lane : D → ℕ) (inj : Function.Injective lane)
    (rows : Series A) (payload : (a : A) → Series (P a)) (width : ℕ) (hw : ∀ a, (payload a).count ≤ width)
    (v : Bool → D → (a : A) → P a → Fin s → ZMod (p+1))
    (env : Env) (deck : Deck) (base : ℕ) (hr : DeckCap base deck) :
    let ii := (twoBlocks src).tab (checkIndex lane)
    let oi := (twoBlocks dst).tab (checkIndex lane)
    let z := broadcast rows payload (fun a => numeral (Raw.mask (η a)).val)
    let out := correctValue (w:=w) t η v
    let cost := kernelFactor p s m t oi ii * (rows.count * (width+1)+1)
    BoundedFits env (kernel p s m t oi ii)
      (pile 0 (Task.forest id (z :: (encodedBank src rows payload (v false) ++ encodedBank src rows payload (v true)))) deck)
      (pile 0 (Task.forest id (encodedBank dst rows payload (out false) ++ encodedBank dst rows payload (out true))) deck)
      cost (base+cost) cost := by
  let si := twoBlocks src
  let so := twoBlocks dst
  let ii := si.tab (checkIndex lane)
  let oi := so.tab (checkIndex lane)
  let tab := checkTable p s m t oi ii
  let z a := numeral (Raw.mask (η a)).val
  let vin (a : A) (j : P a) (u : Option (CheckRole D s)) :=
    u.elim (z a) fun k => numeral (v k.1 k.2.1 a j k.2.2).val
  let out := correctValue (w:=w) t η v
  let vout (a : A) (j : P a) (u : CheckRole D s) := numeral (out u.1 u.2.1 a j u.2.2).val
  have hcell (a : A) (j : P a) : RegisterLookup.read tab (stripe (templateRows si) (vin a j)) =
      stripe so (vout a j) ∧ (stripe (templateRows si) (vin a j), stripe so (vout a j)) ∈ tab := by
    simp only [vin,stripe_template]
    exact checkTable_correct (p:=p) (w:=w) (η a) t so si lane inj (fun k => v k.1 k.2.1 a j k.2.2)
  have h := romLayout_bounded (templateRows si) so none rows payload width hw vin vout tab hcell env deck base hr
  have hinput : stripe (templateRows si) (fun u => stripe rows fun a => stripe (payload a) (fun j => vin a j u)) =
      Tree.fork (broadcast rows payload z)
        (Task.forest id (encodedBank src rows payload (v false) ++ encodedBank src rows payload (v true))) := by
    trans stripe (templateRows si) (fun u => u.elim (broadcast rows payload z) (fun k =>
      encodedRow rows payload fun a j => v k.1 k.2.1 a j k.2.2))
    · congr 1; funext u; cases u <;> rfl
    rw [stripe_template,stripe_two]
  have houtput := stripe_two dst rows payload out
  have hi : (templateRows si).count = ii.length + 1 := by simp [templateRows,Series.count,ii,Series.tab]
  have ho : so.count = oi.length := by simp [oi,Series.tab,Series.count]
  dsimp only at h ⊢
  rw [hinput,show stripe so (fun u => stripe rows (fun a => stripe (payload a) (fun j => vout a j u))) = _ from houtput,
    hi,ho] at h
  simp only [templateRows,List.idxOf_cons_self] at h
  convert h using 1 <;> rfl

end InterchangeROMRepair.Physical.Correction

end NearSquareRoot
end Computability
end OAI
