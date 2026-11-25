import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalCorrectionCost
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalMaskEmit
import OAI.Computability.NearSquareRoot.KernelComputableAddress

/-! # Native sign-dependent Hermite leaf from a raw selected repair table -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Correction

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  IntegerMultiplication.Port Space CommonRegisters GeneratorSyntax InterchangeROMAddress
  InterchangeROMTable InterchangeROM InterchangeROMMaskCompile

noncomputable def nativeLeaf (b n : ℕ) (ranks : List ℕ) (scaffold : ℕ) (pos : List ℕ)
    (p s m : ℕ) (t : Raw.Tape) (oi ii : List CheckIndex) : Cmd :=
  leaf (emit b n ranks scaffold pos) p s m t oi ii

theorem nativeLeaf_within : ∃ R, ∀ b n ranks scaffold pos p s m t oi ii,
    Within R (nativeLeaf b n ranks scaffold pos p s m t oi ii) := by
  obtain ⟨R,e⟩ := emit_within
  exact ⟨max 4 R,fun b n r k pos p s m t oi ii => leaf_within (le_max_left ..)
    (RegisterSelect.within_mono (le_max_right ..) _ (e b n r k pos)) p s m t oi ii⟩

theorem effective_nativeLeaf {X : Type} [Primcodable X] {b n k p s m : X → ℕ}
    {ranks pos : X → List ℕ} {t : X → Raw.Tape} {oi ii : X → List CheckIndex}
    (hb : Computable b) (hn : Computable n) (hr : Computable ranks) (hk : Computable k)
    (hpos : Computable pos) (hp : Computable p) (hs : Computable s) (hm : Computable m)
    (ht : Computable t) (ho : Computable oi) (hi : Computable ii) : Effective ltr fun x =>
      nativeLeaf (b x) (n x) (ranks x) (k x) (pos x) (p x) (s x) (m x) (t x) (oi x) (ii x) :=
  effective_leaf (effective_emit hb hn hr hk hpos) hp hs hm ht ho hi

/-- Packing the dependent payload as one address recovers exactly the
two-block linear map used in the algebraic repair formula. -/
theorem correctValue_applyTag {D A : Type} {P : A → Type} {p w s m : ℕ}
    [Fact (p+1).Prime] (t : Raw.Tape) (η : A → Fin m → Bool)
    (v : Bool → D → (a : A) → P a → Fin s → ZMod (p+1))
    (o : Bool) (d : D) (a : A) (j : P a) :
    correctValue (w:=w) t η v o d a j = applyTag (Raw.decode p w s m t)
      (fun z : Sigma P => η z.1) o (fun l z => v false l z.1 z.2)
      (fun l z => v true l z.1 z.2) d ⟨a,j⟩ := rfl

theorem computable_linearFactor {X : Type} [Primcodable X] {p s m : X → ℕ}
    {t : X → Raw.Tape} {oi ii : X → List CheckIndex} (hp : Computable p)
    (hs : Computable s) (hm : Computable m) (ht : Computable t)
    (ho : Computable oi) (hi : Computable ii) :
    Computable fun x => linearFactor (p x) (s x) (m x) (t x) (oi x) (ii x) := by
  have pow : Computable fun z : ℕ => 2^z :=
    (KernelComputableAddress.primrec_pow (Primrec.const 2) Primrec.id).to_comp
  let plus := @Primrec₂.to_comp _ _ _ _ _ _ Nat.add Primrec.nat_add
  let times := @Primrec₂.to_comp _ _ _ _ _ _ Nat.mul Primrec.nat_mul
  exact plus.comp (computable_kernelFactor hp hs hm ht ho hi) (times.comp (Computable.const 1200)
    (plus.comp (plus.comp (times.comp (plus.comp (Primrec.list_length.to_comp.comp hi) (Computable.const 1))
      (plus.comp (times.comp (Computable.const 2) hp) (Computable.const 8)))
      (times.comp (Computable.const 4) (pow.comp hm))) (Computable.const 9)))

def sign {J : Type} {m b f : ℕ} {P G B : Tape} (chooseSlot : Fin m → J)
    (a : Keys P G B J (Block b f)) (j : Fin m) : Bool :=
  decide (number (a.2.2.2.1 (chooseSlot j)) < number (a.2.1 (chooseSlot j)))

/-- The only external input at a data address is its compact native header.
A physical comparison reads the specified slot ranks, the result is duplicated
over the variable payload, and the selected two-by-two correction acts on all
payload symbols. -/
theorem nativeLeaf_bounded :
    ∃ C E : ℕ, ∀ {J D : Type} [DecidableEq J] [Fintype D] [DecidableEq D]
      {n b m p s w : ℕ} (ord : J ≃ Fin n) (cols : Series (Fin m))
      (chooseSlot : Fin m → J) (k : Fin m) (P G B : Tape) (_ : 2 ≤ b)
      (_ : solid P) (_ : solid G) (_ : solid B) (f : ℕ) (t : Raw.Tape)
      (src dst : Series (D × Fin s)) (lane : D → ℕ) (_ : Function.Injective lane)
      {Y : Keys P G B J (Block b f) → Type} (payload : (a : _) → Series (Y a))
      (width : ℕ) (_ : ∀ a, (payload a).count ≤ width)
      (v : Bool → D → (a : _) → Y a → Fin s → ZMod (p+1)) (env : Env) deck base,
      DeckCap base deck →
      let ranks := cols.tab fun j => (ord (chooseSlot j)).val
      let pos := cols.tab Fin.val
      let ii := (twoBlocks src).tab (checkIndex lane)
      let oi := (twoBlocks dst).tab (checkIndex lane)
      let rows := arrays ord (line b f) P G B
      let h := header f P G B
      let charge := price C E b n m h pos rows.count + 1200*size h +
        linearFactor p s m t oi ii * (rows.count*(width+1)+1)
      let out := correctValue (w:=w) t (sign chooseSlot) v
      let xs := encodedBank src rows payload (v false) ++ encodedBank src rows payload (v true)
      let ys := encodedBank dst rows payload (out false) ++ encodedBank dst rows payload (out true)
      BoundedFits env (nativeLeaf b n ranks (cols.explore.idxOf k) pos p s m t oi ii)
        (pile 0 (packet (send h) xs) deck) (pile 0 (packet (send h) ys) deck)
        charge (base+2*charge) charge := by
  obtain ⟨C,E,emitRuns⟩ := emit_bounded
  refine ⟨C,E,?_⟩
  intro J D decJ finD decD n b m p s w ord cols chooseSlot k P G B hb hP hG hB f t
    src dst lane inj Y payload width hw v env deck base hr ranks pos ii oi rows h charge out xs ys
  let time := price C E b n m h pos rows.count
  have result := leaf_bounded (w:=w) (send h) (emit b n ranks (cols.explore.idxOf k) pos)
    time t (sign chooseSlot) src dst lane inj rows payload width hw v env
    (fun d z hd => (emitRuns ord cols chooseSlot k P G B hb hP hG hB f env d z hd).fits)
    deck base hr
  have c := clock_le (send h) time t (sign chooseSlot) src dst lane rows payload width hw v
  exact result.mono c (Nat.add_le_add_left (Nat.mul_le_mul_left 2 c) base) c

end InterchangeROMRepair.Physical.Correction

end NearSquareRoot
end Computability
end OAI
