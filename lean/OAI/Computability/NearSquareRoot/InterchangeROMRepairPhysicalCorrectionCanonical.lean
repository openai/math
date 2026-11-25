import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalCorrectionNative
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalMaskClock
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelectedIndices
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepBankConcrete

/-! # Two-bank correction on the canonical packed repair layout -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Correction

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  IntegerMultiplication.Port Space CommonRegisters GeneratorSyntax InterchangeROMAddress
  InterchangeROMTable InterchangeROM

def nativeFactor (C E H b a p l s m : ℕ) (t : Raw.Tape) :=
  let idx := Selected.indices l s
  1201*InterchangeROMMaskCompile.linearFactor C E H b (a+m+a) m (List.range m) +
    linearFactor p s m t idx idx

theorem computable_nativeFactor {X : Type} [Primcodable X] (C E H : ℕ)
    {b a p l s m : X → ℕ} {t : X → Raw.Tape} (hb : Computable b) (ha : Computable a)
    (hp : Computable p) (hl : Computable l) (hs : Computable s) (hm : Computable m) (ht : Computable t) :
    Computable fun x => nativeFactor C E H (b x) (a x) (p x) (l x) (s x) (m x) (t x) := by
  have idx := Selected.computable_indices hl hs
  exact Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 1201)
    (InterchangeROMMaskCompile.computable_linearFactor C E H hb
      (Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp ha hm) ha) hm
      (Primrec.list_range.to_comp.comp hm))) (computable_linearFactor hp hs hm ht idx idx)

theorem encodedBank_packed {a m b f p l s : ℕ} {P G S : Tape} {D : Type}
    (rows : Series (Positions P G S a m b f)) (pay : Series D)
    (x : Bank (ZMod (p+1)) (Fin l) (Positions P G S a m b f × D) (Fin s)) :
    encodedBank (Selected.checkSeries l s) rows (fun _ => pay) (fun u k j => x u (k,j)) =
      SweepBank.packed rows pay x := by
  simp only [encodedBank,Selected.checkSeries,Series.tab,Series.via,Series.natural,Series.fixed,
    List.map_map,SweepBank.packed,LocalTable.Lift.bank,LocalTable.Lift.render,List.ofFn_eq_map]
  rfl

theorem packed_bounded :
    ∃ C E H : ℕ, ∀ {a m b f p l s w : ℕ} [Fact (p+1).Prime] [NeZero b]
      (_ : 2 ≤ b) (_ : 0 < m) (P G S : Tape) (_ : ∀ j ∈ P ++ G ++ S, 2 ≤ j ∧ j ≤ b)
      (t : Raw.Tape) {D : Type} (pay : Series D) (width : ℕ) (_ : pay.count ≤ width)
      (x y : Bank (ZMod (p+1)) (Fin l) (Positions P G S a m b f × D) (Fin s))
      (env : Env),
      let h := send (header f P G S)
      let rows := SweepBank.layout P G S a m b f
      let js := Selected.indices l s
      let price := nativeFactor C E H b a p l s m t * (rows.count*(width+1)+1)
      let op := applyTag (Raw.decode p w s m t) (flags ∘ Prod.fst)
      SweepBank.Run env (nativeLeaf b (a+m+a) ((List.range m).map (a+·)) 0
        (List.range m) p s m t js js) (packet h (SweepBank.packed rows pay x ++ SweepBank.packed rows pay y))
        (packet h (SweepBank.packed rows pay (op false x y) ++ SweepBank.packed rows pay (op true x y)))
        ⟨price,2*price,price⟩ := by
  obtain ⟨C,E,native⟩ := nativeLeaf_bounded
  obtain ⟨H,shape⟩ := InterchangeROMMaskCompile.price_le E
  refine ⟨C,E,H,?_⟩
  intro a m b f p l s w prime nz hb hm P G S ok t D pay width hw x y env h rows js price op deck base hr
  let ord := Equiv.refl (Fin (a+m+a))
  let slot := Interchange.RepairSchedule.mainSlots a m
  let cols := Series.natural m
  let src := Selected.checkSeries l s
  let data (o : Bool) (d : Fin l) (z : Positions P G S a m b f) (j : D) := (if o then y else x) d (z,j)
  have hp : solid P := fun i hi => (ok i (by simp [hi])).1
  have hg : solid G := fun i hi => (ok i (by simp [hi])).1
  have hs : solid S := fun i hi => (ok i (by simp [hi])).1
  let k : Fin m := ⟨0,hm⟩
  have res := native (p:=p) (w:=w) ord cols slot k P G S hb hp hg hs f t src src
    Fin.val Fin.val_injective (fun _ => pay) width (fun _ => hw) data env deck base hr
  have rank : cols.tab (fun j => (ord (slot j)).val) = (List.range m).map (a+·) := by
    have r := SweepBank.slots_eq a m false
    change (((List.finRange m).map slot).map Fin.val) = _ at r
    rw [List.map_map] at r
    exact r
  have bits : cols.tab Fin.val = List.range m := by
    change (List.finRange m).map Fin.val = _
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp
  have zero : cols.explore.idxOf k = 0 := List.idxOf_finRange k
  have indices : (twoBlocks src).tab (checkIndex Fin.val) = js := Selected.indices_typed l s
  have out (o : Bool) : correctValue (w:=w) t (sign (b:=b) (f:=f) slot) data o =
      (fun d z j => op o x y d (z,j)) := by rfl
  dsimp only at res
  rw [rank,bits,zero,indices] at res
  rw [out,out] at res
  change BoundedFits env _ (pile 0 (packet h
    (encodedBank src rows (fun _ => pay) (fun d z j => x d (z,j)) ++
    encodedBank src rows (fun _ => pay) (fun d z j => y d (z,j)))) deck)
    (pile 0 (packet h (encodedBank src rows (fun _ => pay) (fun d z j => op false x y d (z,j)) ++
    encodedBank src rows (fun _ => pay) (fun d z j => op true x y d (z,j)))) deck) _ _ _ at res
  simp only [src,encodedBank_packed] at res
  let mask := InterchangeROMMaskCompile.price C E b (a+m+a) m (header f P G S) (List.range m) rows.count
  let L := InterchangeROMMaskCompile.linearFactor C E H b (a+m+a) m (List.range m)
  have hM : mask ≤ L*rows.count := shape C m (List.range m) ord (slot k) P G S hb ok f
  have hsize : size (header f P G S) ≤ mask := by dsimp only [mask,InterchangeROMMaskCompile.price]; omega
  let M := rows.count*(width+1)+1
  have rM : rows.count ≤ M := by dsimp only [M]; nlinarith
  have hL := hM.trans (Nat.mul_le_mul_left L rM)
  have clk : mask+1200*size (header f P G S)+linearFactor p s m t js js*M ≤ price := by
    change _ ≤ (1201*L+linearFactor p s m t js js)*M
    rw [Nat.add_mul,Nat.mul_assoc]
    omega
  exact res.mono clk (Nat.add_le_add_left (Nat.mul_le_mul_left 2 clk) base) clk

end InterchangeROMRepair.Physical.Correction

end NearSquareRoot
end Computability
end OAI
