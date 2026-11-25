import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalMaskBank
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalMaskNative
import OAI.Computability.NearSquareRoot.InterchangeROMTableMaskRows

/-! # Compiling the persistent repair mask directly from the parent header

The rank list selects native slots. The bit-position list selects where the
corresponding three-way comparisons contribute to the repair lookup index.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMMaskCompile

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  IntegerMultiplication.Port Space CommonRegisters GeneratorSyntax InterchangeROMAddress
  InterchangeROMTable InterchangeROMRepair InterchangeROMRepair.Physical

noncomputable def emit (b n : ℕ) (ranks : List ℕ) (scaffold : ℕ) (pos : List ℕ) : Cmd :=
  (collect Mask.scanner b n ranks).join (maskRowCommand scaffold pos)

theorem emit_within : ∃ R, ∀ b n ranks scaffold pos, Within R (emit b n ranks scaffold pos) := by
  obtain ⟨S,ok⟩ := collect_within Mask.scanner
  exact ⟨max S 4,fun b n ranks k pos =>
    ⟨RegisterSelect.within_mono (le_max_left ..) _ (ok b n ranks),
      RegisterSelect.within_mono (le_max_right ..) _ (maskRow_within k pos)⟩⟩

theorem effective_emit {X : Type} [Primcodable X] {b n k : X → ℕ} {ranks pos : X → List ℕ}
    (hb : Computable b) (hn : Computable n) (hr : Computable ranks) (hk : Computable k)
    (hp : Computable pos) : Effective ltr fun x => emit (b x) (n x) (ranks x) (k x) (pos x) :=
  (effective_collect Mask.scanner hb hn hr).join (effective_maskRowCommand hk hp)

def price (C D b n m : ℕ) (h : Header) (pos : List ℕ) (N : ℕ) : ℕ :=
  let U := C*(N+(height b n h+1)^D+1)
  (45*size h+U+7)*m + 60*size h + (4*N+2)*m + U + maskRowFactor pos*(N+1) + 20

/-- The input is the bare native header. The output is a single stream of
little-endian repair indices, in the exact original order of the addresses. -/
theorem emit_bounded :
    ∃ C D : ℕ, ∀ {J : Type} [DecidableEq J] {n b m : ℕ} (ord : J ≃ Fin n)
      (cols : Series (Fin m)) (chooseSlot : Fin m → J) (scaffold : Fin m) (P G B : Tape)
      (_ : 2 ≤ b) (_ : solid P) (_ : solid G) (_ : solid B) (f : ℕ) (env : Env) deck base,
      DeckCap base deck →
      let ranks := cols.tab fun j => (ord (chooseSlot j)).val
      let bits := cols.tab Fin.val
      let rows := arrays ord (line b f) P G B
      let h := header f P G B
      let w := price C D b n m h bits rows.count
      BoundedFits env (emit b n ranks (cols.explore.idxOf scaffold) bits)
        (pile 0 (send h) deck) (pile 0 (stripe rows fun a =>
          numeral (Raw.mask (fun j => decide (number (a.2.2.2.1 (chooseSlot j)) <
            number (a.2.1 (chooseSlot j))))).val) deck) w (base+w) w := by
  obtain ⟨K,scanner⟩ := Mask.scanner_native
  obtain ⟨C,D,collects⟩ := collect_bounded Mask.scanner K 2
  refine ⟨C,D,?_⟩
  intro J dec n b m ord cols chooseSlot scaffold P G B hb hp hg hs f env deck base hd
  let rows := arrays ord (line b f) P G B
  let rank (j : Fin m) := (ord (chooseSlot j)).val
  let ranks := cols.tab rank
  let bits := cols.tab Fin.val
  let h := header f P G B
  let N := rows.count
  let y (j : ℕ) : Tree := if hj : j<n then Mask.maskRow (b:=b) ord P G B f (ord.symm ⟨j,hj⟩)
    else .atom false
  let tag (a : Keys P G B J (Block b f)) (j : Fin m) :=
    InterchangeSpectralStep.direction (number (a.2.1 (chooseSlot j))) (number (a.2.2.2.1 (chooseSlot j)))
  have legit (j : ℕ) (hj : j ∈ ranks) : j < n := by
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hj
    exact (ord (chooseSlot a)).isLt
  have volume (j : ℕ) (hj : j ∈ ranks) : (y j).count ≤ 4*N+1 := by
    rw [show y j = _ from dite_eq_left (legit j hj)]
    apply (stripe_size _ _ 3 _).trans (by simp [N,rows,Nat.mul_comm])
    intro a
    have small (s : Ordering) : (Mask.mark s).count ≤ 3 := by cases s <;> decide
    exact small _
  have scan (j : ℕ) (hj : j ∈ ranks) (dr : Deck) :
      let z := desc (numeric b n j j,h)
      Fits env Mask.scanner (pile 0 (send z) dr) (pile 0 (y j) dr) (K*(N+(size z+1)^2+1)) := by
    have hjn := legit j hj
    have out := scanner ord (ord.symm ⟨j,hjn⟩) P G B hb hp hg hs f env dr
    simpa only [Equiv.apply_symm_apply,Mask.parameter,y,dite_eq_left hjn] using out
  have left := collects b n ranks h y N env deck base hd legit volume scan
  have forest : Task.forest y ranks =
      stripe cols (fun j => stripe rows fun a => comparisonMark (comparisonCode (tag a j))) := by
    rw [stripe_simple]
    change Task.forest y (cols.explore.map rank) = _
    rw [Task.forest_map]
    congr 1
    funext j
    simp [y,rank,Mask.maskRow,rows,tag]
  rw [forest] at left
  have right := maskRow_bounded cols rows scaffold tag env deck base hd
  simp_rw [show ∀ (a : Keys P G B J (Block b f)) j, decide (tag a j = .gt) =
      decide (number (a.2.2.2.1 (chooseSlot j)) < number (a.2.1 (chooseSlot j))) from
      fun a j => direction_flag _ _] at right
  let U := C*(N+(height b n h+1)^D+1)
  let V := maskRowFactor bits*(N+1)
  let W := price C D b n m h bits N
  have len : ranks.length = m := by simp [ranks,Series.card]
  change BoundedFits env _ _ _ ((45*size h+U+7)*ranks.length+60*size h+10)
    (base+60*size h+(4*N+2)*ranks.length+U+11) (60*size h+U+10) at left
  change BoundedFits env _ _ _ V (base+V) V at right
  rw [len] at left
  have lcap : base+60*size h+(4*N+2)*m+U+11 ≤ base+W := by
    dsimp only [W,price]; dsimp only [U,V] at *; omega
  have rcap : V ≤ W := by dsimp only [W,price,V]; omega
  have reserve : (60*size h+U+10)+1 ≤ W := by dsimp only [W,price,U]; omega
  have out := (left.mono le_rfl lcap le_rfl).join
    (right.mono le_rfl (Nat.add_le_add_left rcap base) rcap) reserve
  change BoundedFits env _ _ _ W (base+W) W
  apply out.mono _ le_rfl le_rfl
  dsimp only [W,price,U,V]
  omega

end InterchangeROMMaskCompile

end NearSquareRoot
end Computability
end OAI
