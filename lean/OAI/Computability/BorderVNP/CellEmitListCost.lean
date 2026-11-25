import OAI.Computability.BorderVNP.CellEmitRange
import OAI.Computability.BorderVNP.CellCQFMeterPair
import OAI.Computability.BorderVNP.CellCQFListMapCost
import OAI.Computability.BorderVNP.CellCQFListFlattenCost

/-! # Native costs of compact record-list emitters

The original environment and list are retained through tabulation. Each actual
element is printed once, and the installed word concatenator sees the encoded
list of those emitted fragments.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure

variable {A B : Type} {ea : A → List Bool} {eb : B → List Bool}

private def mapWork (x : A) (rows : List B) (C L : ℕ) :=
  C+((prodCode ea (listCode eb) (x,rows)).length+1)^9+
    (tabSpan (prodCode ea (listCode eb)) rows.length (x,rows) L)^2+1

private theorem flatten_meter {xs : List (List Bool)} {N S L : ℕ}
    (hn : xs.length = N) (hL : ∀ w ∈ xs, w.length ≤ L)
    (hs : (N+1)*(L+1)+1 ≤ S) :
    listJoinWords.meter xs ≤ 16*(listJoinWords.bound.eval 1+1)*S^2 := by
  have h := listCode_length_map_bound (id : List Bool → List Bool) id xs L hL
  simp only [id_eq,List.map_id_fun,hn] at h
  have hnle : N*(L+1) ≤ (N+1)*(L+1) := Nat.mul_le_mul_right _ (Nat.le_succ N)
  rw [show 2*L+2=2*(L+1) by ring,Nat.mul_left_comm N 2] at h
  have sq := Nat.pow_le_pow_left (by omega : (listCode id xs).length+1 ≤ 3*S) 2
  rw [Nat.mul_pow] at sq
  have cost := (cost_listJoinWords xs).trans (Nat.mul_le_mul_left _ sq)
  have hflat := flatten_length_le_code xs
  have ssq : S ≤ S^2 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ S) (show 1 ≤ 2 by decide)
  simp only [meter,id_eq]
  rw [Nat.mul_assoc,Nat.add_mul,Nat.one_mul]
  rw [show listJoinWords.bound.eval 1*(3^2*S^2) = 9*(listJoinWords.bound.eval 1*S^2) by ring] at cost
  omega

private theorem map_then_join {rows : A → List B} {words : A × List B → List (List Bool)}
    (hl : Procedure ea (listCode eb) rows) (p : Procedure (prodCode ea (listCode eb)) (listCode id) words)
    (x : A) {K C L : ℕ} (hnum : (words (x,rows x)).length = (rows x).length)
    (hout : ∀ w ∈ words (x,rows x), w.length ≤ L)
    (hcall : p.cost (x,rows x) ≤ K*((rows x).length+1)*(mapWork (ea := ea) (eb := eb) x (rows x) C L)) :
    (listJoinWords.comp (p.comp ((identity ea).pair hl))).meter x ≤
      (10^14*(K+1)*(listJoinWords.bound.eval 1+1))*
      (hl.meter x+((rows x).length+1)*(mapWork (ea := ea) (eb := eb) x (rows x) C L)) := by
  let env := (x,rows x)
  let N := (rows x).length
  let raw := (prodCode ea (listCode eb) env).length
  let S := tabSpan (prodCode ea (listCode eb)) N env L
  let V := mapWork (ea := ea) (eb := eb) x (rows x) C L
  let U := hl.meter x + (N+1)*V
  let J := listJoinWords.bound.eval 1+1
  let arg := (identity ea).pair hl
  let m := p.comp arg
  have hraw : raw+1 ≤ V := by
    have h : raw+1 ≤ (raw+1)^9 := Nat.le_self_pow (by decide) _
    change raw+1 ≤ C+(raw+1)^9+S^2+1
    omega
  have hsq : S^2 ≤ V := by change _ ≤ C+(raw+1)^9+S^2+1; omega
  have hnV : V ≤ (N+1)*V := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hu : (N+1)*V ≤ U := by dsimp [U]; omega
  have harg : (ea x).length+1 ≤ raw+1 := by
    simp only [raw,env,prodCode,pairBits_length]; omega
  have hK : 0 < K+1 := Nat.succ_pos K
  have hJ : 0 < J := Nat.succ_pos _
  have hkU : U ≤ (K+1)*J*U := Nat.le_mul_of_pos_left _ (Nat.mul_pos hK hJ)
  have hC : p.cost env ≤ (K+1)*J*U := by
    apply hcall.trans
    change K*(N+1)*V ≤ _
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul _ hu
    exact (Nat.le_succ K).trans (Nat.le_mul_of_pos_right _ hJ)
  have hlen := p.output_length_le_cost env
  have hp : p.meter env ≤ 4*((K+1)*J*U) := by
    change p.cost env+raw+(listCode id (words env)).length+1 ≤ _
    change _ ≤ raw+p.cost env at hlen
    omega
  have hs : (N+1)*(L+1)+1 ≤ S := by dsimp [S,tabSpan]; omega
  have hj := flatten_meter hnum hout hs
  change listJoinWords.meter (words env) ≤ 16*J*S^2 at hj
  have hjsq : J*S^2 ≤ (K+1)*J*U := by
    calc _ ≤ J*U := Nat.mul_le_mul_left _ (hsq.trans (hnV.trans hu))
         _ ≤ (K+1)*(J*U) := Nat.le_mul_of_pos_left _ hK
         _ = _ := (Nat.mul_assoc ..).symm
  have hid := meter_identity ea x
  have hi := meter_pair (identity ea) hl x
  have hm := meter_comp p arg x
  have hf := meter_comp listJoinWords m x
  change arg.meter x ≤ _ at hi
  change m.meter x ≤ 6*(arg.meter x+p.meter env) at hm
  change (listJoinWords.comp m).meter x ≤ 6*(m.meter x+listJoinWords.meter (words env)) at hf
  change (listJoinWords.comp m).meter x ≤ (10^14*(K+1)*J)*U
  have hhl : hl.meter x ≤ U := by dsimp [U]; omega
  rw [show (10^14*(K+1)*J)*U = 10^14*((K+1)*J*U) by ring]
  rw [Nat.mul_assoc] at hj
  omega

/-- True child bounds at the actual stored entries suffice for the nonindexed
record compiler. The list argument is evaluated once before mapping. -/
theorem meter_flatMapList (ea : A → List Bool) (eb : B → List Bool) (d : B) :
    ∃ P : ℕ, ∀ {rows : A → List B} {f : A → B → List Bool}
      (hl : Procedure ea (listCode eb) rows) (hf : Procedure (prodCode ea eb) id (fun z => f z.1 z.2))
      (x : A) {L C : ℕ},
      (∀ b ∈ rows x, (f x b).length ≤ L) → (∀ b ∈ rows x, hf.cost (x,b) ≤ C) →
      (flatMapList d hl hf).meter x ≤ P*(hl.meter x+((rows x).length+1)*
        (C+((prodCode ea (listCode eb) (x,rows x)).length+1)^9+
        (tabSpan (prodCode ea (listCode eb)) (rows x).length (x,rows x) L)^2+1)) := by
  obtain ⟨K,hK⟩ := cost_listMapWith ea eb (id : List Bool → List Bool) d []
  refine ⟨10^14*(K+1)*(listJoinWords.bound.eval 1+1),?_⟩
  intro rows f hl hf x L C hL hC
  let p := listMapWith d [] hf
  have h := hK hf (x,rows x) hL hC
  unfold flatMapList
  rw [meter_congrFun]
  apply map_then_join (K := K) (C := C) (L := L) hl p x (List.length_map ..) _ h
  intro w hw
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
  exact hL b hb

/-- The indexed compiler visits each stored record with its original ordinal.
Only the output length and clock at these specific child arguments are charged. -/
theorem meter_flatMapIdxList (ea : A → List Bool) (eb : B → List Bool) (d : B) :
    ∃ P : ℕ, ∀ {rows : A → List B} {f : A → ℕ → B → List Bool}
      (hl : Procedure ea (listCode eb) rows)
      (hf : Procedure (prodCode ea (prodCode Nat.bits eb)) id (fun z => f z.1 z.2.1 z.2.2))
      (x : A) {L C : ℕ},
      (∀ i : Fin (rows x).length, (f x i (rows x)[i]).length ≤ L) →
      (∀ i : Fin (rows x).length, hf.cost (x,i.val,(rows x)[i]) ≤ C) →
      (flatMapIdxList d hl hf).meter x ≤ P*(hl.meter x+((rows x).length+1)*
        (C+((prodCode ea (listCode eb) (x,rows x)).length+1)^9+
        (tabSpan (prodCode ea (listCode eb)) (rows x).length (x,rows x) L)^2+1)) := by
  obtain ⟨K,hK⟩ := cost_listMapIdxWith ea eb (id : List Bool → List Bool) d []
  refine ⟨10^14*(K+1)*(listJoinWords.bound.eval 1+1),?_⟩
  intro rows f hl hf x L C hL hC
  let p := listMapIdxWith d [] hf
  have h := hK hf (x,rows x) hL hC
  apply map_then_join (K := K) (C := C) (L := L) hl p x (List.length_mapIdx ..) _ h
  intro w hw
  have e := List.mem_iff_getElem.mp hw
  obtain ⟨i,hi,rfl⟩ := e
  have ht : i < (rows x).length := by simpa using hi
  rw [List.getElem_mapIdx]
  exact hL ⟨i,ht⟩

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
