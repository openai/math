import OAI.Computability.BorderVNP.CellPacketReadScalar
import OAI.Computability.QuantumFactoring.BitStackListCode

/-! # Bounded counted-list traversal for the native packet decoder -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Native

open ExactQuantumFactoring.BitStackProgram

/-- A checked conversion of a binary length to unary loop tokens. Its clock is measured in
the number of declared members, each of which has a nonempty literal packet encoding. -/
structure CountRoutine (k : Fin 3) where
  /-- Program using the digit scratch stack and the designated list counter. -/
  program : Program Register
  /-- Absolute numerical clock multiplier. -/
  scale : ℕ
  /-- Conversion leaves every other counter and both public streams intact. -/
  runs (n : ℕ) (rest out : List Bool) (ct : Fin 3 → List Bool) (hc : ct k = []) :
    ∃ c ≤ scale*(n+1)^2, Runs program
      (Function.update (bank rest out ct) Register.digits n.bits.reverse)
      (bank rest out (Function.update ct k (List.replicate n true))) c

private theorem update_count (k : Fin 3) (s out : List Bool) (ct : Fin 3 → List Bool) (v : List Bool) :
    Function.update (bank s out ct) (Register.counter k) v = bank s out (Function.update ct k v) := by
  funext r
  cases r <;> simp [bank,Function.update]

private def visitsCost {α : Type} (src : α → List Bool) (C : ℕ) (xs : List α) :=
  (xs.map (fun a => C*((src a).length+1)^2+1)).sum

private theorem visitsCost_le {α : Type} (src : α → List Bool) (C : ℕ)
    (hp : ∀ a, 0 < (src a).length) (xs : List α) :
    visitsCost src C xs ≤ (4*C+1)*(xs.flatMap src).length^2 := by
  induction xs with
  | nil => simp [visitsCost]
  | cons a as ih =>
    have hl := hp a
    have hw : (src a).length+1 ≤ 2*(src a).length := by omega
    have he := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hw 2)
    have hu : 1 ≤ (src a).length^2 := Nat.one_le_pow _ _ hl
    simp only [visitsCost, List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append] at ih ⊢
    nlinarith only [ih,he,hu,Nat.zero_le (C*(src a).length*(as.flatMap src).length),
      Nat.zero_le ((src a).length*(as.flatMap src).length)]

private theorem many_runs {α : Type} {src dst : α → List Bool} {K : Finset (Fin 3)} (k : Fin 3)
    (hk : k ∉ K) (p : Reader src dst K) (xs : List α) (rest out : List Bool)
    (ct : Fin 3 → List Bool) (hc : ∀ j ∈ K, ct j = []) (h0 : ct k = []) :
    ∃ c ≤ visitsCost src p.scale xs+1, Runs (.loop (.counter k) p.program p.program)
      (bank (xs.flatMap src ++ rest) out (Function.update ct k (List.replicate xs.length true)))
      (bank rest ((xs.flatMap dst).reverse ++ out) ct) c := by
  induction xs generalizing out with
  | nil =>
    have he : Function.update ct k [] = ct := by rw [← h0, Function.update_eq_self]
    simp only [List.length_nil, List.replicate_zero, he, List.flatMap_nil, List.nil_append,
      List.reverse_nil, visitsCost, List.map_nil, List.sum_nil, Nat.zero_add]
    exact ⟨1,le_rfl,Runs.loop_nil h0⟩
  | cons a as ih =>
    let ctx := Function.update ct k (List.replicate as.length true)
    obtain ⟨u,hu,run⟩ := p.runs a (as.flatMap src ++ rest) out ctx (fun j hj => by
      have he : j ≠ k := fun h => hk (h ▸ hj)
      simpa only [ctx,Function.update_of_ne he] using hc j hj)
    obtain ⟨v,hv,again⟩ := ih ((dst a).reverse ++ out)
    let start := bank (src a ++ (as.flatMap src ++ rest)) out
      (Function.update ct k (List.replicate (a::as).length true))
    have hs : start (.counter k) = true :: List.replicate as.length true := by simp [start,bank,List.replicate_succ]
    have hup : Function.update start (.counter k) (List.replicate as.length true) =
        bank (src a ++ (as.flatMap src ++ rest)) out ctx := by
      simp only [start,update_count,Function.update_idem,ctx]
    have hloop := Runs.loop_true (p := p.program) hs (hup.symm ▸ run) again
    refine ⟨v+u+1,?_,?_⟩
    · simp only [visitsCost, List.map_cons,List.sum_cons] at hv ⊢
      omega
    · simpa only [start,List.flatMap_cons,List.reverse_append,List.append_assoc] using hloop

/-- Execute the count header, fill a designated counter and visit each serialized member.
The child program sees the remaining count on its caller-owned stack. -/
def readMany {α : Type} {src dst : α → List Bool} {K : Finset (Fin 3)}
    (k : Fin 3) (counter : CountRoutine k) (p : Reader src dst K)
    (hk : k ∉ K) (hp : ∀ a, 0 < (src a).length) :
    Reader (fun xs : List α => wire [xs.length] ++ xs.flatMap src) (fun xs => xs.flatMap dst) (insert k K) where
  program := .seq (readScalarCode .digits (fun b => [b]))
    (.seq counter.program (.loop (.counter k) p.program p.program))
  scale := 8+counter.scale+(4*p.scale+1)
  runs xs rest out ct h := by
    let tail := xs.flatMap src ++ rest
    let s := bank (wire [xs.length] ++ tail) out ct
    have h0 := h k (Finset.mem_insert_self ..)
    obtain ⟨u,hu,word⟩ := readScalarCode_runs s .digits (by decide) (by decide) (fun b => [b])
      xs.length.bits tail (by simp [s,bank]) rfl
    have he : Function.update (Function.update s .input tail) .digits
        ((xs.length.bits.flatMap fun b => [b]).reverse ++ s .digits) =
        Function.update (bank tail out ct) .digits xs.length.bits.reverse := by
      funext r; cases r <;> simp [s,bank,Function.update]
    rw [he] at word
    obtain ⟨v,hv,tokens⟩ := counter.runs xs.length tail out ct h0
    obtain ⟨w,hw,body⟩ := many_runs k hk p xs rest out ct (fun j hj => h j (Finset.mem_insert_of_mem hj)) h0
    refine ⟨w+v+u,?_,?_⟩
    · have hvst := visitsCost_le src p.scale hp xs
      have hlen := length_le_flat src xs hp
      have hwl : xs.length.bits.length+1 ≤ (wire [xs.length]).length := by simp [wire,CellMacro.Generator.records]; omega
      let n := (wire [xs.length] ++ xs.flatMap src).length
      have hB : xs.length.bits.length+1 ≤ (n+1)^2 := by
        have hl : xs.length.bits.length+1 ≤ n+1 := by dsimp only [n]; rw [List.length_append]; omega
        nlinarith only [hl, Nat.zero_le n, Nat.zero_le (n^2)]
      have hN : xs.length+1 ≤ n+1 := by dsimp only [n]; rw [List.length_append]; omega
      have hT : (xs.flatMap src).length ≤ n+1 := by dsimp only [n]; rw [List.length_append]; omega
      have hV := Nat.mul_le_mul_left counter.scale (Nat.pow_le_pow_left hN 2)
      have hW := Nat.mul_le_mul_left (4*p.scale+1) (Nat.pow_le_pow_left hT 2)
      have hn : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
      change _ ≤ (8+counter.scale+(4*p.scale+1))*(n+1)^2
      simp only [List.length_singleton, max_self] at hu
      rw [Nat.add_mul,Nat.add_mul]
      omega
    · simpa only [s,tail,List.append_assoc] using Runs.seq word (Runs.seq tokens body)

/-- A typed prefix reader can operate under any fixed number of CQF quote layers. -/
abbrev TypedReader {α : Type} (raw : α → List ℕ) (dst : α → List Bool) (clean : Finset (Fin 3)) :=
  (emit : Emit) → Reader (fun a => wire (raw a)) (fun a => (dst a).flatMap emit) clean

/-- Relabel a typed input with pointwise-equal physical field sequences and output bits. -/
def typedOn {α β : Type} {raw : α → List ℕ} {dst : α → List Bool} {K : Finset (Fin 3)}
    (p : TypedReader raw dst K) (f : β → α) {src' : β → List ℕ} {dst' : β → List Bool}
    (hs : ∀ b, raw (f b) = src' b) (hd : ∀ b, dst (f b) = dst' b) : TypedReader src' dst' K :=
  fun emit => ((p emit).on f).castCode (fun b => congrArg wire (hs b)) (fun b => congrArg (List.flatMap emit) (hd b))

/-- Pairing two actual typed readers implements precisely the upstream first-component framing. -/
def typedPair {α β : Type} {raw : α → List ℕ} {dst : α → List Bool}
    {raw' : β → List ℕ} {dst' : β → List Bool} {K L : Finset (Fin 3)}
    (p : TypedReader raw dst K) (q : TypedReader raw' dst' L) :
    TypedReader (fun x : α × β => raw x.1 ++ raw' x.2) (prodCode dst dst') (K ∪ L) := by
  intro emit
  let pp := (p (underQuote emit)).on (Prod.fst : α × β → α)
  let qq := (q emit).on (Prod.snd : α × β → β)
  let endQuote : Reader (fun _ : α × β => []) (fun _ => emit false) K := (Reader.literal _).reserve (Finset.empty_subset K)
  have hK : K ∪ K = K := Finset.union_self K
  let b := (pp.followed endQuote).followed qq
  exact (hK ▸ b).castCode (fun x => by simp)
    (fun x => by simp [prodCode,pairBits,flatMap_quote,List.append_assoc])

/-- A length-prefixed packet list becomes a CQF tagged list with a quoted frame for every
child payload and its own final false marker. -/
def typedList {α : Type} {raw : α → List ℕ} {dst : α → List Bool} {K : Finset (Fin 3)}
    (k : Fin 3) (counter : CountRoutine k) (p : TypedReader raw dst K)
    (hk : k ∉ K) (hp : ∀ a, 0 < (wire (raw a)).length) :
    TypedReader (fieldList raw) (listCode dst) (insert k K) := by
  intro emit
  let add (b : Bool) : Reader (fun _ : α => []) (fun _ => emit b) K :=
    (Reader.literal _).reserve (Finset.empty_subset K)
  have hK : K ∪ K ∪ K = K := by simp
  let child := (add true).followed (p (underQuote emit)) |>.followed (add false)
  let core := readMany k counter (hK ▸ child) hk (fun a => by simpa using hp a)
  let done_ : Reader (fun _ : List α => []) (fun _ => emit false) (insert k K) :=
    (Reader.literal _).reserve (Finset.empty_subset _)
  let total := core.followed done_
  have hKK : insert k K ∪ insert k K = insert k K := Finset.union_self _
  apply (hKK ▸ total).castCode
  · intro xs
    have hw (as : List α) : wire (as.flatMap raw) = as.flatMap (fun a => wire (raw a)) := by
      induction as with | nil => rfl | cons a as ih => simp [ih]
    simp [fieldList,hw]
  · intro xs
    induction xs with
    | nil => simp [listCode]
    | cons a xs ih => simp [listCode,pairBits,flatMap_quote,List.append_assoc] at ih ⊢; exact ih

end CellSparse.Packet.Native

end BorderVNP
end Computability
end OAI
