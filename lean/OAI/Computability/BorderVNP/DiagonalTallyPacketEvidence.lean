import OAI.Computability.BorderVNP.DiagonalTallyPacketEmitRun

/-! # Interpreting the emitted references at an owned cube vertex -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyPacketEmit

open VPVNP.BurstRAM RoutingISA Cube Cube.Tally VPVNP.MotifBase DiagonalTallyGather
open DiagonalTallyMaterialize (digitRefsAt)

variable {n b h K s D w : ℕ}

/-- The selected packet term and the physical assignment at one owned vertex.
Only attached ends and incident edges are required by the native execution. -/
structure Visit (n b h K s : ℕ) where
  /-- Runtime address of this packet’s bit bank. -/
  base : ℕ
  /-- Selected cube summand supplied to all incident groups. -/
  selector : Selector n K h
  /-- Cube vertex owned by the current processor group. -/
  vertex : Vertex (n+1)
  /-- Demand-end words of the assigned packet. -/
  ends : Ends n → Fin (h*b) → Bool
  /-- One shared assignment for each directed supply edge. -/
  supply : (e : Edge (n+1)) → Fin (payload (onEdge s) selector.2 e) → Bool

/-- The row of the genuine cube table for this visit. -/
def Visit.entry (v : Visit n b h K s) (D : ℕ) : TableEntry n b h K s :=
  packetEntry D b s v.selector v.vertex v.ends v.supply

/-- The reference vector with its physical addresses and the bits reached in the source bank. -/
noncomputable def Visit.request (v : Visit n b h K s) (f : Frame) (m : ℕ → ℕ) (i : ℕ) :
    DiagonalTallyPacket.Request :=
  ⟨f.refs+i*f.width,(recipe v.selector v.vertex b s).map fun r =>
    let a := r.address v.base f.zeroAddr f.oneAddr
    (a,decide (m a = 1))⟩

/-- The three runtime words written by the physical packet ownership scan. -/
def Visit.tripleAt (v : Visit n b h K s) (m : ℕ → ℕ) (p : ℕ) : Prop :=
  m p=v.base ∧ m (p+1)=(selectorOrder n K h v.selector).val ∧
    m (p+2)=(vertexOrder (n+1) v.vertex).val

/-- A single fixed relative recipe table shared by all packet instances and input lengths. -/
def Frame.recipeAt (f : Frame) (m : ℕ → ℕ) (n b h K s : ℕ) : Prop :=
  f.width = argumentWidth n b h K s ∧ f.vertices = Fintype.card (Vertex (n+1)) ∧
    ∀ (u : Selector n K h) (v : Vertex (n+1)) (j : ℕ) (hj : j<(recipe u v b s).length),
      m (f.recipes+((selectorOrder n K h u).val*f.vertices+(vertexOrder _ v).val)*f.width+j) =
        ((recipe u v b s)[j]).code

private theorem resolve_code (f : Frame) (base : ℕ) (r : Reference) :
    f.resolve base r.code = r.address base f.zeroAddr f.oneAddr := by
  cases r with
  | literal b => cases b <;> rfl
  | packet k =>
    simp [Frame.resolve,Reference.code,Reference.address,show k+2≠1 by omega]

/-- The generated pointer is the relocation of the fixed recipe for this selector and vertex. -/
theorem Visit.generatedRef (v : Visit n b h K s) (f : Frame) (m : ℕ → ℕ) (i : ℕ)
    (hFrame : f.recipeAt m n b h K s) (ht : v.tripleAt m (f.triples+3*i)) {j : ℕ} (hj : j<f.width) :
    f.refValue m (i*f.width+j) = ((recipe v.selector v.vertex b s)[j]'(by rw [recipe_length,← hFrame.1]; exact hj)).address
      v.base f.zeroAddr f.oneAddr := by
  have hw : 0<f.width := Nat.zero_lt_of_lt hj
  have hd : (i*f.width+j)/f.width = i := by
    simp [Nat.mul_comm i f.width,Nat.mul_add_div hw,Nat.div_eq_of_lt hj]
  have hm : (i*f.width+j)%f.width = j := by simp [Nat.add_mod,Nat.mod_eq_of_lt hj]
  obtain ⟨hb,hs,hv⟩ := ht
  simp only [Frame.refValue,Frame.recipeAddr,hd,hm,hb,hs,hv]
  rw [hFrame.2.2 _ _ _ (by rw [recipe_length,← hFrame.1]; exact hj),resolve_code]

private theorem data_as_bits (xs : List ℕ) (ys : List Bool) (he : xs=ys.map Bool.toNat) :
    xs.map (fun a => decide (a=1)) = ys ∧ ∀ a ∈ xs, a=(decide (a=1)).toNat := by
  subst xs
  constructor
  · simp only [List.map_map]
    convert List.map_id ys
    funext b
    cases b <;> rfl
  · intro a ha
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha
    cases b <;> rfl

/-- Every generated request has exactly the physical selected-ID lookup index. -/
theorem Visit.request_index (v : Visit n b h K s) (f : Frame) (m : Memory w) (i : ℕ)
    (hb : VertexAt m v.base v.selector v.vertex v.ends v.supply)
    (hzero : (m f.zeroAddr).val=0) (hone : (m f.oneAddr).val=1) (D : ℕ) :
    (v.request f (readings m) i).index = lookupIndex (selectorOrder n K h) (vertexOrder _) (v.entry D) := by
  have he := recipe_reads_at (D := D) m v.base f.zeroAddr f.oneAddr v.selector v.vertex v.ends v.supply hb hzero hone
  have h := (data_as_bits _ _ he).1
  simp only [List.map_map,Function.comp_def] at h
  rw [DiagonalTallyPacket.Request.index,Visit.request]
  simp only [List.map_map,Function.comp_def,readings]
  exact (congrArg (readDigits 0) h).trans (lookupDigits_index _ _ _)

private theorem refsAt_of_index (m : Memory w) (p : ℕ) (xs : List (ℕ × Bool))
    (h : ∀ j, (hj : j<xs.length) → (m (p+j)).val=xs[j].1 ∧ (m xs[j].1).val=xs[j].2.toNat) :
    digitRefsAt m p xs := by
  induction xs generalizing p with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨a,b⟩ := x
    have head := h 0 (by simp)
    refine ⟨by simpa using head.1,by simpa using head.2,ih (p+1) ?_⟩
    intro j hj
    have hx := h j.succ (by simpa using hj)
    rw [List.getElem_cons_succ] at hx
    simpa only [Nat.add_assoc,Nat.add_comm 1 j] using hx

/-- The concrete descriptor and digit vector written by the finite emitter satisfy the
full input predicate of the native lookup loop, with actual local vertex bits. -/
theorem Visit.resident_after_emit (v : Visit n b h K s) (f : Frame) (m m' : Memory w) (i : ℕ)
    (hi : i<f.count) (hFrame : f.recipeAt (readings m) n b h K s)
    (ht : v.tripleAt (readings m) (f.triples+3*i))
    (hb : VertexAt m v.base v.selector v.vertex v.ends v.supply)
    (hz : (m f.zeroAddr).val=0) (ho : (m f.oneAddr).val=1)
    (hbelow : ∀ r ∈ recipe v.selector v.vertex b s, r.address v.base f.zeroAddr f.oneAddr<f.descriptors)
    (hSep : f.descriptors+2*f.count ≤ f.refs) (he : readings m'=f.image (readings m)) :
    (v.request f (readings m) i).resident m' (f.descriptors+2*i) := by
  have len : (v.request f (readings m) i).digits.length = f.width := by
    simp [Visit.request,recipe_length,← hFrame.1]
  have hstart : readings m' (f.descriptors+2*i) = f.refs+i*f.width := by
    rw [he,f.image_descriptor _ hSep (2*i) (by omega)]
    simp [Frame.descValue]
  have hstop : readings m' (f.descriptors+2*i+1) = f.refs+i*f.width+f.width := by
    rw [he, Nat.add_assoc,f.image_descriptor _ hSep (2*i+1) (by omega)]
    simp [Frame.descValue,Nat.mul_add_div (by decide : 0<2),Nat.add_mul,Nat.add_assoc]
  refine ⟨hstart,?_,refsAt_of_index m' _ _ ?_⟩
  · rw [len]; exact hstop
  intro j hj
  rw [len] at hj
  have hlen : j<(recipe v.selector v.vertex b s).length := by rw [recipe_length,← hFrame.1]; exact hj
  let r := (recipe v.selector v.vertex b s)[j]
  have rmem : r ∈ recipe v.selector v.vertex b s := List.getElem_mem hlen
  let addr := r.address v.base f.zeroAddr f.oneAddr
  have hidx : i*f.width+j < f.count*f.width := by
    have h := Nat.mul_le_mul_right f.width hi
    rw [Nat.succ_mul] at h; omega
  have first : readings m' (f.refs+i*f.width+j) = addr := by
    rw [he,Nat.add_assoc,f.image_ref _ _ hidx,v.generatedRef f _ i hFrame ht hj]
  have current : readings m' addr = readings m addr := by
    rw [he,f.image_before _ (by omega) _ (hbelow r rmem)]
  have eq := recipe_reads_at (D := 0) m v.base f.zeroAddr f.oneAddr v.selector v.vertex v.ends v.supply hb hz ho
  have hv := (data_as_bits _ _ eq).2 (readings m addr) (List.mem_map.mpr ⟨r,rmem,rfl⟩)
  simp only [Visit.request,List.getElem_map]
  exact ⟨first,current.trans hv⟩

end DiagonalTallyPacketEmit

end BorderVNP
end Computability
end OAI
