import OAI.Computability.NearSquareRoot.CRTPositionPairs
import OAI.Computability.IntegerMultiplication.Code.Iter
import OAI.Computability.NearSquareRoot.CRTPositionBorrowRows

/-! # Computing the bit-position XOR descriptors from a permutation table

The input contains a width, the starts of the two chunks, and one unary image for
each address position. A row in the output is either the local index of its partner
in the source chunk or an empty entry.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication IntegerMultiplication.Code

abbrev ChunkQuery := Tally × Tally × Tally × List Tally

/-- Keep an in-range position and subtract the first index of the chunk. -/
private def localIndex (x : Tally × Tally × Tally) : Option Tally :=
  bif Iter.small (x.2.2,x.2.1) then none else
    bif Iter.small (x.2.2,x.2.1 ++ x.1) then some ((cutLists (x.2.1,x.2.2)).2) else none

private theorem localIndex_poly : Poly localIndex := by
  let X := Tally × Tally × Tally
  have lo : Poly (fun x : X => Iter.small (x.2.2,x.2.1)) :=
    (show Easy (fun x : X => (x.2.2,x.2.1)) by fun_prop).poly.compose Iter.small_easy.poly
  have hi : Poly (fun x : X => Iter.small (x.2.2,x.2.1 ++ x.1)) :=
    (show Easy (fun x : X => (x.2.2,x.2.1 ++ x.1)) by fun_prop).poly.compose Iter.small_easy.poly
  have off : Easy (fun x : X => (cutLists (x.2.1,x.2.2)).2) :=
    (easy_cut (g := fun x : X => (x.2.1,x.2.2)) (by fun_prop)).sndCompose
  exact Poly.choose lo (Code.Poly.const _) (Poly.choose hi (off.compose Easy.some).poly (Code.Poly.const _))

private theorem localIndex_tally (m lo y : ℕ) :
    localIndex (tally m,tally lo,tally y) =
      if lo ≤ y ∧ y < lo + m then some (tally (y-lo)) else none := by
  by_cases hl : y < lo
  · simp [localIndex, Iter.small, hl, Nat.not_le_of_gt hl]
  · have h : lo ≤ y := by omega
    by_cases hh : y < lo + m
    · simp [localIndex, Iter.small, hl, h, hh, cutLists]
      rw [← recover_tally ((tally y).drop lo)]
      simp
    · simp [localIndex, Iter.small, hl, h, hh]

private def partner (x : ChunkQuery × Tally) : Option Tally :=
  localIndex (x.1.1,x.1.2.1,Iter.pick ([] : Tally) (x.1.2.2.2,x.1.2.2.1 ++ x.2))

private theorem partner_poly : Poly partner := by
  have y : Easy (fun x : ChunkQuery × Tally =>
      Iter.pick ([] : Tally) (x.1.2.2.2,x.1.2.2.1 ++ x.2)) :=
    (show Easy (fun x : ChunkQuery × Tally => (x.1.2.2.2,x.1.2.2.1 ++ x.2)) by fun_prop).compose (Iter.facile _)
  exact ((show Easy (fun x : ChunkQuery × Tally => (x.1.1,(x.1.2.1,
    Iter.pick ([] : Tally) (x.1.2.2.2,x.1.2.2.1 ++ x.2)))) from
    Easy.pair (by fun_prop) (Easy.pair (by fun_prop) y)).poly).compose localIndex_poly

/-- The read ports of a directed XOR between two complete chunks. -/
def crossDescriptor (q : ChunkQuery) : List (Option Tally) :=
  polyPush partner (q, Iter.lineup q.1)

@[fun_prop] theorem crossDescriptor_poly : Poly crossDescriptor := by
  exact (Poly.pair Poly.identity ((Easy.fst (Y := Tally × Tally × List Tally)).poly.compose Iter.poly_line)).compose
    (Poly.push ([],[],[],[]) [] partner_poly)

/-- Encoding of a permutation by the unary images of successive positions. -/
def positionImages {k : ℕ} (v : Equiv.Perm (Fin k)) : List Tally :=
  List.ofFn (fun j : Fin k => tally (v j).val)

private theorem partner_value {k m s d : ℕ} (hd : d + m ≤ k) (v : Equiv.Perm (Fin k))
    (j : Fin m) :
    partner ((tally m,tally s,tally d,positionImages v),tally j.val) =
      let y := (v ⟨d+j.val, by omega⟩).val
      if s ≤ y ∧ y < s+m then some (tally (y-s)) else none := by
  have ht : tally d ++ tally j.val = tally (d+j.val) := by
    rw [← recover_tally (tally d ++ tally j.val)]
    simp
  unfold partner positionImages
  dsimp only
  rw [ht, Iter.entry (fun j : Fin k => tally (v j).val) ⟨d+j.val,by omega⟩]
  exact localIndex_tally ..

theorem crossDescriptor_value {k m s d : ℕ} (hd : d+m ≤ k) (v : Equiv.Perm (Fin k)) :
    crossDescriptor (tally m,tally s,tally d,positionImages v) =
      List.ofFn fun j : Fin m =>
        let y := (v ⟨d+j.val, by omega⟩).val
        if s ≤ y ∧ y < s+m then some (tally (y-s)) else none := by
  simp only [crossDescriptor,polyPush,Iter.lined,List.map_ofFn]
  exact congrArg List.ofFn (funext (partner_value hd v))

/-- Embed a local position in the given contiguous chunk. -/
def chunkAt {k s m : ℕ} (hs : s+m ≤ k) (j : Fin m) : Fin k := ⟨s+j.val,by omega⟩

private def localValue {k m s : ℕ} (hs : s+m ≤ k) (v : Equiv.Perm (Fin k)) (i : Fin m) : Fin m :=
  let y := v (chunkAt hs i)
  if h : s ≤ y.val ∧ y.val < s+m then ⟨y.val - s, by omega⟩ else i

private theorem localValue_inv {k m s : ℕ} (hs : s+m ≤ k) (v : Equiv.Perm (Fin k))
    (hv : Function.Involutive v) : Function.Involutive (localValue hs v) := by
  intro i
  let y := v (chunkAt hs i)
  by_cases h : s ≤ y.val ∧ y.val < s+m
  · have hin : s ≤ (chunkAt hs i).val ∧ (chunkAt hs i).val < s+m :=
      ⟨Nat.le_add_right .., Nat.add_lt_add_left i.isLt _⟩
    let j : Fin m := ⟨y.val-s,by omega⟩
    have ej : localValue hs v i = j := dite_eq_left h
    have ej' : chunkAt hs j = y := Fin.ext (show s+(y.val-s) = y.val by omega)
    rw [ej]
    simp only [localValue, ej', y, hv (chunkAt hs i), dite_eq_left hin]
    exact Fin.ext (show s+i.val-s = i.val by omega)
  · have e : localValue hs v i = i := dite_eq_right h
    rw [e,e]

/-- Restrict the involution to the transpositions entirely inside this chunk. -/
def withinChunk {k m s : ℕ} (v : Equiv.Perm (Fin k)) (hv : Function.Involutive v)
    (hs : s+m ≤ k) : Equiv.Perm (Fin m) :=
  ⟨localValue hs v,localValue hs v,localValue_inv hs v hv,localValue_inv hs v hv⟩

theorem withinChunk_involutive {k m s : ℕ} (v : Equiv.Perm (Fin k)) (hv : Function.Involutive v)
    (hs : s+m ≤ k) : Function.Involutive (withinChunk v hv hs) := localValue_inv hs v hv

abbrev BorrowQuery := Tally × Tally × List Tally
abbrev BorrowPorts := Option Tally × Option Tally × Option Tally

private def localDefault (x : (Tally × Tally × Tally) × Tally) : Tally :=
  bif Iter.small (x.1.2.2,x.1.2.1) then x.2 else
    bif Iter.small (x.1.2.2,x.1.2.1 ++ x.1.1) then (cutLists (x.1.2.1,x.1.2.2)).2 else x.2

private theorem localDefault_poly : Poly localDefault := by
  let X := (Tally × Tally × Tally) × Tally
  have lo : Poly (fun x : X => Iter.small (x.1.2.2,x.1.2.1)) :=
    (show Easy (fun x : X => (x.1.2.2,x.1.2.1)) by fun_prop).poly.compose Iter.small_easy.poly
  have hi : Poly (fun x : X => Iter.small (x.1.2.2,x.1.2.1 ++ x.1.1)) :=
    (show Easy (fun x : X => (x.1.2.2,x.1.2.1 ++ x.1.1)) by fun_prop).poly.compose Iter.small_easy.poly
  exact Poly.choose lo Easy.snd.poly (Poly.choose hi
    (easy_cut (g := fun x : X => (x.1.2.1,x.1.2.2)) (by fun_prop)).sndCompose.poly Easy.snd.poly)

private def ports (x : Tally × Tally) : BorrowPorts :=
  (bif Iter.small x then some x.1 else none,
    bif Iter.small x then some x.2 else none,
    bif Iter.small x.swap then some x.2 else none)

private theorem ports_poly : Poly ports := by
  have s : Poly (fun x : Tally × Tally => Iter.small x.swap) := Easy.exchange.poly.compose Iter.small_easy.poly
  have fst : Poly (fun x : Tally × Tally => some x.1) := (Easy.fst.compose Easy.some).poly
  have snd : Poly (fun x : Tally × Tally => some x.2) := (Easy.snd.compose Easy.some).poly
  exact (Poly.choose Iter.small_easy.poly fst (Code.Poly.const _)).pair
    ((Poly.choose Iter.small_easy.poly snd (Code.Poly.const _)).pair (Poly.choose s snd (Code.Poly.const _)))

private def borrowPartner (x : BorrowQuery × Tally) : BorrowPorts :=
  ports (x.2,localDefault ((x.1.1,x.1.2.1,Iter.pick ([] : Tally) (x.1.2.2,x.1.2.1 ++ x.2)),x.2))

private theorem borrowPartner_poly : Poly borrowPartner := by
  let X := BorrowQuery × Tally
  have y : Easy (fun x : X => Iter.pick ([] : Tally) (x.1.2.2,x.1.2.1 ++ x.2)) :=
    (show Easy (fun x : X => (x.1.2.2,x.1.2.1 ++ x.2)) by fun_prop).compose (Iter.facile _)
  have z := (((show Easy (fun x : X => x.1.1) by fun_prop).pair
    ((show Easy (fun x : X => x.1.2.1) by fun_prop).pair y)).pair Easy.snd).poly.compose localDefault_poly
  exact (Easy.snd.poly.pair z).compose ports_poly

/-- Three directional read ports per local index for a matching within one chunk.
The ports respectively select the initial borrowing swap and the two directions
of the middle exchange. The final swap uses the first port again. -/
def borrowedDescriptor (x : BorrowQuery) : List BorrowPorts :=
  polyPush borrowPartner (x, Iter.lineup x.1)

@[fun_prop] theorem borrowedDescriptor_poly : Poly borrowedDescriptor :=
  (Poly.pair Poly.identity ((Easy.fst (Y := Tally × List Tally)).poly.compose Iter.poly_line)).compose
    (Poly.push ([],[],[]) [] borrowPartner_poly)

private theorem localDefault_tally (m s y i : ℕ) :
    localDefault ((tally m,tally s,tally y),tally i) = tally (if s ≤ y ∧ y < s+m then y-s else i) := by
  by_cases hl : y < s
  · simp [localDefault, Iter.small, hl, Nat.not_le_of_gt hl]
  · have h : s ≤ y := by omega
    by_cases hh : y < s + m
    · simp [localDefault, Iter.small, hl, h, hh, cutLists]
      rw [← recover_tally ((tally y).drop s)]
      simp
    · simp [localDefault, Iter.small, hl, h, hh]

def unaryPort {m : ℕ} (i : Option (Fin m)) : Option Tally := i.map fun j => tally j.val

theorem borrowedDescriptor_value {k m s : ℕ} (hs : s+m ≤ k) (v : Equiv.Perm (Fin k))
    (hv : Function.Involutive v) :
    let q := withinChunk v hv hs
    borrowedDescriptor (tally m,tally s,positionImages v) = List.ofFn fun i : Fin m =>
      (unaryPort (borrowIdRead q i), unaryPort (borrowUpRead q i), unaryPort (borrowDownRead q i)) := by
  simp only [borrowedDescriptor,polyPush,Iter.lined,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  have ht : tally s ++ tally i.val = tally (chunkAt hs i).val := by
    rw [← recover_tally (tally s ++ tally i.val)]
    simp [chunkAt]
  change ports (tally i.val,localDefault ((tally m,tally s,Iter.pick ([] : Tally)
       (positionImages v,tally s ++ tally i.val)),tally i.val)) = _
  rw [ht,positionImages,Iter.entry,localDefault_tally]
  have val : ((withinChunk v hv hs) i).val =
      if s ≤ (v (chunkAt hs i)).val ∧ (v (chunkAt hs i)).val < s+m then
        (v (chunkAt hs i)).val-s else i.val := by
    change (localValue hs v i).val = _
    unfold localValue
    by_cases h : s ≤ (v (chunkAt hs i)).val ∧ (v (chunkAt hs i)).val < s+m
    · rw [dite_eq_left h, ite_eq_left h]
    · rw [dite_eq_right h, ite_eq_right h]
  rw [← val]
  by_cases up : i < withinChunk v hv hs i <;> by_cases down : withinChunk v hv hs i < i <;>
    simp [ports, Iter.small, borrowIdRead, borrowUpRead, borrowDownRead, unaryPort,
      up, down]

/-- Read a partner in the contiguous source chunk of a permutation of the true
address positions. Images in the tail or in any other chunk give an empty entry. -/
def chunkRead {k : ℕ} (v : Equiv.Perm (Fin k)) (s d : Fin 3) (i : Fin (k/3)) :
    Option (Fin (k/3)) :=
  let e := threeChunksWithTail k
  match e (v (e.symm (.inl (d,i)))) with
  | .inl (c,j) => if c = s then some j else none
  | .inr _ => none

theorem crossDescriptor_native {k : ℕ} (v : Equiv.Perm (Fin k)) (s d : Fin 3) :
    let m := k/3
    crossDescriptor (tally m,tally (m*s.val),tally (m*d.val),positionImages v) =
      List.ofFn fun i => unaryPort (chunkRead v s d i) := by
  let m := k/3
  let e := threeChunksWithTail k
  have hd : m*d.val+m ≤ k := by
    have h := Nat.mul_le_mul_left m (show d.val+1 ≤ 3 by omega)
    simp only [Nat.mul_succ] at h
    omega
  dsimp only
  rw [crossDescriptor_value hd v]
  apply congrArg List.ofFn
  funext i
  let x := e.symm (.inl (d,i))
  have hx : chunkAt hd i = x := by
    apply Fin.ext
    simp [chunkAt,x,e,m,Nat.add_comm]
  change (if m*s.val ≤ (v (chunkAt hd i)).val ∧ (v (chunkAt hd i)).val < m*s.val+m then
    some (tally ((v (chunkAt hd i)).val-m*s.val)) else none) = _
  rw [hx]
  unfold chunkRead
  change _ = unaryPort (match e (v x) with
    | .inl (c,j) => if c = s then some j else none
    | .inr _ => none)
  generalize hh : e (v x) = p
  have image : v x = e.symm p := (e.symm_apply_apply _).symm.trans (congrArg e.symm hh)
  rw [image]
  cases p with
  | inl cj =>
    obtain ⟨c,j⟩ := cj
    change (if m*s.val ≤ j.val + m*c.val ∧ j.val + m*c.val < m*s.val+m then
      some (tally (j.val + m*c.val - m*s.val)) else none) = unaryPort (if c=s then some j else none)
    have hj := j.isLt
    change j.val < m at hj
    rcases lt_trichotomy c s with h | h | h
    · have hc := Nat.mul_le_mul_left m (show c.val+1 ≤ s.val by exact h)
      rw [Nat.mul_succ] at hc
      rw [ite_eq_right (by omega), ite_eq_right h.ne]
      rfl
    · subst c
      rw [ite_eq_left (by omega), ite_eq_left rfl]
      simp [unaryPort]
    · have hc := Nat.mul_le_mul_left m (show s.val+1 ≤ c.val by exact h)
      rw [Nat.mul_succ] at hc
      rw [ite_eq_right (by omega), ite_eq_right h.ne']
      rfl
  | inr j =>
    have h := Nat.mul_le_mul_left m (show s.val+1 ≤ 3 by omega)
    rw [Nat.mul_succ] at h
    change (if m*s.val ≤ 3*m+j.val ∧ 3*m+j.val < m*s.val+m then _ else none) = none
    rw [ite_eq_right (by omega)]

private theorem chunkRead_some {k : ℕ} (v : Equiv.Perm (Fin k)) (s d : Fin 3)
    (i j : Fin (k/3)) :
    chunkRead v s d i = some j ↔
      v ((threeChunksWithTail k).symm (.inl (d,i))) = (threeChunksWithTail k).symm (.inl (s,j)) := by
  rw [Equiv.eq_symm_apply]
  unfold chunkRead
  dsimp only
  generalize (threeChunksWithTail k) (v ((threeChunksWithTail k).symm (.inl (d,i)))) = p
  cases p with
  | inr _ => simp
  | inl q =>
    rcases q with ⟨c,q⟩
    by_cases h : c=s <;> simp [h]

/-- Opposite tables of an involution are inverse partial matchings. -/
theorem chunkRead_inverse {k : ℕ} (v : Equiv.Perm (Fin k)) (hv : Function.Involutive v)
    (s d : Fin 3) (i j : Fin (k/3)) :
    chunkRead v s d i = some j ↔ chunkRead v d s j = some i := by
  rw [chunkRead_some, chunkRead_some]
  constructor <;> intro h <;> rw [← h,hv]

/-- In the existing tree codec, an absent port is the empty Boolean list and a
present unary port is a list with a leading true bit and a unary-length tail. -/
private def portWord : Option Tally → List Bool
  | none => []
  | some j => true :: j.map (fun _ => false)

private theorem portWord_easy : Easy portWord := by
  have enc (t : Tally) : send (t.map (fun _ => false)) = send t := by
    induction t with
    | nil => rfl
    | cons u t ih => simp only [List.map_cons,send_cons,ih]; rfl
  have same : (fun t : Option Tally => send (portWord t)) = send := by
    funext t
    cases t with
    | none => rfl
    | some t => simp only [portWord,send_cons,enc,send_some]; rfl
  change Task size send (fun t : Option Tally => send (portWord t))
  rw [same]
  exact Task.self

private def readPort (x : List Bool × Option Tally) : Bool :=
  Iter.pick false (false::x.1, ruler (portWord x.2))

private theorem readPort_poly : Poly readPort := by
  exact ((show Easy (fun x : List Bool × Option Tally => false :: x.1) by fun_prop).pair
    ((Easy.snd.compose portWord_easy).ruler)).poly.compose (Iter.facile false).poly

/-- Produce all XOR controls from the selected source row and its directed port table. -/
def readControls : List Bool × List (Option Tally) → List Bool := polyPush readPort

@[fun_prop] theorem readControls_poly : Poly readControls := Poly.push [] none readPort_poly

theorem readControls_value {m n : ℕ} (w : Fin m → Bool) (read : Fin n → Option (Fin m)) :
    readControls (List.ofFn w,List.ofFn (fun i => unaryPort (read i))) =
      List.ofFn fun i => (read i).elim false w := by
  simp only [readControls,polyPush,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change readPort (List.ofFn w,unaryPort (read i)) = (read i).elim false w
  cases h : read i with
  | none => rfl
  | some j =>
    change Iter.pick false (false::List.ofFn w,ruler (portWord (some (tally j.val)))) = w j
    have q : ruler (portWord (some (tally j.val))) = tally (j.val+1) := by
      rw [← recover_tally (ruler _)]
      simp [portWord]
    rw [q]
    exact Iter.entry w j false

/-- Compute the concrete control vector directly from the table and the source word. -/
def crossControls (x : List Bool × ChunkQuery) : List Bool :=
  readControls (x.1,crossDescriptor x.2)

@[fun_prop] theorem crossControls_poly : Poly crossControls :=
  (Easy.fst.poly.pair (Easy.snd.poly.compose crossDescriptor_poly)).compose readControls_poly

theorem crossControls_native {k : ℕ} (v : Equiv.Perm (Fin k)) (s d : Fin 3) (w : Fin (k/3) → Bool) :
    let m := k/3
    crossControls (List.ofFn w,tally m,tally (m*s.val),tally (m*d.val),positionImages v) =
      List.ofFn fun i => (chunkRead v s d i).elim false w := by
  dsimp only
  change readControls (List.ofFn w,_) = _
  rw [crossDescriptor_native, readControls_value]

/-- The three generated tables can be scanned independently to produce the
control bits of any requested borrow direction. -/
def borrowedControls (x : List Bool × BorrowQuery) : List Bool × List Bool × List Bool :=
  let t := borrowedDescriptor x.2
  (readControls (x.1,t.map Prod.fst),readControls (x.1,t.map (Prod.fst ∘ Prod.snd)),
    readControls (x.1,t.map (Prod.snd ∘ Prod.snd)))

@[fun_prop] theorem borrowedControls_poly : Poly borrowedControls := by
  have t := (Easy.snd (X := List Bool)).poly.compose borrowedDescriptor_poly
  have get (f : BorrowPorts → Option Tally) (hf : Easy f) :
      Poly (fun x : List Bool × BorrowQuery => readControls (x.1,(borrowedDescriptor x.2).map f)) :=
    (Easy.fst.poly.pair (t.compose hf.mapping.poly)).compose readControls_poly
  exact (get _ Easy.fst).pair ((get _ (Easy.snd.compose Easy.fst)).pair (get _ (Easy.snd.compose Easy.snd)))

theorem borrowedControls_value {k m s : ℕ} (hs : s+m ≤ k) (v : Equiv.Perm (Fin k))
    (hv : Function.Involutive v) (w : Fin m → Bool) :
    let q := withinChunk v hv hs
    let bits (f : Fin m → Option (Fin m)) := List.ofFn fun i => (f i).elim false w
    borrowedControls (List.ofFn w,tally m,tally s,positionImages v) =
      (bits (borrowIdRead q),bits (borrowUpRead q),bits (borrowDownRead q)) := by
  simp only [borrowedControls,borrowedDescriptor_value hs v hv,List.map_ofFn,Function.comp_def,readControls_value]

/-- Read one actual row of a full position word. -/
def chunkWord {k : ℕ} (w : Fin k → Bool) (d : Fin 3) (j : Fin (k/3)) : Bool :=
  w ((threeChunksWithTail k).symm (.inl (d,j)))

def chunkOf {k : ℕ} (p : Fin k) : Option (Fin 3) :=
  ((threeChunksWithTail k) p).elim (some ∘ Prod.fst) (fun _ => none)

private theorem copyChunk {k : ℕ} (v : Equiv.Perm (Fin k)) (w : Fin k → Bool)
    (s d : Fin 3) (i : Fin (k/3)) :
    let x := (threeChunksWithTail k).symm (.inl (d,i))
    copyFrom (chunkRead v s d) (chunkWord w s) (chunkWord w d) i =
      if chunkOf (v x) = some s then w (v x) else w x := by
  let e := threeChunksWithTail k
  let x := e.symm (.inl (d,i))
  have status : (chunkRead v s d i).isSome = decide (chunkOf (v x) = some s) := by
    unfold chunkRead chunkOf
    dsimp only
    change (match e (v x) with
      | .inl (c,j) => if c=s then some j else none
      | .inr _ => none).isSome = decide ((e (v x)).elim (some ∘ Prod.fst) (fun _ => none) = some s)
    generalize e (v x) = z
    cases z with
    | inr _ => rfl
    | inl z =>
      obtain ⟨c,j⟩ := z
      by_cases h : c=s <;> simp [h]
  cases h : chunkRead v s d i with
  | none =>
    have hc : chunkOf (v x) ≠ some s := by simpa [h] using status.symm
    change copyFrom (chunkRead v s d) _ _ i = if chunkOf (v x) = some s then _ else _
    simp [copyFrom,h,hc,chunkWord,x,e]
  | some j =>
    have hc : chunkOf (v x) = some s := by simpa [h] using status.symm
    have image := (chunkRead_some v s d i j).mp h
    change copyFrom (chunkRead v s d) _ _ i = if chunkOf (v x) = some s then _ else _
    rw [ite_eq_left hc]
    simp only [copyFrom,h,chunkWord]
    exact congrArg w image.symm

/-- Run the three directed cross-chunk XORs on the full position word. -/
def crossWord {k : ℕ} (v : Equiv.Perm (Fin k)) (s d : Fin 3) (w : Fin k → Bool)
    (x : Fin k) : Bool :=
  let rows := exchangeRows (chunkRead v d s) (chunkRead v s d) (chunkWord w s,chunkWord w d)
  match threeChunksWithTail k x with
  | .inr _ => w x
  | .inl (c,i) => if c=s then rows.1 i else if c=d then rows.2 i else w x

theorem crossWord_value {k : ℕ} (v : Equiv.Perm (Fin k)) (hv : Function.Involutive v)
    (s d : Fin 3) (ne : s ≠ d) (w : Fin k → Bool) (x : Fin k) :
    crossWord v s d w x =
      if (chunkOf x = some s ∧ chunkOf (v x) = some d) ∨
         (chunkOf x = some d ∧ chunkOf (v x) = some s) then w (v x) else w x := by
  let e := threeChunksWithTail k
  obtain ⟨p,rfl⟩ := e.symm.surjective x
  unfold crossWord
  rw [exchangeRows_eq _ _ (chunkRead_inverse v hv d s)]
  cases p with
  | inr j => simp [chunkOf,e]
  | inl p =>
    obtain ⟨c,i⟩ := p
    by_cases cs : c=s
    · subst c
      simp [chunkOf,e,ne,copyChunk]
      split <;> simp_all
    · by_cases cd : c=d
      · subst c
        simp [chunkOf,e,ne.symm,copyChunk]
        split <;> simp_all
      · simp [chunkOf,e,cs,cd]

theorem chunkFits (k : ℕ) (c : Fin 3) : k/3*c.val + k/3 ≤ k := by
  have h := Nat.mul_le_mul_left (k/3) (show c.val+1 ≤ 3 by omega)
  rw [Nat.mul_succ] at h
  omega

/-- The chunk-restricted involution read from a native table. -/
def nativeWithin {k : ℕ} (v : Equiv.Perm (Fin k)) (hv : Function.Involutive v) (c : Fin 3) :=
  withinChunk v hv (chunkFits k c)

theorem nativeWithin_read {k : ℕ} (v : Equiv.Perm (Fin k)) (hv : Function.Involutive v)
    (c : Fin 3) (i : Fin (k/3)) :
    nativeWithin v hv c i = (chunkRead v c c i).getD i := by
  let m := k/3
  let s := m*c.val
  let hs := chunkFits k c
  let y := (v (chunkAt hs i)).val
  have tables := (crossDescriptor_value (s := s) hs v).symm.trans (crossDescriptor_native v c c)
  have atPort := congrFun (List.ofFn_injective tables) i
  change (if s ≤ y ∧ y < s+m then some (tally (y-s)) else none) = unaryPort (chunkRead v c c i) at atPort
  apply Fin.ext
  change (localValue hs v i).val = _
  by_cases hy : s ≤ y ∧ y < s+m
  · rw [localValue,dite_eq_left hy]
    cases h : chunkRead v c c i with
    | none => simp [h,hy,unaryPort] at atPort
    | some j =>
      simp [h,hy,unaryPort] at atPort
      change y-s = j.val
      exact (tally_length _).symm.trans ((congrArg List.length atPort).trans (tally_length _))
  · rw [localValue,dite_eq_right hy]
    cases h : chunkRead v c c i with
    | none => rfl
    | some _ => simp [h,hy,unaryPort] at atPort

/-- Execute the nine XORs with the specified auxiliary chunk on the native word. -/
def borrowWord {k : ℕ} (v : Equiv.Perm (Fin k)) (hv : Function.Involutive v)
    (c d : Fin 3) (w : Fin k → Bool) (x : Fin k) : Bool :=
  let q := nativeWithin v hv c
  let aux := exchangeRows (borrowIdRead q) (borrowIdRead q)
  let middle := exchangeRows (borrowDownRead q) (borrowUpRead q)
  let rows := aux (middle (aux (chunkWord w c,chunkWord w d)))
  match threeChunksWithTail k x with
  | .inr _ => w x
  | .inl (a,i) => if a=c then rows.1 i else if a=d then rows.2 i else w x

theorem borrowWord_value {k : ℕ} (v : Equiv.Perm (Fin k)) (hv : Function.Involutive v)
    (c d : Fin 3) (w : Fin k → Bool) (x : Fin k) :
    borrowWord v hv c d w x =
      if chunkOf x = some c ∧ chunkOf (v x) = some c then w (v x) else w x := by
  let q := nativeWithin v hv c
  have hq : Function.Involutive q := withinChunk_involutive v hv (chunkFits k c)
  have select (i : Fin (k/3)) : chunkWord w c (q i) =
      copyFrom (chunkRead v c c) (chunkWord w c) (chunkWord w c) i := by
    rw [show q i = _ from nativeWithin_read v hv c i]
    cases h : chunkRead v c c i <;> simp [copyFrom,h]
  let e := threeChunksWithTail k
  obtain ⟨p,rfl⟩ := e.symm.surjective x
  unfold borrowWord
  dsimp only
  rw [borrowRows_correct _ hq]
  cases p with
  | inr i => simp [e,chunkOf]
  | inl p =>
    obtain ⟨a,i⟩ := p
    by_cases ac : a=c
    · subst a
      simp [e,chunkOf,Function.comp_def,select,copyChunk]
      split <;> simp_all
    · by_cases ad : a=d
      · subst d
        simp [e,chunkOf,chunkWord,ac]
      · simp [e,chunkOf,ac,ad]

end Controlled

end NearSquareRoot
end Computability
end OAI
