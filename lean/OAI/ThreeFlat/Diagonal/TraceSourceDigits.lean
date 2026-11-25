import OAI.ThreeFlat.Diagonal.TraceSharedOrdinal
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Ring

namespace OAI
/-! # Mixed-radix addresses of hidden slots in each physical trace row -/

namespace ThreeFlat.Diagonal.TraceSourceOwner

variable {α : Type*}

/-- The dimensions that occur in the absolute-address directory. -/
structure Shape where
  rows : ℕ
  header : ℕ
  ticks : ℕ
  layers : ℕ
  cpu : ℕ
  edge : ℕ
  copy : ℕ
  gates : ℕ

def Shape.track (s : Shape) := 2*s.edge
def Shape.stride (s : Shape) := 2*s.cpu + (s.layers*s.track + (s.edge+(s.copy+s.gates)))
def Shape.count (s : Shape) :=
  s.ticks*s.cpu+(s.layers*(s.rows*s.track)+((s.rows-1)*s.edge+(s.rows*s.copy+s.rows*s.gates)))

def shape (w p r k S f d n : ℕ) : Shape :=
  ⟨2^d,S,f,Computability.VPVNP.RAMLayout.layerCount d,(5+r)*(w+1),7*(w+1),(1+6*p+k)*w,n⟩

theorem stride_bound (w p r k S f d n : ℕ) :
    (shape w p r k S f d n).stride ≤ 2*((5+r)*(w+1))+
      ((d+1)^2*(2*(7*(w+1)))+(7*(w+1)+((1+6*p+k)*w+n))) := by
  unfold Shape.stride Shape.track shape
  exact Nat.add_le_add_left (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (Nat.choose_le_pow (d+1) 2)) _) _

def appendAt (n : ℕ) (a b : ℕ → α) (j : ℕ) := if j<n then a j else b (j-n)

@[simp] theorem appendAt_left (a b : ℕ → α) {n j : ℕ} (h : j<n) : appendAt n a b j = a j := by
  simp [appendAt,h]

@[simp] theorem appendAt_right (a b : ℕ → α) (n j : ℕ) : appendAt n a b (n+j) = b j := by
  simp [appendAt]

/-- The pair consists of the physical owner and the offset in its rectangular
hidden-variable reservation. Regions occur in CPU, sort-layer, boundary,
broadcast-program, and row-local gate order in both address spaces. -/
def locate (s : Shape) : ℕ → ℕ × ℕ :=
  appendAt (s.ticks*s.cpu) (fun j => ((s.header+j/s.cpu)/2, ((s.header+j/s.cpu)%2)*s.cpu+j%s.cpu))
    (appendAt (s.layers*(s.rows*s.track))
      (fun j => ((j/s.track)%s.rows, 2*s.cpu+(j/(s.rows*s.track))*s.track+j%s.track))
      (appendAt ((s.rows-1)*s.edge)
        (fun j => (j/s.edge, 2*s.cpu+(s.layers*s.track+j%s.edge)))
        (appendAt (s.rows*s.copy) (fun j => (j/s.copy, 2*s.cpu+(s.layers*s.track+(s.edge+j%s.copy))))
          (fun j => (j/s.gates,2*s.cpu+(s.layers*s.track+(s.edge+(s.copy+j%s.gates))))))))

theorem pack_lt {x i n q : ℕ} (hx : x<n) (hi : i<q) : i*n+x < q*n := by
  calc
    i*n+x < i*n+n := Nat.add_lt_add_left hx _
    _ = (i+1)*n := by rw [Nat.add_mul,Nat.one_mul]
    _ ≤ q*n := Nat.mul_le_mul_right _ hi

theorem pack_div {i x n : ℕ} (hx : x<n) : (i*n+x)/n = i := by
  rw [Nat.mul_comm i n,Nat.mul_add_div (by omega : 0<n),Nat.div_eq_of_lt hx,Nat.add_zero]

theorem pack_mod {i x n : ℕ} (hx : x<n) : (i*n+x)%n = x := by
  simp [Nat.mod_eq_of_lt hx]

theorem locate_cpu (s : Shape) {t j : ℕ} (ht : t<s.ticks) (hj : j<s.cpu) :
    locate s (t*s.cpu+j) = ((s.header+t)/2,((s.header+t)%2)*s.cpu+j) := by
  simp [locate,appendAt_left _ _ (pack_lt hj ht),pack_div hj,pack_mod hj]

theorem locate_sort (s : Shape) {l v j : ℕ} (hl : l<s.layers) (hv : v<s.rows) (hj : j<s.track) :
    locate s (s.ticks*s.cpu+(l*(s.rows*s.track)+(v*s.track+j))) =
      (v,2*s.cpu+(l*s.track+j)) := by
  have inner := pack_lt hj hv
  have outer := pack_lt inner hl
  simp only [locate,appendAt_right,appendAt_left _ _ outer,pack_div inner]
  rw [show l*(s.rows*s.track)+(v*s.track+j) = (l*s.rows+v)*s.track+j by ring,
    pack_div hj,pack_mod hv,pack_mod hj]
  congr 1; omega

theorem locate_edge (s : Shape) {v j : ℕ} (hv : v<s.rows-1) (hj : j<s.edge) :
    locate s (s.ticks*s.cpu+(s.layers*(s.rows*s.track)+(v*s.edge+j))) =
      (v,2*s.cpu+(s.layers*s.track+j)) := by
  simp only [locate,appendAt_right,appendAt_left _ _ (pack_lt hj hv),pack_div hj,pack_mod hj]

theorem locate_copy (s : Shape) {v j : ℕ} (hv : v<s.rows) (hj : j<s.copy) :
    locate s (s.ticks*s.cpu+(s.layers*(s.rows*s.track)+((s.rows-1)*s.edge+(v*s.copy+j)))) =
      (v,2*s.cpu+(s.layers*s.track+(s.edge+j))) := by
  simp only [locate,appendAt_right,appendAt_left _ _ (pack_lt hj hv),pack_div hj,pack_mod hj]

theorem locate_gate (s : Shape) {v j : ℕ} (hj : j<s.gates) :
    locate s (s.ticks*s.cpu+(s.layers*(s.rows*s.track)+((s.rows-1)*s.edge+(s.rows*s.copy+(v*s.gates+j))))) =
      (v,2*s.cpu+(s.layers*s.track+(s.edge+(s.copy+j)))) := by
  simp only [locate,appendAt_right,pack_div hj,pack_mod hj]

/-- Absolute source IDs zero and one name literals. Header pins have two
header words per row. Every other bit uses its mixed-radix hidden ordinal. -/
def ownerAt (s : Shape) (word receiver address : ℕ) : ℕ :=
  appendAt 2 (fun _ => receiver) (appendAt (s.header*word) (fun j => (j/word)/2)
    (fun h => (locate s h).1)) address

def ownerNat (w p r k S f d n receiver address : ℕ) : ℕ :=
  appendAt 2 (fun _ => receiver) (appendAt (S*w) (fun j => (j/w)/2)
    (fun h => (locate (shape w p r k S f d n) h).1)) address

end ThreeFlat.Diagonal.TraceSourceOwner

end OAI
