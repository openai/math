import OAI.Computability.IntegerMultiplication.Foundation

/-! # Fixed-tape integer multiplication

Formalization of OpenAI's main theorem in *Integer multiplication below n log n*.
The complete finite-alphabet multitape construction is developed in the imported modules.
-/

namespace OAI
namespace Computability
namespace IntegerMultiplication

theorem sub_nlogn_integer_multiplication : IntegerMultiplication.Goal := IntegerMultiplication.multiplication

end IntegerMultiplication
end Computability
end OAI
