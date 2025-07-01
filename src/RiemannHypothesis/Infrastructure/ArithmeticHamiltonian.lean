import RiemannHypothesis.Infrastructure.WeightedHilbertSpace

/-!
# Arithmetic Hamiltonian

This file re-exports the arithmetic Hamiltonian and operator A(s) from WeightedHilbertSpace.
-/

namespace RiemannHypothesis

-- Re-export the operator A(s) so it's available at the top level
export WeightedHilbertSpace (operatorA domainA operatorA_wellDefined)

end RiemannHypothesis
