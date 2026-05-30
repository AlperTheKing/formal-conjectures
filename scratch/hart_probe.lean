import FormalConjectures.Paper.HartshorneConjecture

namespace HartshorneConjecture
open HartshorneConjecture
universe u
open CategoryTheory Limits MvPolynomial AlgebraicGeometry
variable (S : AlgebraicGeometry.Scheme.{u})
namespace AlgebraicGeometry.Scheme

example : HasFiniteCoproducts S.VectorBundles := by
  infer_instance

end AlgebraicGeometry.Scheme
end HartshorneConjecture
