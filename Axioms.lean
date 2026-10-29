module

/- Run with `lake env lean Axioms.lean` after `lake build`.
Every result below should depend only on `propext`, `Classical.choice` and `Quot.sound`. -/
import GaussianRiesz

#print axioms ObstacleDecomposition
#print axioms ObstacleDecompositionUnique
#print axioms SqrtDomainSobolev
#print axioms EndpointTheorem
#print axioms PVIdentification
#print axioms CoordinateEndpointBound
#print axioms SpectralNormalizationBound
#print axioms UnnormalizedMeasureInvariance
#print axioms ComplexEndpointTheorem
