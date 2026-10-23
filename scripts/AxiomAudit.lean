module

public import MultiplicativeBasisDeformations

/-! Axiom report for the main theorems and the principal statements.
Run with `lake env lean scripts/AxiomAudit.lean`, or `python3 scripts/audit_axioms.py`. -/

@[expose] public section

#print axioms MultiplicativeBasisDeformations.theoremA
#print axioms MultiplicativeBasisDeformations.theoremB
#print axioms MultiplicativeBasisDeformations.awayFromTwoBasis
#print axioms MultiplicativeBasisDeformations.standard_iff_rayLinearization
#print axioms MultiplicativeBasisDeformations.IndSkeleton.familyCriterion_WP
#print axioms MultiplicativeBasisDeformations.IndSkeleton.polynomialMeshComparison_WP
#print axioms MultiplicativeBasisDeformations.MeshWalk.familyCriterion_G
#print axioms MultiplicativeBasisDeformations.MeshWalk.polynomialMeshComparison_G
#print axioms MultiplicativeBasisDeformations.MeshWalk.coinvEquiv_line
#print axioms MultiplicativeBasisDeformations.RaySys.Sys.BL_proper_inS
#print axioms MultiplicativeBasisDeformations.RaySys.Sys.nondeep_return_types
#print axioms MultiplicativeBasisDeformations.Statement.theoremA
#print axioms MultiplicativeBasisDeformations.Statement.theoremB
#print axioms MultiplicativeBasisDeformations.Statement.translateCompatible
