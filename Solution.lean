module

public import MultiplicativeBasisDeformations.Independent.TheoremB

@[expose] public section

universe u

/-- **Theorem A.** Every finite-dimensional representation-finite algebra over an
algebraically closed field has a normed multiplicative basis. -/
theorem MultiplicativeBasisDeformations.Challenge.theoremA
    (k A : Type u) [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] : MultiplicativeBasisDeformations.Statement.TheoremA k A :=
  MultiplicativeBasisDeformations.Statement.theoremA k A

/-- **Theorem B.** Every basic finite-dimensional representation-finite algebra over
an algebraically closed field of characteristic different from two is standard. -/
theorem MultiplicativeBasisDeformations.Challenge.theoremB
    (k A : Type u) [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] : MultiplicativeBasisDeformations.Statement.TheoremB k A :=
  MultiplicativeBasisDeformations.Statement.theoremB k A
