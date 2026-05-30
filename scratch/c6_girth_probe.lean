import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph
namespace WrittenOnTheWallII.Test

example : (cycleGraph_EulerianCircuit 3).IsCycle := by
  simp [cycleGraph_EulerianCircuit, Walk.isCycle_def]

example : C6.girth ≤ 6 := by
  have hw : (cycleGraph_EulerianCircuit 3).IsCycle := by
    simp [cycleGraph_EulerianCircuit, Walk.isCycle_def]
  simpa [C6, cycleGraph_EulerianCircuit_length] using
    (C6.girth_le_length (a := (0 : Fin 6)) (w := cycleGraph_EulerianCircuit 3) hw)

end WrittenOnTheWallII.Test
