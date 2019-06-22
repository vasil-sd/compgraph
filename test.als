open compgraph[node] as cg

sig node {}

connect_is_safe:
check {
  -- для всех возможных наборов рёбер r1, r2
  all r1, r2 : node->node |
  -- для всех возможных узлов source, drain, from, to
  all source, drain, from, to : node  {
    -- r1 является валидным вычислительным графом с
    -- source/drain истоком/стоком
    -- и r2 является графом r1 с добавленным операцией
    -- connect ребром from->to
    (cg/valid[r1, source, drain] and
     cg/connect[r1, r2, source, drain, from, to])
    -- это влечёт то, что r2 + source/drain
    -- также является валидным вычислительным
    -- графом
    implies cg/valid[r2, source, drain]
    -- то есть операция connect сохраняет валидность
    -- вычислительного графа
  }
} for 8

-- Executing "Check connect_is_safe for 8"
--    Sig this/node scope <= 8
--    Sig this/node in [[node$0], [node$1], [node$2], [node$3], [node$4], [node$5], [node$6], [node$7]]
--    Generating facts...
--    Simplifying the bounds...
--    Solver=sat4j Bitwidth=4 MaxSeq=7 SkolemDepth=4 Symmetry=20
--    Generating CNF...
--    Generating the solution...
--    8513 vars. 168 primary vars. 24817 clauses. 333ms.
--    No counterexample found. Assertion may be valid. 17639ms.


disconnect_is_safe:
check {
  all r1, r2 : node->node |
  all source, drain, from, to : node  {
    (
       cg/valid[r1, source, drain] and -- r1 валидный
       disconnect[r1, r2, source, drain, from, to] -- r2 - это r1 без дуги from->to
     )
    implies cg/valid[r2, source, drain] -- r2 тоже валидный
  }
} for 8

-- Executing "Check disconnect_is_safe for 8"
--    Sig this/node scope <= 8
--    Sig this/node in [[node$0], [node$1], [node$2], [node$3], [node$4], [node$5], [node$6], [node$7]]
--    Generating facts...
--    Simplifying the bounds...
--    Solver=sat4j Bitwidth=4 MaxSeq=7 SkolemDepth=4 Symmetry=20
--    Generating CNF...
--    Generating the solution...
--    8485 vars. 168 primary vars. 24771 clauses. 120ms.
--    No counterexample found. Assertion may be valid. 17559ms.

connect_is_total:
check {
  all r1, r2 : node->node |
  all source,drain, from, to : node {
    (
      cg/valid[r1, source, drain] and -- оба графа валидные
      cg/valid[r2, source, drain] and
      r2 = r1 + from->to and r2 != r1 -- и различаются на дугу from->to
    )
    =>
    some n1, n2: node | connect[r1, r2, source, drain, n1, n2]
  }
} for 8

-- Executing "Check connect_is_total for 8"
--    Sig this/node scope <= 8
--    Sig this/node in [[node$0], [node$1], [node$2], [node$3], [node$4], [node$5], [node$6], [node$7]]
--    Generating facts...
--    Simplifying the bounds...
--    Solver=sat4j Bitwidth=4 MaxSeq=7 SkolemDepth=4 Symmetry=20
--    Generating CNF...
--    Generating the solution...
--    9161 vars. 168 primary vars. 25962 clauses. 259ms.
--    No counterexample found. Assertion may be valid. 1441ms.

disconnect_is_total:
check {
  all r1, r2 : node->node |
  all source,drain, from, to : node {
    (
      cg/valid[r1, source, drain] and -- оба графа валидные
      cg/valid[r2, source, drain] and
      r1 = r2 + from->to and r2 != r1 -- и различаются на дугу from->to
    )
    =>
    some n1, n2: node | disconnect[r1, r2, source, drain, n1, n2]
  }
} for 8

-- Executing "Check disconnect_is_total for 8"
--    Sig this/node scope <= 8
--    Sig this/node in [[node$0], [node$1], [node$2], [node$3], [node$4], [node$5], [node$6], [node$7]]
--    Generating facts...
--    Simplifying the bounds...
--    Solver=sat4j Bitwidth=4 MaxSeq=7 SkolemDepth=4 Symmetry=20
--    Generating CNF...
--    Generating the solution...
--    8906 vars. 168 primary vars. 25524 clauses. 153ms.
--    No counterexample found. Assertion may be valid. 478ms.
