module compgraph[node]

open graph[node]


-- предикат активного узла, то есть
-- в этот узел могут прийти данные из
-- истока
pred active[
   edges : node->node,
   source: node,
   n : node
] {
  -- n находится в множестве узлов,
  -- достижимых от истока или
  -- сам является истоком
  n in source.*edges
}


-- безопасность узла, то есть, при подаче туда данных
-- не произойдёт их потери
pred safe[
   edges : node->node,
   drain : node,
    n : node
] {
  -- если есть ещё листья кроме drain
  -- то не один путь из n
  -- не должен вести в эти узлы
  -- и n не должно быть одним из
  -- этих узлов
  no n.*edges & (leaves[edges] - drain)
  drain in n.*edges
}

-- предикат валидности вычислительного графа
pred valid [
    edges: node -> node,
    source : one node, -- свойство 1
    drain : one  node -- свойство 2
] {
  edges.connected -- граф связный
  edges.dag -- свойство 6 и 7 (направленный и ацикличный)
  source in edges.roots -- свойство 1, 4 и 9
  drain in edges.leaves -- свойство 2, 4 и 8
  all n : edges.roots - source |     -- св-ство 9
    not active[edges, source, n]  -- кроме source все остальные
                                                                     -- неактивные
  all n : edges.nodes | -- 10 свойство
    active[edges, source, n] => safe[edges, drain, n] -- все активные
    -- являются безопасными
}


-- предикат для операции добавления дуги в граф
pred connect[
  old_edges : node->node,
  new_edges : node->node,
  source : one node,
  drain : one node,
  from : one node, 
  to : one node
] {
  from->to not in old_edges -- дуги from->to ещё не было
  from not in to.*old_edges -- from не достижим из to
                                                             -- чтобы не получилось циклов
  to != source -- входящие дуги в источник не имеют смысла
  -- вот тут поправили
  active[old_edges, source, from] => safe[old_edges, drain, to]
  -- учитываем безопасность to только для активной from,
  -- и, так как to теперь может быть отдельной вершиной,
  -- как и from, то нужно добавить условие
  -- сохранения связанности графа
  new_edges.connected
  -- это стало очевидным, так как старая проверка
  -- стала давать контрпримеры :)
  new_edges = old_edges + from -> to
}


-- предикат убирания дуги из графа
pred disconnect[
  old_edges : node->node,
  new_edges : node->node,
  source : one node,
  drain : one node,
  from : one node,
  to : one node
] {
  from->to in old_edges
  -- если удаляем исходящее ребро из активной вершины,
  -- то она должна оставаться безопасной
  active[old_edges, source, from] => safe[new_edges, drain, from]
  -- заметьте, что теперь не нужно анализировать на
  -- то, что вершина вышла из графа:
  -- (from not in new_edges.nodes and
  --  from != source)
  new_edges.connected
  new_edges = old_edges - from->to
}
